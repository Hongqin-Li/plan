//! Efficient cache layer based on LRU and hash map.

use alloc::boxed::Box;
use core::{
    cell::UnsafeCell,
    fmt::{self, Debug},
    future::Future,
    hash::Hash,
    mem,
    ops::{Deref, DerefMut},
};

use kalloc::wrapper::map_insert;
use kalloc::wrapper::HashMap;
use kcore::error::Result;
use ksched::sync::{Mutex, Spinlock};

use intrusive_collections::intrusive_adapter;
use intrusive_collections::{LinkedList, LinkedListLink};

/// Status of a cache entry.
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum CState {
    /// Initial value.
    Empty,
    /// Not yet read from disk.
    Invalid,
    /// As latest as the value in disk.
    Valid,
    /// Modified in cache but not yet flushed to disk.
    Dirty,
}

/// Inner data of a cache node.
struct CNodeInner<K, V> {
    /// Guarded by [`CacheData`].
    pub nref: usize,
    /// Guarded by [`CacheData`]. Immutable since get.
    pub key: K,

    /// Lock guard.
    pub lock: Mutex<()>,
    /// Guarded by [`CNodeInner::lock`].
    pub state: CState,
    /// Guarded by [`CNodeInner::lock`].
    pub val: V,
    /// Times being locked since referenced. Reset when there are no reference.
    /// This is useful for kind of STM, i.e. ensuring no one has mutated the entry
    /// since we have unlocked it.
    ///
    /// Guarded by [`CNodeInner::lock`].
    pub nlocks: usize,
}

impl<K: Debug, V: Debug> Debug for CNodeInner<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CNodeInner")
            .field("nref", &self.nref)
            .field("lock", &self.lock)
            .field("state", &self.state)
            .field("key", &self.key)
            .field("val", &self.val)
            .finish()
    }
}

/// Pointer the a cache entry node.
pub struct CNodePtr<K, V>(*const CNode<K, V>);
impl<K, V> CNodePtr<K, V> {
    /// Retrieve node by address pointing to that node.
    pub unsafe fn from_addr(ptr: usize) -> Self {
        Self(ptr as *const CNode<K, V>)
    }
    /// Convert node pointer to address.
    pub fn to_addr(self) -> usize {
        self.0 as usize
    }
}

impl<K, V> Copy for CNodePtr<K, V> {}
impl<K, V> Clone for CNodePtr<K, V> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}

impl<K, V> Deref for CNodePtr<K, V> {
    type Target = CNode<K, V>;
    fn deref(&self) -> &Self::Target {
        unsafe { self.0.as_ref().unwrap() }
    }
}

impl<K, V> Debug for CNodePtr<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("CNodePtr").field(&self.0).finish()
    }
}

/// Cache entry node.
pub struct CNode<K, V> {
    link: LinkedListLink,
    /// Unsafe inner data.
    inner: UnsafeCell<CNodeInner<K, V>>,
}

impl<K: Debug, V: Debug> Debug for CNode<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CNode")
            .field("link", &self.link)
            .field("inner", &self.inner)
            .finish()
    }
}

intrusive_adapter!(CNodeAdapter<K, V> = Box<CNode<K, V>>: CNode<K, V> { link: LinkedListLink });

/// Inner data structure of the cache.
pub struct CacheData<K, V> {
    map: HashMap<K, CNodePtr<K, V>>,
    lru: LinkedList<CNodeAdapter<K, V>>,
}

impl<K: Debug, V: Debug> Debug for CacheData<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CacheData")
            .field("map", &self.map)
            .field("lru", &self.lru)
            .finish()
    }
}

/// Cache trait.
pub trait Cache
where
    Self: Sized,
{
    /// Key type.
    type Key: Hash + Eq + Default + Copy + fmt::Debug;
    /// Value type.
    type Value: fmt::Debug;

    /// Function used to retrieve the cache.
    fn cache_self<'a>(&'a self) -> &'a Spinlock<CacheData<Self::Key, Self::Value>>;

    /// Create a new cache with at most n in-memory cache entries.
    ///
    /// `default_val` is used to generate the initial value.
    /// It should return a [`Result`] since oom may occur during generation, e.g. `Box<[u8; 512]>`.
    ///
    /// Donot override this implementation.
    fn new_cache(
        n: usize,
        default_val: impl Fn() -> Result<Self::Value>,
    ) -> Result<Spinlock<CacheData<Self::Key, Self::Value>>> {
        let mut lru = LinkedList::new(CNodeAdapter::new());
        for _ in 0..n {
            lru.push_back(Box::try_new(CNode {
                link: LinkedListLink::new(),
                inner: UnsafeCell::new(CNodeInner {
                    nref: 0,
                    key: Self::Key::default(),
                    val: default_val()?,
                    lock: Mutex::new(()),
                    state: CState::Empty,
                    nlocks: 0,
                }),
            })?);
        }
        Ok(Spinlock::new(CacheData {
            map: HashMap::new(),
            lru,
        }))
    }

    /// Future returned by [`Self::disk_read`].
    type ReadFut<'a>: Future<Output = Result<()>> + 'a
    where
        Self::Key: 'a,
        Self::Value: 'a;
    /// Async function to fetch data from disk, should be implemented by yourself.
    fn disk_read<'a>(&'a self, key: &'a Self::Key, val: &'a mut Self::Value) -> Self::ReadFut<'a>;

    /// Future returned by [`Self::disk_write`].
    type WriteFut<'a>: Future<Output = Result<()>> + 'a
    where
        Self::Key: 'a,
        Self::Value: 'a;

    /// Async function to flush data to disk, should be implemented by yourself.
    fn disk_write<'a>(&'a self, key: &'a Self::Key, val: &'a Self::Value) -> Self::WriteFut<'a>;

    /// Future returned by [`Self::cache_get`].
    type GetFut<'a>: Future<Output = Result<Option<CEntry<'a, Self>>>> + 'a
    where
        Self: 'a,
        Self::Key: 'a,
        Self::Value: 'a;

    /// Get a cache item by key. Won't lock it.
    /// If key has already been in memory, this operation always succeed.
    /// If cannot reserve cache entry, returns [None].
    /// Donot implement it. Instead, injected to the trait implementation by [`super::cache_impl`].
    fn cache_get<'a>(&'a self, key: Self::Key, flush: bool) -> Self::GetFut<'a>;

    /// Mark all dirty entry as invalid without synchronizing with disk. May cause inconsistency!
    /// Donot implement it. Instead, injected to the trait implementation by [`super::cache_impl`].
    fn cache_invalidate<'a>(&'a self);
}

/// Macro to automatically inject implementations.
#[macro_export]
macro_rules! cache_impl {
    ($key:ty, $val:ty, $field:ident) => {
        type Key = $key;
        type Value = $val;

        fn cache_self<'a>(&'a self) -> &'a Spinlock<CacheData<Self::Key, Self::Value>> {
            &self.$field
        }

        type ReadFut<'a>
        where
            Self::Key: 'a,
            Self::Value: 'a,
        = impl core::future::Future<Output = kcore::error::Result<()>> + 'a;

        type WriteFut<'a>
        where
            Self::Key: 'a,
            Self::Value: 'a,
        = impl core::future::Future<Output = kcore::error::Result<()>> + 'a;

        type GetFut<'a>
        where
            Self: 'a,
            Self::Key: 'a,
            Self::Value: 'a,
        = impl core::future::Future<
            Output = kcore::error::Result<Option<$crate::cache::CEntry<'a, Self>>>,
        >;

        fn cache_get<'a>(&'a self, key: Self::Key, flush: bool) -> Self::GetFut<'a>
        where
            Self::Key: core::hash::Hash + Eq + Copy,
        {
            $crate::cache::cache_get(self, key, flush)
        }

        fn cache_invalidate<'a>(&'a self) {
            $crate::cache::cache_invalidate(self);
        }
    };
}

/// Return (locked, ptr).
///
/// `flush` indicates if it's allowed to flush any dirty cache entries.
/// NOTE: should be fn since [`LinkedList::CursorMut`] is not [Send].
fn cache_get1<T: Cache>(
    sel: &T,
    key: T::Key,
    flush: bool,
) -> Result<Option<(bool, CNodePtr<T::Key, T::Value>)>> {
    let mut g = sel.cache_self().lock();
    if let Some(ptr) = g.map.get(&key) {
        let ptr = ptr.clone();
        let u = unsafe { ptr.deref().inner.get().as_mut().unwrap() };
        u.nref += 1;
        debug_assert_ne!(u.state, CState::Empty);

        // #[cfg(test)]
        // println!("cache_get: key {:?}, nref: {}", u.key, u.nref);

        drop(g);
        return Ok(Some((false, ptr)));
    }

    let CacheData {
        ref mut map,
        ref mut lru,
    } = g.deref_mut();

    let mut cur = lru.front_mut();
    while let Some(u) = cur.get() {
        let inner = unsafe { u.inner.get().as_mut().unwrap() };
        if inner.nref == 0 {
            let ptr = CNodePtr(u as *const CNode<T::Key, T::Value>);

            if inner.state == CState::Dirty {
                if flush {
                    inner.nref += 1;

                    // Always succeed since ref is 0.
                    let gg = inner.lock.try_lock().unwrap();
                    mem::forget(gg);
                    drop(g);
                    return Ok(Some((true, ptr)));
                }
            } else {
                map_insert(map, key, ptr.clone())?;
                if inner.state != CState::Empty {
                    debug_assert_eq!(map.get(&inner.key).unwrap().0, ptr.0);
                    map.remove(&inner.key);
                }

                inner.nref += 1;
                inner.key = key;

                // SAFETY: Guarded by implicit lock.
                // Since anyone who want to access inner.state after this point
                // should first acquire g, which must be after `drop(g)`. Thus,
                // no need for memory fence here.
                inner.state = CState::Invalid;
                inner.nlocks = 0;
                drop(g);
                return Ok(Some((false, ptr)));
            }
        }
        cur.move_next();
    }
    Ok(None)
}

/// Get a cache entry by key.
pub async fn cache_get<'a, T: Cache>(
    sel: &'a T,
    key: T::Key,
    flush: bool,
) -> Result<Option<CEntry<'a, T>>> {
    loop {
        if let Some((dirty, ptr)) = cache_get1(sel, key, flush)? {
            if !dirty {
                break Ok(Some(CEntry { cache: sel, ptr }));
            } else {
                let inner = unsafe { (*ptr).inner.get().as_mut().unwrap() };
                let result = sel.disk_write(&inner.key, &inner.val).await;
                if result.is_ok() {
                    inner.state = CState::Valid;
                }
                inner.lock.release();
                // Don't move to back of LRU since it's likely to be replaced soon.
                let g = sel.cache_self().lock();
                inner.nref -= 1;
                drop(g);
                result?;
            }
        } else {
            break Ok(None);
        }
    }
}

/// See `Cache`.
pub fn cache_invalidate<T: Cache>(sel: &T) {
    let mut g = sel.cache_self().lock();
    let mut cur = g.lru.front_mut();
    while let Some(u) = cur.get() {
        let inner = unsafe { u.inner.get().as_mut().unwrap() };
        if inner.nref == 0 && inner.state == CState::Dirty {
            inner.state = CState::Invalid;
        }
        cur.move_next();
    }
}

/// Return number of referenced nodes and dirty nodes.
pub fn cache_stat<T: Cache>(sel: &T) -> (usize, usize) {
    let (mut refed, mut dirty) = (0, 0);
    let mut g = sel.cache_self().lock();
    let mut cur = g.lru.front_mut();
    while let Some(u) = cur.get() {
        let inner = unsafe { u.inner.get().as_mut().unwrap() };
        if inner.nref != 0 {
            refed += 1;
            #[cfg(test)]
            println!("cache_stat: referred {:?}, nref {}", inner.key, inner.nref);
        }
        if inner.state == CState::Dirty {
            dirty += 1;
        }
        cur.move_next();
    }
    drop(g);
    (refed, dirty)
}

/// Representing a client of a cache entry.
///
/// There may be several [`CEntry`] that refer to the same cache entry (i.e. same key) at a time.
/// Therefore, [`Cache`] maintains reference counter for each in-memory cache entry. If the
/// reference couter is not zero, it cannot be replace by another cache entyr. Once the the counter
/// decreases to zero, it will be moved to the back of LRU and can be flushed to disk when replaced
/// by another cache entry.
pub struct CEntry<'a, T>
where
    T: Cache,
{
    cache: &'a T,
    ptr: CNodePtr<T::Key, T::Value>,
}

impl<'a, T> Drop for CEntry<'a, T>
where
    T: Cache,
{
    fn drop(&mut self) {
        let inner = unsafe { (*self.ptr.0).inner.get().as_mut().unwrap() };
        let mut g = self.cache.cache_self().lock();
        debug_assert_ne!(inner.nref, 0);
        debug_assert_ne!(inner.state, CState::Empty);
        // SAFETY: nref is guarded by cache.inner.
        inner.nref -= 1;

        // #[cfg(test)]
        // println!("cache_drop: key {:?}, nref: {}", inner.key, inner.nref);

        if inner.nref == 0 {
            let mut cur = unsafe { LinkedList::cursor_mut_from_ptr(&mut g.lru, self.ptr.0) };
            let x = cur.remove().unwrap();
            g.lru.push_back(x);
        }
        drop(g);
    }
}

impl<'a, T> CEntry<'a, T>
where
    T: Cache,
{
    /// Lock and read the cache entry.
    pub async fn lock(&'a self) -> Result<CGuard<'a, T>> {
        let inner = unsafe { (*self.ptr.0).inner.get().as_mut().unwrap() };

        inner.lock.acquire().await;
        debug_assert_ne!(inner.nref, 0);
        debug_assert_ne!(inner.state, CState::Empty);
        inner.nlocks += 1;

        if inner.state == CState::Invalid {
            // Read from disk.
            let result = self.cache.disk_read(&inner.key, &mut inner.val).await;
            if let Err(e) = result {
                inner.lock.release();
                return Err(e);
            }
            inner.state = CState::Valid;
        }
        Ok(CGuard(self))
    }

    /// Get pointer to this cache entry.
    pub fn leak(self) -> CNodePtr<T::Key, T::Value> {
        let p = self.ptr;
        mem::forget(self);
        p
    }

    /// Get the key of this cache entry.
    ///
    /// Safe since the key is immutable since referenced.
    pub fn key(&self) -> T::Key {
        let inner = unsafe { (*self.ptr).inner.get().as_ref().unwrap() };
        inner.key
    }

    /// Get the reference count of this cache entry.
    ///
    /// Note that the count may changes after this function returns. You may need to lock the
    /// whole cache to make sure it is the latest ref count.
    pub fn nref(&self) -> usize {
        let g = self.cache.cache_self().lock();
        let inner = unsafe { (*self.ptr).inner.get().as_ref().unwrap() };
        let nref = inner.nref;
        drop(g);
        nref
    }

    /// Restore the cache entry from a node pointer. Useful for non-RAII operations.
    pub unsafe fn from_ptr(cache: &'a T, ptr: CNodePtr<T::Key, T::Value>) -> Self {
        Self { cache, ptr }
    }
}

/// Guard representing the unique ownership of a cache entry.
pub struct CGuard<'a, T>(&'a CEntry<'a, T>)
where
    T: Cache;

impl<'a, T> CGuard<'a, T>
where
    T: Cache,
{
    /// Check if the buffer is dirty.
    pub fn is_dirty(&self) -> bool {
        let inner = unsafe { (*self.0.ptr).inner.get().as_mut().unwrap() };
        debug_assert_eq!(inner.lock.try_lock().is_none(), true);

        inner.state == CState::Dirty
    }

    /// Return the key of this cache entry.
    pub fn key(&self) -> T::Key {
        let inner = unsafe { (*self.0.ptr).inner.get().as_mut().unwrap() };
        debug_assert_eq!(inner.lock.try_lock().is_none(), true);
        inner.key
    }

    /// Return the key of this cache entry.
    pub fn nlocks(&self) -> usize {
        let inner = unsafe { (*self.0.ptr).inner.get().as_mut().unwrap() };
        debug_assert_eq!(inner.lock.try_lock().is_none(), true);
        debug_assert!(inner.nlocks > 0);
        inner.nlocks
    }

    /// Release the cache entry.
    ///
    /// If flush is true, the data will be flushed to disk if modified. Otherwise, it won't be flushed
    /// until dropped from in-memory cache. If error, just release the lock and donot flush any data
    /// to disk.
    ///
    /// If flush is false, this operation will always succeed.
    pub async fn unlock(self, flush: bool) -> Result<()> {
        let inner = unsafe { (*self.0.ptr).inner.get().as_mut().unwrap() };
        debug_assert_eq!(inner.lock.try_lock().is_none(), true);

        if flush {
            if inner.state == CState::Dirty {
                // Flush to disk.
                let result = self.0.cache.disk_write(&inner.key, &inner.val).await;
                if let Err(e) = result {
                    inner.lock.release();
                    mem::forget(self);
                    return Err(e);
                }
                inner.state = CState::Valid;
            }
        }
        inner.lock.release();
        mem::forget(self);

        Ok(())
    }
}

impl<T> Deref for CGuard<'_, T>
where
    T: Cache,
{
    type Target = T::Value;
    fn deref(&self) -> &Self::Target {
        let inner = unsafe { (*self.0.ptr).inner.get().as_ref().unwrap() };

        debug_assert_eq!(inner.lock.try_lock().is_none(), true);
        debug_assert_ne!(inner.state, CState::Empty);
        debug_assert_ne!(inner.state, CState::Invalid);

        &inner.val
    }
}

impl<T> DerefMut for CGuard<'_, T>
where
    T: Cache,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        let inner = unsafe { (*self.0.ptr.0).inner.get().as_mut().unwrap() };

        debug_assert_eq!(inner.lock.try_lock().is_none(), true);
        debug_assert_ne!(inner.state, CState::Empty);
        debug_assert_ne!(inner.state, CState::Invalid);

        inner.state = CState::Dirty;
        &mut inner.val
    }
}

impl<T> Drop for CGuard<'_, T>
where
    T: Cache,
{
    fn drop(&mut self) {
        panic!("forget to unlock");
    }
}

impl<T> fmt::Debug for CGuard<'_, T>
where
    T: Cache,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let inner = unsafe { (*self.0.ptr.0).inner.get().as_mut().unwrap() };
        f.debug_tuple("CGuard")
            .field(&inner.state)
            .field(&inner.key)
            .field(&inner.val)
            .finish()
    }
}

unsafe impl<K: Send, V: Send> Send for CNodePtr<K, V> {}
unsafe impl<K: Sync, V: Sync> Sync for CNodePtr<K, V> {}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::sync::Arc;
    use alloc::vec::Vec;
    use ksched::task;
    use ktest::*;
    use rand::Rng;
    use task::yield_now;

    struct MyCache<const CACHESZ: usize, const DISKSZ: usize> {
        cache: Spinlock<CacheData<usize, u32>>,
        pub disk: Arc<Mutex<[u32; DISKSZ]>>,
    }

    impl<const CACHESZ: usize, const DISKSZ: usize> MyCache<CACHESZ, DISKSZ> {
        pub fn new() -> Result<Self> {
            Ok(Self {
                cache: Self::new_cache(CACHESZ, || Ok(0))?,
                disk: Arc::try_new(Mutex::new([0; DISKSZ]))?,
            })
        }
    }

    impl<const CACHESZ: usize, const DISKSZ: usize> Cache for MyCache<CACHESZ, DISKSZ> {
        cache_impl!(usize, u32, cache);

        fn disk_read<'a>(
            &'a self,
            key: &'a Self::Key,
            val: &'a mut Self::Value,
        ) -> Self::ReadFut<'a> {
            async move {
                let g = self.disk.lock().await;
                *val = g[key.clone()];
                Ok(())
            }
        }

        fn disk_write<'a>(
            &'a self,
            key: &'a Self::Key,
            val: &'a Self::Value,
        ) -> Self::WriteFut<'a> {
            async move {
                let key: usize = key.clone().into();
                let mut g = self.disk.lock().await;
                g[key] = *val;
                Ok(())
            }
        }
    }

    fn test_write1<const CACHESZ: usize, const DISKSZ: usize>(
        ncpu: usize,
        ntask: usize,
        write_back: bool,
    ) {
        let cache = Arc::new(MyCache::<CACHESZ, DISKSZ>::new().unwrap());
        let mut rng = rand::thread_rng();
        let idx: Vec<usize> = (0..ntask).map(|_| rng.gen_range(0..DISKSZ)).collect();
        for idx in idx {
            let cache = cache.clone();
            task::spawn(0, async move {
                let ent = loop {
                    if let Some(ent) = cache.cache_get(idx, true).await.unwrap() {
                        break ent;
                    }
                    yield_now().await;
                };
                let mut b = ent.lock().await.unwrap();
                let pre = *b;
                *b = pre + 1;
                b.unlock(!write_back).await.unwrap();
                drop(ent);

                let ent = loop {
                    if let Some(ent) = cache.cache_get(idx, true).await.unwrap() {
                        break ent;
                    }
                    yield_now().await;
                };
                let b = ent.lock().await.unwrap();
                assert!(*b > pre);
                b.unlock(!write_back).await.unwrap();
                drop(ent);
            })
            .unwrap();
        }

        run_multi(ncpu);
        let (refed, dirty) = cache_stat(cache.deref());
        assert_eq!(refed, 0);
        if !write_back {
            assert_eq!(dirty, 0);
        }

        let cache2 = cache.clone();
        task::spawn(0, async move {
            let g = cache2.disk.lock().await;
            let sum = g.iter().sum::<u32>();
            if write_back {
                assert!(sum <= ntask as u32);
            } else {
                assert_eq!(sum, ntask as u32);
            }
        })
        .unwrap();
        task::run_all();

        let tot = Arc::new(Spinlock::new(0));
        for i in 0..DISKSZ {
            let tot = tot.clone();
            let cache = cache.clone();
            task::spawn(0, async move {
                let ent = loop {
                    if let Some(ent) = cache.cache_get(i, true).await.unwrap() {
                        break ent;
                    }
                    yield_now().await;
                };
                let b = ent.lock().await.unwrap();
                let pre = *b;
                b.unlock(true).await.unwrap();
                drop(ent);

                *tot.lock() += pre;
            })
            .unwrap();
        }
        task::run_all();
        assert_eq!(*tot.lock(), ntask as u32);

        let cache2 = cache.clone();
        task::spawn(0, async move {
            let g = cache2.disk.lock().await;
            let sum = g.iter().sum::<u32>();
            assert_eq!(sum, ntask as u32);
        })
        .unwrap();
        task::run_all();
    }

    // // May corrupt other testing thread when panic.
    // #[test]
    // #[should_panic]
    // fn forget_to_unlock() {
    //     let cache = Arc::new(MyCache::<10, 100>::new().unwrap());
    //     task::spawn(0, async move {
    //         let ent = cache.cache_get(1).await.unwrap();
    //         let b = ent.lock().await.unwrap();
    //     })
    //     .unwrap();
    //     task::run_all();
    // }

    #[test]
    fn test_nref() {
        const CACHESZ: usize = 100;
        const DISKSZ: usize = 1000;
        let ntask = 200;
        let ncpu = 10;

        let cache = Arc::new(MyCache::<CACHESZ, DISKSZ>::new().unwrap());
        let mut rng = rand::thread_rng();
        let idx: Vec<usize> = (0..ntask).map(|_| rng.gen_range(0..DISKSZ)).collect();
        for idx in idx {
            let cache = cache.clone();
            task::spawn(0, async move {
                let ent = loop {
                    if let Some(ent) = cache.cache_get(idx, true).await.unwrap() {
                        break ent;
                    }
                    yield_now().await;
                };
                let mut b = ent.lock().await.unwrap();
                let pre = *b;
                *b = pre + 1;
                let flush = rand_int(0..2) == 1;
                b.unlock(flush).await.unwrap();
            })
            .unwrap();
        }

        run_multi(ncpu);
        let (refed, dirty) = cache_stat(cache.deref());
        assert_eq!(refed, 0);
        assert!(0 < dirty && dirty <= ntask);
    }

    #[test]
    fn test_write_through() {
        test_write1::<100, 1000>(4, 10, false);
        test_write1::<100, 1000>(4, 100, false);
        test_write1::<100, 1000>(10, 10000, false);
    }

    #[test]
    fn test_write_back() {
        test_write1::<100, 1000>(4, 10, true);
        test_write1::<100, 1000>(4, 100, true);
        test_write1::<100, 1000>(10, 10000, true);
    }
}
