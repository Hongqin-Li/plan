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
pub enum CacheState {
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
struct CacheNodeInner<K, V> {
    /// Guarded by [`CacheData`].
    pub nref: usize,
    /// Guarded by [`CacheData`]. Immutable since get.
    pub key: K,

    /// Lock guard.
    pub lock: Mutex<()>,
    /// Guarded by [`CacheNodeInner::lock`].
    pub state: CacheState,
    /// Guarded by [`CacheNodeInner::lock`].
    pub val: V,
}

impl<K: Debug, V: Debug> Debug for CacheNodeInner<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CacheNodeInner")
            .field("nref", &self.nref)
            .field("lock", &self.lock)
            .field("state", &self.state)
            .field("key", &self.key)
            .field("val", &self.val)
            .finish()
    }
}

/// Pointer the a cache entry node.
pub struct CacheNodePtr<K, V>(*const CacheNode<K, V>);
impl<K, V> CacheNodePtr<K, V> {
    /// Retrieve node by address pointing to that node.
    pub unsafe fn from_addr(ptr: usize) -> Self {
        Self(ptr as *const CacheNode<K, V>)
    }
    /// Convert node pointer to address.
    pub fn to_addr(self) -> usize {
        self.0 as usize
    }
}

impl<K, V> Copy for CacheNodePtr<K, V> {}
impl<K, V> Clone for CacheNodePtr<K, V> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}

impl<K, V> Deref for CacheNodePtr<K, V> {
    type Target = CacheNode<K, V>;
    fn deref(&self) -> &Self::Target {
        unsafe { self.0.as_ref().unwrap() }
    }
}

impl<K, V> Debug for CacheNodePtr<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("CacheNodePtr").field(&self.0).finish()
    }
}

/// Cache entry node.
pub struct CacheNode<K, V> {
    link: LinkedListLink,
    /// Unsafe inner data.
    inner: UnsafeCell<CacheNodeInner<K, V>>,
}

impl<K: Debug, V: Debug> Debug for CacheNode<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CacheNode")
            .field("link", &self.link)
            .field("inner", &self.inner)
            .finish()
    }
}

intrusive_adapter!(CacheNodeAdapter<K, V> = Box<CacheNode<K, V>>: CacheNode<K, V> { link: LinkedListLink });

/// Inner data structure of the cache.
pub struct CacheData<K, V> {
    map: HashMap<K, CacheNodePtr<K, V>>,
    lru: LinkedList<CacheNodeAdapter<K, V>>,
}

impl<K: Debug, V: Debug> Debug for CacheData<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CacheData")
            .field("map", &self.map)
            .field("lru", &self.lru)
            .finish()
    }
}

#[allow(missing_docs)]
#[async_trait::async_trait_static]
pub trait Cache: Sized {
    type Key: Hash + Eq + Default + Copy + fmt::Debug;
    type Value: fmt::Debug;
    async fn disk_read(&self, key: &Self::Key, value: &mut Self::Value) -> Result<()>;
    async fn disk_write(&self, key: &Self::Key, value: &Self::Value) -> Result<()>;

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
        let mut lru = LinkedList::new(CacheNodeAdapter::new());
        for _ in 0..n {
            lru.push_back(Box::try_new(CacheNode {
                link: LinkedListLink::new(),
                inner: UnsafeCell::new(CacheNodeInner {
                    nref: 0,
                    key: Self::Key::default(),
                    val: default_val()?,
                    lock: Mutex::new(()),
                    state: CacheState::Empty,
                }),
            })?);
        }
        Ok(Spinlock::new(CacheData {
            map: HashMap::new(),
            lru,
        }))
    }

    /// Mark all dirty entry as invalid without synchronizing with disk. May cause inconsistency!
    /// Donot implement it.
    fn cache_invalidate<'a>(&'a self) {
        cache_invalidate(self);
    }

    /// Function used to retrieve the cache.
    fn cache_self<'a>(&'a self) -> &'a Spinlock<CacheData<Self::Key, Self::Value>>;

    type GetFut<'a>
    where
        Self: 'a,
        Self::Key: 'a,
        Self::Value: 'a;

    /// Get a cache item by key. Won't lock it.
    /// If key has already been in memory, this operation always succeed.
    /// If cannot reserve cache entry, returns [None].
    /// Donot implement it. Instead, injected to the trait implementation by [`super::cache_impl`].
    fn cache_get<'a>(&'a self, key: Self::Key, flush: bool) -> Self::GetFut<'a>;
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

        type GetFut<'a>
        where
            Self: 'a,
            Self::Key: 'a,
            Self::Value: 'a,
        = impl core::future::Future<
            Output = kcore::error::Result<Option<$crate::cache::CacheEntry<'a, Self>>>,
        >;

        fn cache_get<'a>(&'a self, key: Self::Key, flush: bool) -> Self::GetFut<'a> {
            $crate::cache::cache_get(self, key, flush)
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
) -> Result<Option<(bool, CacheNodePtr<T::Key, T::Value>)>> {
    let mut g = sel.cache_self().lock();

    let CacheData {
        ref mut map,
        ref mut lru,
    } = g.deref_mut();

    if let Some(ptr) = map.get(&key) {
        let mut cur = unsafe { LinkedList::cursor_mut_from_ptr(lru, ptr.0) };
        let node = cur.remove().unwrap();
        let u = unsafe { node.inner.get().as_mut().unwrap() };
        u.nref += 1;
        debug_assert_ne!(u.state, CacheState::Empty);

        lru.push_back(node);

        return Ok(Some((false, ptr.clone())));
    }

    let mut cur = lru.front_mut();
    while let Some(u) = cur.get() {
        let inner = unsafe { u.inner.get().as_mut().unwrap() };
        if inner.nref == 0 {
            let ptr = CacheNodePtr(u as *const CacheNode<T::Key, T::Value>);

            if inner.state == CacheState::Dirty {
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
                if inner.state != CacheState::Empty {
                    debug_assert_eq!(map.get(&inner.key).unwrap().0, ptr.0);
                    map.remove(&inner.key);
                }

                inner.nref += 1;
                inner.key = key;

                // SAFETY: Guarded by implicit lock.
                // Since anyone who want to access inner.state after this point
                // should first acquire g, which must be after `drop(g)`. Thus,
                // no need for memory fence here.
                inner.state = CacheState::Invalid;
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
) -> Result<Option<CacheEntry<'a, T>>> {
    loop {
        if let Some((dirty, ptr)) = cache_get1(sel, key, flush)? {
            if !dirty {
                break Ok(Some(CacheEntry { cache: sel, ptr }));
            } else {
                let inner = unsafe { (*ptr).inner.get().as_mut().unwrap() };
                let result = sel.disk_write(&inner.key, &inner.val).await;
                if result.is_ok() {
                    inner.state = CacheState::Valid;
                }
                unsafe { inner.lock.release() }
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
        if inner.nref == 0 && inner.state == CacheState::Dirty {
            inner.state = CacheState::Invalid;
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
        if inner.state == CacheState::Dirty {
            dirty += 1;
        }
        cur.move_next();
    }
    drop(g);
    (refed, dirty)
}

/// Representing a client of a cache entry.
///
/// There may be several [`CacheEntry`] that refer to the same cache entry (i.e. same key) at a time.
/// Therefore, [`Cache`] maintains reference counter for each in-memory cache entry. If the
/// reference couter is not zero, it cannot be replace by another cache entyr. Once the the counter
/// decreases to zero, it will be moved to the back of LRU and can be flushed to disk when replaced
/// by another cache entry.
pub struct CacheEntry<'a, T: Cache> {
    cache: &'a T,
    ptr: CacheNodePtr<T::Key, T::Value>,
}

impl<'a, T: Cache> Drop for CacheEntry<'a, T> {
    fn drop(&mut self) {
        let inner = unsafe { (*self.ptr.0).inner.get().as_mut().unwrap() };
        let g = self.cache.cache_self().lock();
        debug_assert_ne!(inner.nref, 0);
        debug_assert_ne!(inner.state, CacheState::Empty);
        // SAFETY: nref is guarded by cache.inner.
        inner.nref -= 1;

        // #[cfg(test)]
        // println!("cache_drop: key {:?}, nref: {}", inner.key, inner.nref);
        drop(g);
    }
}

impl<'a, T: Cache> CacheEntry<'a, T> {
    /// Lock and read the cache entry.
    pub async fn lock(&'a self) -> Result<CacheGuard<'a, T>> {
        let inner = unsafe { (*self.ptr.0).inner.get().as_mut().unwrap() };

        inner.lock.acquire().await;
        debug_assert_ne!(inner.nref, 0);
        debug_assert_ne!(inner.state, CacheState::Empty);

        if inner.state == CacheState::Invalid {
            // Read from disk.
            let result = self.cache.disk_read(&inner.key, &mut inner.val).await;
            if let Err(e) = result {
                unsafe { inner.lock.release() }
                return Err(e);
            }
            inner.state = CacheState::Valid;
        }
        Ok(CacheGuard(self))
    }

    /// Get pointer to this cache entry.
    pub fn leak(self) -> CacheNodePtr<T::Key, T::Value> {
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
    pub unsafe fn from_ptr(cache: &'a T, ptr: CacheNodePtr<T::Key, T::Value>) -> Self {
        Self { cache, ptr }
    }
}

/// Guard representing the unique ownership of a cache entry.
pub struct CacheGuard<'a, T: Cache>(&'a CacheEntry<'a, T>);

impl<'a, T: Cache> CacheGuard<'a, T> {
    /// Check if the buffer is dirty.
    pub fn is_dirty(&self) -> bool {
        let inner = unsafe { (*self.0.ptr).inner.get().as_mut().unwrap() };
        debug_assert_eq!(inner.lock.try_lock().is_none(), true);

        inner.state == CacheState::Dirty
    }

    /// Return the key of this cache entry.
    pub fn key(&self) -> T::Key {
        let inner = unsafe { (*self.0.ptr).inner.get().as_mut().unwrap() };
        debug_assert_eq!(inner.lock.try_lock().is_none(), true);
        inner.key
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
            if inner.state == CacheState::Dirty {
                // Flush to disk.
                let result = self.0.cache.disk_write(&inner.key, &inner.val).await;
                if let Err(e) = result {
                    unsafe { inner.lock.release() }
                    mem::forget(self);
                    return Err(e);
                }
                inner.state = CacheState::Valid;
            }
        }
        unsafe { inner.lock.release() }
        mem::forget(self);

        Ok(())
    }
}

impl<T: Cache> Deref for CacheGuard<'_, T> {
    type Target = T::Value;
    fn deref(&self) -> &Self::Target {
        let inner = unsafe { (*self.0.ptr).inner.get().as_ref().unwrap() };

        debug_assert_eq!(inner.lock.try_lock().is_none(), true);
        debug_assert_ne!(inner.state, CacheState::Empty);
        debug_assert_ne!(inner.state, CacheState::Invalid);

        &inner.val
    }
}

impl<T: Cache> DerefMut for CacheGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        let inner = unsafe { (*self.0.ptr.0).inner.get().as_mut().unwrap() };

        debug_assert_eq!(inner.lock.try_lock().is_none(), true);
        debug_assert_ne!(inner.state, CacheState::Empty);
        debug_assert_ne!(inner.state, CacheState::Invalid);

        inner.state = CacheState::Dirty;
        &mut inner.val
    }
}

impl<T: Cache> Drop for CacheGuard<'_, T> {
    fn drop(&mut self) {
        panic!("forget to unlock");
    }
}

impl<T: Cache> fmt::Debug for CacheGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let inner = unsafe { (*self.0.ptr.0).inner.get().as_mut().unwrap() };
        f.debug_tuple("CacheGuard")
            .field(&inner.state)
            .field(&inner.key)
            .field(&inner.val)
            .finish()
    }
}

unsafe impl<K: Send, V: Send> Send for CacheNodePtr<K, V> {}
unsafe impl<K: Sync, V: Sync> Sync for CacheNodePtr<K, V> {}

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

    #[async_trait::async_trait_static]
    impl<const CACHESZ: usize, const DISKSZ: usize> Cache for MyCache<CACHESZ, DISKSZ> {
        cache_impl!(usize, u32, cache);

        async fn disk_read(&self, key: &Self::Key, val: &mut Self::Value) -> Result<()> {
            let g = self.disk.lock().await;
            *val = g[key.clone()];
            Ok(())
        }

        async fn disk_write(&self, key: &Self::Key, val: &Self::Value) -> Result<()> {
            let key: usize = key.clone().into();
            let mut g = self.disk.lock().await;
            g[key] = *val;
            Ok(())
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
        assert!(dirty <= ntask);
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
