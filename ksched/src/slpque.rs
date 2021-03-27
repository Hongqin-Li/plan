use core::{alloc::AllocError, cell::UnsafeCell, task::Waker};

use alloc::collections::VecDeque;

pub struct SleepQueue {
    inner: UnsafeCell<Inner>,
}

impl SleepQueue {
    pub fn new() -> Self {
        Self {
            inner: UnsafeCell::new(Inner::new()),
        }
    }
    pub fn wakeup_all(&self) {
        // Safe since UnsafeCell is not sync.
        unsafe { (*self.inner.get()).wakeup_all() }
    }

    pub fn wakeup_one(&self) {
        // Safe since UnsafeCell is not sync.
        unsafe { (*self.inner.get()).wakeup_one() }
    }

    pub fn sleep(&self, w: Waker) -> Result<(), AllocError> {
        // Safe since UnsafeCell is not sync.
        unsafe { (*self.inner.get()).insert(w) }
    }
}

struct Inner {
    slpque: VecDeque<Waker>,
}

impl Inner {
    fn new() -> Self {
        Self {
            slpque: VecDeque::new(),
        }
    }

    /// Notifies at most one blocked operation.
    fn wakeup_one(&mut self) {
        if let Some(w) = self.slpque.pop_front() {
            w.wake();
        }
    }

    /// Notifies all blocked operations.
    fn wakeup_all(&mut self) {
        while let Some(w) = self.slpque.pop_front() {
            w.wake();
        }
    }

    fn insert(&mut self, w: Waker) -> Result<(), AllocError> {
        self.slpque.try_reserve(1).map_err(|_| AllocError)?;
        self.slpque.push_back(w);
        Ok(())
    }
}
