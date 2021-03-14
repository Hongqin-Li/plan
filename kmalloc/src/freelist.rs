use core::ptr::{self, null_mut};

#[derive(Clone, Copy)]
pub struct Freelist {
    next: *mut Freelist,
}

impl Freelist {
    pub fn new() -> Self {
        Freelist {
            next: ptr::null_mut(),
        }
    }
    pub fn is_empty(&self) -> bool {
        self.next.is_null()
    }
    /// Pop a block of memory from the free list.
    ///
    /// Retures the start address of the memory.
    /// Callers **must** check if the free list is empty before calling this function.
    pub fn pop(&mut self) -> *mut u8 {
        let p = self.next;
        unsafe {
            self.next = (*(self.next)).next;
        }
        return p as *mut u8;
    }
    /// Add a block of memory starting at `p` to the free list.
    pub fn push(&mut self, p: *mut u8) {
        let p = p as *mut Self;
        unsafe {
            (*p).next = self.next;
        }
        self.next = p;
    }
}

impl Default for Freelist {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const NPAGES: usize = 10;
    const PGSIZE: usize = 64;

    #[test]
    fn test_all() {
        let mut f = Freelist::default();
        let mut buf: [u8; NPAGES * PGSIZE] = [0; NPAGES * PGSIZE];
        assert_eq!(f.is_empty(), true);
        for i in 0..NPAGES {
            f.push((buf.as_mut_ptr() as usize + PGSIZE * i) as *mut u8);
        }
        for i in 0..NPAGES {
            let x = f.pop();
            assert_eq!(x.is_null(), false);
            let offset = x as usize - buf.as_mut_ptr() as usize;
            assert_eq!(offset % PGSIZE, 0);
            assert_eq!(offset / PGSIZE + i + 1, NPAGES);
        }
        assert_eq!(f.is_empty(), true);
    }
}
