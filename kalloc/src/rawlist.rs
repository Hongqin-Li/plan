#[derive(Copy, Clone, Debug)]
#[repr(C)]
pub struct Rawlist {
    pub prev: *mut Rawlist,
    pub next: *mut Rawlist,
}

impl Rawlist {
    pub unsafe fn init(p: *mut Self) {
        (*p).prev = p;
        (*p).next = p;
    }

    pub unsafe fn is_empty(head: *mut Self) -> bool {
        (*head).next == head
    }

    pub unsafe fn front(head: *mut Self) -> *mut Self {
        (*head).next
    }

    unsafe fn insert(cur: *mut Self, prev: *mut Self, next: *mut Self) {
        (*next).prev = cur;
        (*cur).next = next;
        (*cur).prev = prev;
        (*prev).next = cur;
    }

    unsafe fn del(prev: *mut Self, next: *mut Self) {
        (*next).prev = prev;
        (*prev).next = next;
    }

    pub unsafe fn drop(cur: *mut Self) {
        Self::del((*cur).prev, (*cur).next);
    }

    pub unsafe fn push_front(head: *mut Self, cur: *mut Self) {
        Self::insert(cur, head, (*head).next);
    }

    pub unsafe fn pop_front(head: *mut Self) -> *mut Self {
        let front = Self::front(head);
        Self::drop(front);
        front
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::ptr;

    #[test]
    fn test_push_pop_front() {
        const N: usize = 10;
        let mut item: [Rawlist; N] = [Rawlist {
            prev: ptr::null_mut(),
            next: ptr::null_mut(),
        }; N];
        let mut head = Rawlist {
            prev: ptr::null_mut(),
            next: ptr::null_mut(),
        };
        unsafe {
            Rawlist::init(&mut head);
            assert_eq!(Rawlist::is_empty(&mut head), true);
            for i in 0..N {
                Rawlist::push_front(&mut head, &mut item[i]);
                assert_eq!(Rawlist::is_empty(&mut head), false);
                assert_eq!(Rawlist::front(&mut head), &mut item[i] as *mut Rawlist);
            }

            for i in 0..N {
                assert_eq!(Rawlist::is_empty(&mut head), false);
                assert_eq!(
                    Rawlist::front(&mut head),
                    &mut item[N - 1 - i] as *mut Rawlist
                );

                let p = Rawlist::pop_front(&mut head);
                assert_eq!(p, &mut item[N - 1 - i] as *mut Rawlist);
            }
            assert_eq!(Rawlist::is_empty(&mut head), true);
        }
    }
}
