#[derive(Copy, Clone, Debug)]
pub struct List {
    pub prev: *mut List,
    pub next: *mut List,
}

impl List {
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
    pub unsafe fn back(head: *mut Self) -> *mut Self {
        (*head).prev
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
    pub unsafe fn push_back(head: *mut Self, cur: *mut Self) {
        Self::insert(cur, (*head).prev, head);
    }
    pub unsafe fn pop_front(head: *mut Self) -> *mut Self {
        let front = Self::front(head);
        Self::drop(front);
        front
    }
    pub unsafe fn pop_back(head: *mut Self) -> *mut Self {
        let back = Self::back(head);
        Self::drop(back);
        back
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use core::ptr;

    #[test]
    fn test_push_pop_back() {
        const N: usize = 10;
        let mut item: [List; N] = [List {
            prev: ptr::null_mut(),
            next: ptr::null_mut(),
        }; N];
        let mut head = List {
            prev: ptr::null_mut(),
            next: ptr::null_mut(),
        };
        unsafe {
            List::init(&mut head);
            assert_eq!(List::is_empty(&mut head), true);
            for i in 0..N {
                List::push_back(&mut head, &mut item[i]);
                assert_eq!(List::is_empty(&mut head), false);
                assert_eq!(List::back(&mut head), &mut item[i] as *mut List);
                assert_eq!(List::front(&mut head), &mut item[0] as *mut List);
            }

            for i in 0..N {
                assert_eq!(List::is_empty(&mut head), false);
                assert_eq!(List::back(&mut head), &mut item[N - 1 - i] as *mut List);
                assert_eq!(List::front(&mut head), &mut item[0] as *mut List);

                let p = List::pop_back(&mut head);
                assert_eq!(p, &mut item[N - 1 - i] as *mut List);
            }
            assert_eq!(List::is_empty(&mut head), true);
        }
    }

    #[test]
    fn test_push_pop_front() {
        const N: usize = 10;
        let mut item: [List; N] = [List {
            prev: ptr::null_mut(),
            next: ptr::null_mut(),
        }; N];
        let mut head = List {
            prev: ptr::null_mut(),
            next: ptr::null_mut(),
        };
        unsafe {
            List::init(&mut head);
            assert_eq!(List::is_empty(&mut head), true);
            for i in 0..N {
                List::push_front(&mut head, &mut item[i]);
                assert_eq!(List::is_empty(&mut head), false);
                assert_eq!(List::front(&mut head), &mut item[i] as *mut List);
                assert_eq!(List::back(&mut head), &mut item[0] as *mut List);
            }

            for i in 0..N {
                assert_eq!(List::is_empty(&mut head), false);
                assert_eq!(List::front(&mut head), &mut item[N - 1 - i] as *mut List);
                assert_eq!(List::back(&mut head), &mut item[0] as *mut List);

                let p = List::pop_front(&mut head);
                assert_eq!(p, &mut item[N - 1 - i] as *mut List);
            }
            assert_eq!(List::is_empty(&mut head), true);
        }
    }
}
