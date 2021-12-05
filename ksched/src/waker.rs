use crate::task::Task;
use alloc::sync::Arc;
use core::{
    mem::{self, ManuallyDrop},
    task::{RawWaker, RawWakerVTable, Waker},
};

struct FakeWaker {
    waker: FakeRawWaker,
}

struct FakeRawWaker {
    data: *const (),
    _vtable: &'static RawWakerVTable,
}

pub(crate) fn get_task(waker: &Waker) -> Arc<Task> {
    let waker: &FakeWaker = unsafe { mem::transmute(waker) };
    if waker.waker._vtable != waker_vtable() {
        panic!("not waker from ksched");
    } else if waker.waker.data.is_null() {
        panic!("task has been taken");
    }
    let arc_task = unsafe { Arc::from_raw(waker.waker.data as *const Task) };
    let task_ref = ManuallyDrop::new(arc_task);
    (*task_ref).clone()
}

pub(crate) fn waker(task: Arc<Task>) -> Waker {
    let ptr = Arc::into_raw(task) as *const ();
    unsafe { Waker::from_raw(RawWaker::new(ptr, waker_vtable())) }
}

fn waker_vtable() -> &'static RawWakerVTable {
    &RawWakerVTable::new(
        clone_arc_raw,
        wake_arc_raw,
        wake_by_ref_arc_raw,
        drop_arc_raw,
    )
}

unsafe fn clone_arc_raw(_data: *const ()) -> RawWaker {
    unimplemented!();
}

unsafe fn wake_arc_raw(_data: *const ()) {
    unimplemented!();
}

unsafe fn wake_by_ref_arc_raw(_data: *const ()) {
    unimplemented!();
}

unsafe fn drop_arc_raw(data: *const ()) {
    drop(Arc::from_raw(data as *const Task))
}
