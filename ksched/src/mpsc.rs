//! A multi-producer, single-consumer queue for sending values between asynchronous tasks.

use crate::{condvar::Condvar, sync::Spinlock};
use alloc::{boxed::Box, sync::Arc};
use core::alloc::AllocError;
use intrusive_collections::{intrusive_adapter, LinkedList, LinkedListLink};

/// Message that carries user-provided data.
#[derive(Debug)]
pub struct Message<T> {
    link: LinkedListLink,
    data: T,
}

intrusive_adapter!(MessageAdapter<T> = Box<Message<T>>: Message<T> { link: LinkedListLink });

/// The transmission end of a unbounded mpsc channel.
///
/// This value is created by the [`channel`](channel) function.
#[derive(Debug)]
pub struct Sender<T>(Arc<Channel<T>>);

/// The receiving end of a unbounded mpsc channel.
///
/// This value is created by the [`channel`](channel) function.
#[derive(Debug)]
pub struct Receiver<T>(Arc<Channel<T>>);

#[derive(Debug)]
struct ChannelInner<T> {
    /// Number of corresponding senders of this channel.
    sender_cnt: usize,
    /// `true` when the channel is open.
    open: bool,
    /// FIFO queue used to send messages to the receiver.
    msg_queue: LinkedList<MessageAdapter<T>>,
}

#[derive(Debug)]
struct Channel<T> {
    inner: Spinlock<ChannelInner<T>>,
    /// If sender is waiting for space to pushed to queue. Guarded by inner.
    send_cvar: Condvar,
    /// If receiver is waiting for sender. Guarded by inner.
    recv_cvar: Condvar,
}

impl<T> Sender<T> {
    /// Check whether the channel is closed.
    ///
    /// A closed channel cannot be sent to.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::task::spawn(async {
    /// use ksched::sync::mpsc;
    /// use ksched::task;
    ///
    /// let (tx, mut rx) = mpsc::channel::<usize>().unwrap();
    /// assert_eq!(tx.is_closed(), false);
    /// rx.close();
    /// assert_eq!(tx.is_closed(), true);
    /// # }).unwrap();
    /// # ksched::task::run();
    /// ```
    pub fn is_closed(&self) -> bool {
        !self.0.inner.lock().open
    }

    /// Sends a value.
    ///
    /// A successful send occurs when it is determined that the other end of the channel has not
    /// hung up already. An unsuccessful send would be one where the corresponding receiver has
    /// already been closed or allocation failed. Note that a return value of `Err` means that the
    /// data will never be received, but a return value of `Ok` does not mean that the data will
    /// be received. It is possible for the corresponding receiver to hang up immediately after
    /// this function returns `Ok`.
    ///
    /// # Errors
    ///
    /// If the receive half of the channel is closed, either due to [`close`] being called or the
    /// [`Receiver`] handle dropping, the function returns an error. Or if allocation fails during
    /// create a message for sending, the function returns an error. The error includes the value
    /// passed to `send`.
    ///
    /// [`close`]: Receiver::close
    /// [`Receiver`]: Receiver
    ///
    /// # Examples
    ///
    /// In the following example, each call to `send` will block until the previously sent value
    /// was received.
    ///
    /// ```
    /// # ksched::task::spawn(async {
    /// use ksched::sync::mpsc;
    /// use ksched::task;
    ///
    /// let (tx, mut rx) = mpsc::channel().unwrap();
    ///
    /// task::spawn(async move {
    ///     for i in 0..10 {
    ///         if let Err(_) = tx.send(i) {
    ///             println!("receiver dropped");
    ///             return;
    ///         }
    ///     }
    /// }).unwrap();
    ///
    /// while let Some(i) = rx.recv().await {
    ///     println!("got = {}", i);
    /// }
    /// # }).unwrap();
    /// # ksched::task::run();
    /// ```
    pub fn send(&self, value: T) -> Result<(), T> {
        if let Ok(mut uninit_box) = Box::try_new_uninit() {
            let msg = Message {
                link: LinkedListLink::new(),
                data: value,
            };
            uninit_box.write(msg);

            let box_msg = unsafe { uninit_box.assume_init() };
            let mut inner = self.0.inner.lock();
            if inner.open {
                inner.msg_queue.push_back(box_msg);
                self.0.recv_cvar.notify_one();
                drop(inner);
                Ok(())
            } else {
                Err(box_msg.data)
            }
        } else {
            Err(value)
        }
    }
}

impl<T> Drop for Sender<T> {
    fn drop(&mut self) {
        let mut inner = self.0.inner.lock();
        inner.sender_cnt -= 1;
        if inner.sender_cnt == 0 {
            self.0.recv_cvar.notify_one();
        }
        drop(inner);
    }
}

impl<T> Clone for Sender<T> {
    fn clone(&self) -> Self {
        self.0.inner.lock().sender_cnt += 1;
        Self(self.0.clone())
    }
}

impl<T> Receiver<T> {
    /// Receives the next value for this receiver.
    ///
    /// `None` is returned when all `Sender` halves have dropped, indicating
    /// that no further values can be sent on the channel.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::task::spawn(async {
    /// use ksched::sync::mpsc;
    /// use ksched::task;
    ///
    /// let (tx, mut rx) = mpsc::channel().unwrap();
    ///
    /// task::spawn(async move {
    ///     tx.send("hello").unwrap();
    /// });
    ///
    /// assert_eq!(Some("hello"), rx.recv().await);
    /// assert_eq!(None, rx.recv().await);
    /// # }).unwrap();
    /// # ksched::task::run();
    /// ```
    ///
    /// Values are buffered:
    ///
    /// ```
    /// # ksched::task::spawn(async {
    /// use ksched::sync::mpsc;
    /// let (tx, mut rx) = mpsc::channel().unwrap();
    ///
    /// tx.send("hello").unwrap();
    /// tx.send("world").unwrap();
    ///
    /// assert_eq!(Some("hello"), rx.recv().await);
    /// assert_eq!(Some("world"), rx.recv().await);
    /// # }).unwrap();
    /// # ksched::task::run();
    /// ```
    pub async fn recv(&mut self) -> Option<T> {
        loop {
            let inner = self.0.inner.lock();
            let mut inner = self
                .0
                .recv_cvar
                .spin_wait_until(inner, |inner| {
                    !inner.msg_queue.is_empty() || inner.sender_cnt == 0
                })
                .await;
            if let Some(msg) = inner.msg_queue.pop_front() {
                return Some(msg.data);
            } else if inner.sender_cnt == 0 {
                return None;
            }
        }
    }

    /// Closes the receiving half of a channel, without dropping it.
    ///
    /// This prevents any further messages from being sent on the channel while
    /// still enabling the receiver to drain messages that are buffered.
    pub fn close(&mut self) {
        let mut inner = self.0.inner.lock();
        inner.open = false;
    }
}

impl<T> Drop for Receiver<T> {
    fn drop(&mut self) {
        self.close();
    }
}

/// Creates a unbounded mpsc channel for communicating between asynchronous tasks.
pub fn channel<T>() -> Result<(Sender<T>, Receiver<T>), AllocError> {
    let c = Arc::try_new(Channel {
        inner: Spinlock::new(ChannelInner {
            sender_cnt: 1,
            open: true,
            msg_queue: LinkedList::new(MessageAdapter::new()),
        }),
        send_cvar: Condvar::new(),
        recv_cvar: Condvar::new(),
    })?;
    Ok((Sender(c.clone()), Receiver(c)))
}
