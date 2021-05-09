//! A multi-producer, single-consumer queue for sending values between asynchronous tasks.
use core::alloc::AllocError;

use alloc::boxed::Box;
use alloc::sync::Arc;

use intrusive_collections::intrusive_adapter;
use intrusive_collections::{LinkedList, LinkedListLink};

use crate::{condvar::Condvar, sync::Spinlock};

/// Message node.
#[derive(Debug)]
pub struct Node<T> {
    link: LinkedListLink,
    data: T,
    /// If this message is received by [`Receiver`].
    received: bool,
}

intrusive_adapter!(NodeAdapter<T> = Box<Node<T>>: Node<T> { link: LinkedListLink });

/// The transmission end of a bounded mpsc channel.
///
/// This value is created by the [`channel`](channel) function.
#[derive(Debug)]
pub struct Sender<T>(Arc<Channel<T>>);

/// The receiving end of a bounded mpsc channel.
///
/// This value is created by the [`channel`](channel) function.
#[derive(Debug)]
pub struct Receiver<T>(Arc<Channel<T>>);

#[derive(Debug)]
struct ChannelInner<T> {
    /// Number of corresponding senders of this channerl.
    nsend: usize,
    /// `true` when the channel is open.
    open: bool,
    /// FIFO queue used to send messages to the receiver.
    msgque: LinkedList<NodeAdapter<T>>,
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
    ///
    pub fn is_closed(&self) -> bool {
        !self.0.inner.lock().open
    }
    /// Sends a value.
    ///
    /// A successful send occurs when it is determined that the other end of the
    /// channel has not hung up already. An unsuccessful send would be one where
    /// the corresponding receiver has already been closed. Note that a return
    /// value of `Err` means that the data will never be received, but a return
    /// value of `Ok` does not mean that the data will be received. It is
    /// possible for the corresponding receiver to hang up immediately after
    /// this function returns `Ok`.
    ///
    /// # Errors
    ///
    /// If the receive half of the channel is closed, either due to [`close`]
    /// being called or the [`Receiver`] handle dropping, the function returns
    /// an error. The error includes the value passed to `send`.
    ///
    /// If allocation error happened during sending, the value is dropped and
    /// return an error of [`None`].
    ///
    /// [`close`]: Receiver::close
    /// [`Receiver`]: Receiver
    ///
    /// # Examples
    ///
    /// In the following example, each call to `send` will block until the
    /// previously sent value was received.
    ///
    /// ```
    /// # ksched::task::spawn(0, async {
    /// use ksched::sync::mpsc;
    /// use ksched::task;
    ///
    /// let (tx, mut rx) = mpsc::channel().unwrap();
    ///
    /// task::spawn(0, async move {
    ///     for i in 0..10 {
    ///         if let Err(Some(_)) = tx.send(i) {
    ///             println!("receiver dropped");
    ///             return;
    ///         }
    ///     }
    /// }).unwrap();
    ///
    /// while let Some(i) = rx.recv().await {
    ///     println!("got = {}", i);
    /// }
    /// }).unwrap();
    /// # ksched::task::run_all();
    /// ```
    pub fn send(&self, value: T) -> Result<(), Option<T>> {
        let u = Box::try_new(Node {
            link: LinkedListLink::new(),
            data: value,
            received: false,
        })
        .map_err(|_| None)?;

        let mut g = self.0.inner.lock();
        if g.open {
            g.msgque.push_back(u);
            self.0.recv_cvar.notify_one();
            drop(g);
            Ok(())
        } else {
            Err(Some(u.data))
        }
    }
}

impl<T> Drop for Sender<T> {
    fn drop(&mut self) {
        let mut g = self.0.inner.lock();
        g.nsend -= 1;
        if g.nsend == 0 {
            self.0.recv_cvar.notify_one();
        }
        drop(g);
    }
}

impl<T> Clone for Sender<T> {
    fn clone(&self) -> Self {
        self.0.inner.lock().nsend += 1;
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
    /// # ksched::task::spawn(0, async {
    /// use ksched::sync::mpsc;
    /// use ksched::task;
    ///
    /// let (tx, mut rx) = mpsc::channel().unwrap();
    ///
    /// task::spawn(0, async move {
    ///     tx.send("hello").unwrap();
    /// });
    ///
    /// assert_eq!(Some("hello"), rx.recv().await);
    /// assert_eq!(None, rx.recv().await);
    /// # }).unwrap();
    /// # ksched::task::run_all();
    /// ```
    ///
    /// Values are buffered:
    ///
    /// ```
    /// # ksched::task::spawn(0, async {
    /// use ksched::sync::mpsc;
    /// let (tx, mut rx) = mpsc::channel().unwrap();
    ///
    /// tx.send("hello").unwrap();
    /// tx.send("world").unwrap();
    ///
    /// assert_eq!(Some("hello"), rx.recv().await);
    /// assert_eq!(Some("world"), rx.recv().await);
    /// # }).unwrap();
    /// # ksched::task::run_all();
    /// ```
    pub async fn recv(&mut self) -> Option<T> {
        loop {
            let g = self.0.inner.lock();
            let mut g = self
                .0
                .recv_cvar
                .spin_wait_until(g, |g| !g.msgque.is_empty() || g.nsend == 0)
                .await;
            if let Some(b) = g.msgque.pop_front() {
                return Some(b.data);
            } else if g.nsend == 0 {
                return None;
            }
        }
    }

    /// Closes the receiving half of a channel, without dropping it.
    ///
    /// This prevents any further messages from being sent on the channel while
    /// still enabling the receiver to drain messages that are buffered.
    pub fn close(&mut self) {
        let mut g = self.0.inner.lock();
        g.open = false;
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
            nsend: 1,
            open: true,
            msgque: LinkedList::new(NodeAdapter::new()),
        }),
        send_cvar: Condvar::new(),
        recv_cvar: Condvar::new(),
    })?;
    Ok((Sender(c.clone()), Receiver(c)))
}
