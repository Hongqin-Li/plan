//! The Pipe file system.
//! FIXME: The proc cannot be killed when blocking now.
use alloc::boxed::Box;
use alloc::vec::Vec;
use core::usize;
use intrusive_collections::intrusive_adapter;
use intrusive_collections::{LinkedList, LinkedListLink};
use kalloc::list::List;
use kcore::{
    chan::{ChanId, ChanKind, Dirent},
    dev::Device,
    error::{Error, Result},
};
use ksched::sync::Condvar;
use ksched::sync::Mutex;

fn parse_path<'a>(path: u64) -> (u64, usize, &'a mut Node) {
    let raw_path = (path >> 3) << 3;
    let node_id = (path - raw_path) as usize;
    let node = unsafe { (raw_path as *mut Node).as_mut().unwrap() };
    (raw_path, node_id, node)
}

/// The Pipe device driver.
#[derive(Default)]
pub struct Pipe(Mutex<PipeInner>);

#[derive(Default)]
struct PipeInner {
    nxtid: usize,
    list: LinkedList<NodeAdapter>,
}

#[repr(align(8))]
struct Node {
    id: usize,
    nref: usize,
    dref: [usize; 2],
    cvar: [Condvar; 2],
    /// Each vector in the data list is from one sender.
    data: [List<Vec<u8>>; 2],
    link: LinkedListLink,
}

intrusive_adapter!(NodeAdapter = Box<Node>: Node { link: LinkedListLink });

struct NodePtr(*mut Node);

#[async_trait::async_trait_try]
impl Device for Pipe {
    async fn shutdown(self)
    where
        Self: Sized,
    {
    }

    async fn attach(&self, aname: &[u8]) -> Result<ChanId>
    where
        Self: Sized,
    {
        let mut g = self.0.lock().await;
        let node = Box::try_new(Node {
            id: g.nxtid,
            nref: 1,
            dref: [0; 2],
            cvar: [Condvar::new(), Condvar::new()],
            data: [List::new(), List::new()],
            link: LinkedListLink::new(),
        })?;
        let path = node.as_ref() as *const _ as u64;
        debug_assert_eq!(path % 8, 0);
        g.list.push_back(node);
        g.nxtid += 1;

        Ok(ChanId {
            path,
            version: 0,
            kind: ChanKind::Dir,
        })
    }

    async fn open(
        &self,
        dir: &ChanId,
        name: &[u8],
        create_dir: Option<bool>,
    ) -> Result<Option<ChanId>> {
        let g = self.0.lock().await;
        let (raw_path, node_id, node) = parse_path(dir.path);

        let ret = if name.is_empty() {
            node.nref += 1;
            if (1..=2).contains(&node_id) {
                node.dref[node_id - 1] += 1;
            }
            Ok(Some(dir.clone()))
        } else if create_dir.is_some() {
            Err(Error::BadRequest("create in devpipe"))
        } else {
            debug_assert_eq!(dir.kind, ChanKind::Dir);
            match name {
                b"data" => {
                    node.nref += 1;
                    node.dref[0] += 1;
                    Ok(Some(ChanId {
                        path: raw_path + 1,
                        version: 0,
                        kind: ChanKind::File,
                    }))
                }
                b"data1" => {
                    node.nref += 1;
                    node.dref[1] += 1;
                    Ok(Some(ChanId {
                        path: raw_path + 2,
                        version: 0,
                        kind: ChanKind::File,
                    }))
                }
                _ => Ok(None),
            }
        };
        drop(g);
        ret
    }

    async fn close(&self, c: ChanId) {
        let (_raw_path, node_id, node) = parse_path(c.path);

        let mut g = self.0.lock().await;
        node.nref -= 1;
        if (1..=2).contains(&node_id) {
            let di = node_id - 1;
            node.dref[di] -= 1;
            node.cvar[1 - di].notify_all();
        }

        if node.nref == 0 {
            debug_assert_eq!(node.dref, [0, 0]);
            let mut cur = unsafe { g.list.cursor_mut_from_ptr(node) };
            cur.remove();
        }
        drop(g);
    }

    async fn remove(&self, c: &ChanId) -> Result<bool> {
        Err(Error::BadRequest("remove file of devpipe"))
    }

    async fn truncate(&self, c: &ChanId, size: usize) -> Result<usize> {
        Ok(0)
    }

    async fn stat(&self, c: &ChanId) -> Result<Dirent> {
        todo!()
    }

    async fn wstat(&self, c: &ChanId, dirent: &Dirent) -> Result<()> {
        todo!()
    }

    async fn read(&self, c: &ChanId, buf: &mut [u8], off: usize) -> Result<usize> {
        debug_assert_eq!(c.kind, ChanKind::File);
        let (_raw_path, node_id, node) = parse_path(c.path);
        debug_assert!(node_id == 1 || node_id == 2);
        let di = node_id - 1;

        loop {
            let g = self.0.lock().await;

            let mut empty = false;
            let mut i = 0;
            if let Some(bytes) = node.data[di].back_mut() {
                while i < buf.len() {
                    if let Some(b) = bytes.pop() {
                        buf[i] = b;
                        i += 1;
                    } else {
                        break;
                    }
                }
                if bytes.is_empty() {
                    empty = true;
                }
            }
            if empty {
                node.data[di].pop_back();
            }

            if empty || i != 0 || buf.len() == 0 {
                return Ok(i);
            }

            // No writer.
            if node.dref[1 - di] == 0 {
                return Ok(0);
            }
            node.cvar[di].await_notify(g).await;
        }
    }

    async fn write(&self, c: &ChanId, buf: &[u8], off: usize) -> Result<usize> {
        debug_assert_eq!(c.kind, ChanKind::File);
        let (_raw_path, node_id, node) = parse_path(c.path);
        debug_assert!(node_id == 1 || node_id == 2);
        let di = node_id - 1;

        let mut v = Vec::new();
        v.try_reserve(buf.len())?;
        for b in buf {
            v.push(*b);
        }
        v.reverse();

        let g = self.0.lock().await;
        if node.dref[1 - di] == 0 {
            return Err(Error::Gone("write broken pipe"));
        }
        node.data[1 - di].push_front(v)?;
        node.cvar[1 - di].notify_all();
        drop(g);

        Ok(buf.len())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::sync::Arc;
    use kcore::chan::Chan;
    use ksched::task;

    #[test]
    fn test_pipe() {
        let devpipe = Arc::new(Pipe::default());
        task::spawn(0, async move {
            let p = Chan::attach(devpipe, b"").await.unwrap();
            let data = p.open(b"data", None).await.unwrap().unwrap();
            let data1 = p.open(b"data1", None).await.unwrap().unwrap();

            task::spawn(0, async move {
                assert_eq!(data.write(b"12345", 0).await.unwrap(), 5);
                let mut buf = [0u8; 10];
                assert_eq!(data.read(&mut buf, 0).await.unwrap(), 4);
                assert_eq!(&buf[0..4], b"abcd");
                data.close().await;
            })
            .unwrap();
            task::spawn(0, async move {
                let mut buf = [0u8; 5];
                assert_eq!(data1.read(&mut buf, 0).await.unwrap(), 5);
                assert_eq!(&buf, b"12345");
                assert_eq!(data1.write(b"abcd", 0).await.unwrap(), 4);
                data1.close().await;
            })
            .unwrap();
            p.close().await;
        })
        .unwrap();
        task::run_all();
    }

    #[test]
    fn test_pipe_read_portion() {
        let devpipe = Arc::new(Pipe::default());
        task::spawn(0, async move {
            let p = Chan::attach(devpipe, b"").await.unwrap();
            let data = p.open(b"data", None).await.unwrap().unwrap();
            let data1 = p.open(b"data1", None).await.unwrap().unwrap();

            task::spawn(0, async move {
                assert_eq!(data.write(b"12345abcd", 0).await.unwrap(), 9);
                assert_eq!(data.write(b"0", 0).await.unwrap(), 1);
                data.close().await;
            })
            .unwrap();
            task::spawn(0, async move {
                let mut buf = [0u8; 5];
                assert_eq!(data1.read(&mut buf, 0).await.unwrap(), 5);
                assert_eq!(&buf, b"12345");
                assert_eq!(data1.read(&mut buf, 0).await.unwrap(), 4);
                assert_eq!(&buf[0..4], b"abcd");
                assert_eq!(data1.read(&mut buf, 0).await.unwrap(), 1);
                assert_eq!(&buf[0..1], b"0");
                assert_eq!(data1.read(&mut buf, 0).await.unwrap(), 0);
                data1.close().await;
            })
            .unwrap();
            p.close().await;
        })
        .unwrap();
        task::run_all();
    }

    #[test]
    fn test_pipe_write_broken() {
        let devpipe = Arc::new(Pipe::default());
        task::spawn(0, async move {
            let p = Chan::attach(devpipe, b"").await.unwrap();
            let data = p.open(b"data", None).await.unwrap().unwrap();
            assert_eq!(data.write(b"", 0).await.is_err(), true);
            data.close().await;
            p.close().await;
        })
        .unwrap();
        task::run_all();
    }

    #[test]
    fn test_pipe_read_empty() {
        let devpipe = Arc::new(Pipe::default());
        task::spawn(0, async move {
            let p = Chan::attach(devpipe, b"").await.unwrap();
            let data = p.open(b"data", None).await.unwrap().unwrap();
            let mut buf = [0; 10];
            assert_eq!(data.read(&mut buf, 0).await.unwrap(), 0);
            data.close().await;
            p.close().await;
        })
        .unwrap();
        task::run_all();
    }
}
