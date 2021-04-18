//! Mount space.

use crate::{
    chan::Chan,
    error::{Error, Result},
    utils::{arc_new, deque_push_back, deque_push_front, map_insert, vec_push},
};
use alloc::sync::Weak;
use alloc::vec::Vec;
use alloc::{collections::VecDeque, sync::Arc};
use core::cmp::min;
use hashbrown::HashMap;

///
pub struct MountChan {
    create: bool,
    chan: Chan,
}

/// A mount point consisting of serveral directories.
///
/// When attempt to create file(directory) in a union directory, and the file does not exist,
/// the elements of the union are searched in order until one is found with `create` set.
/// The file(directory) is created in that directory; if that attempt fails, the create fails.
pub struct MountUnion {
    chans: VecDeque<MountChan>,
}

impl MountUnion {
    fn find<'a>(&'a self, c: &Chan) -> Option<&'a MountChan> {
        for oc in self.chans.iter() {
            if &oc.chan == c {
                return Some(oc);
            }
        }
        return None;
    }
}

/// Mount, unmount and path resolving.
pub struct MountSpace {
    mnt_table: HashMap<Chan, MountUnion>,
    // root: Arc<Chan>,
}

impl MountSpace {
    fn new() -> Self {
        Self {
            mnt_table: HashMap::new(),
        }
    }

    /// Generate new current directory.
    ///
    /// The first element of `cwd` must be root, which implies that `cwd` should be non-empty.
    pub async fn chdir(&self, cwd: &Vec<Arc<Chan>>, path: &Path) -> Result<Vec<Arc<Chan>>> {
        let (begin, names) = path.resolve(cwd);
        let mut new_cwd = Vec::new();
        for c in cwd[..=begin].iter() {
            vec_push(&mut new_cwd, c.clone())?;
        }
        self.namex(&cwd[begin], names, Some(&mut new_cwd)).await?;
        Ok(new_cwd)
    }

    /// Tune a path to channel.
    pub async fn namec(&self, cwd: &Vec<Arc<Chan>>, path: &Path) -> Result<Option<Arc<Chan>>> {
        let (begin, names) = path.resolve(cwd);
        self.namex(&cwd[begin], names, None).await
    }

    // Tune a path to channel, stop one level early.
    // pub async fn namecparent<'a>(
    //     &'a self,
    //     cwd: &Vec<Arc<Chan>>,
    //     path: &'a Path,
    // ) -> Result<Option<(Arc<Chan>, &[u8])>> {
    //     let (begin, names) = path.resolve(cwd);
    //     let n = names.len();
    //     debug_assert_ne!(n, 0);
    //     self.namex(&cwd[begin], &names[..(n - 1)], None)
    //         .await
    //         .map(|c| c.map(|c| (c, names[n - 1].as_slice())))
    // }

    /// Parse path `names` starting from `begin` channel.
    ///
    /// Append the corresponding channels for each name to the back of `output`,
    /// which is used in `chdir`.
    ///
    /// Return the target channel if found else `None`.
    pub async fn namex(
        &self,
        begin: &Arc<Chan>,
        names: &[Vec<u8>],
        output: Option<&mut Vec<Arc<Chan>>>,
    ) -> Result<Option<Arc<Chan>>> {
        todo!();

        // if names.is_empty() {
        //     return Ok(Some(begin.clone()));
        // }

        // struct Node<'a> {
        //     chan: &'a Chan,
        //     dep: usize,
        //     parent: Option<Weak<Node<'a>>>,
        //     child: VecDeque<Arc<Node<'a>>>,
        // }

        // // Non-recursive DFS.
        // let root = Node {chan: begin, dep : 0, parent: None, child: VecDeque::new()};

        // fn expand(u: Node) {

        // }

        // let pushnxt = |que: &mut VecDeque<Arc<Node>>,
        //                cur: &Arc<Chan>,
        //                dep: usize,
        //                parent: Option<Arc<Node>>|
        //  -> Result<()> {
        //     if let Some(mu) = self.mnt_table.get(cur) {
        //         for mc in mu.chans.iter() {
        //             deque_push_back(
        //                 que,
        //                 arc_new(Node {
        //                     chan: &mc.chan,
        //                     dep,
        //                     parent: parent.clone(),
        //                 })?,
        //             )?;
        //         }
        //     } else {
        //         deque_push_back(
        //             que,
        //             arc_new(Node {
        //                 chan: &cur,
        //                 dep,
        //                 parent: parent.clone(),
        //             })?,
        //         )?;
        //     }
        //     Ok(())
        // };

        // pushnxt(&mut que, &begin, 0, None)?;
        // while let Some(u) = que.pop_front() {
        //     if let Some(x) = names.get(u.dep) {
        //         if let Some(nc) = u.chan.dev.walk(&u.chan, x)?.await? {
        //             // Found it.
        //             if u.dep + 1 == names.len() {
        //                 if let Some(v) = output {
        //                     let mut u = u;
        //                     let i = v.len();
        //                     v.try_reserve(names.len()).map_err(|_| Error::OutOfMemory)?;
        //                     vec_push(v,u.chan)?;
        //                     while let Some(fa) = u.parent.clone() {
        //                         u = fa;
        //                         vec_push(v, u.chan)?;
        //                     }
        //                     v[i..].reverse();
        //                 }

        //                 return Ok(Some(nc));
        //             }
        //             pushnxt(&mut que, &nc, u.dep + 1, Some(u))?;
        //         }
        //     }
        // }
        // Ok(None)
    }

    /// Mount `to` in replacement of `from`.
    ///
    /// Both `to` and `from` are required to be a directory. If `front`, the new directory
    /// `to` will be pushed to the front of the union directory. Otherwise, it will be pushed back.
    /// `create` is such a flag that allows creation of new files inside `to` according to the
    /// creation rules(see [MountUnion]).
    fn mount(&mut self, from: Chan, to: Chan, create: bool, front: bool) -> Result<bool> {
        match self.mnt_table.get_mut(&from) {
            Some(m) => {
                if m.find(&to).is_some() {
                    Err(Error::Conflict)
                } else {
                    if front {
                        deque_push_front(&mut m.chans, MountChan { create, chan: to })?;
                    } else {
                        deque_push_back(&mut m.chans, MountChan { create, chan: to })?;
                    }
                    Ok(false)
                }
            }
            None => {
                let mut chans = VecDeque::new();
                deque_push_back(&mut chans, MountChan { create, chan: to })?;
                map_insert(&mut self.mnt_table, from, MountUnion { chans })?;
                Ok(true)
            }
        }
    }
}

/// Path without any `.` and `..` elements.
pub enum Path {
    /// Absolute path is just a list of file name.
    Absolute(Vec<Vec<u8>>),
    /// Relative path consisting of the number of ``..` ahead and a list of file name.
    Relative(usize, Vec<Vec<u8>>),
}

impl Path {
    ///
    pub fn resolve(&self, cwd: &Vec<Arc<Chan>>) -> (usize, &Vec<Vec<u8>>) {
        debug_assert_ne!(cwd.len(), 0);
        let (begin, names) = match self {
            Path::Absolute(names) => (0, names),
            Path::Relative(ndotdots, names) => {
                let l = cwd.len() - 1;
                (l - min(l, ndotdots.clone()), names)
            }
        };
        debug_assert!(begin < cwd.len());
        (begin, names)
    }
}
