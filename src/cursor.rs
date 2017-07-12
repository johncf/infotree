use ::CVec;
use base::CursorNav;
use node::{Node, NodesPtr};
use traits::{Leaf, PathInfo};
use mines::SliceExt; // for boom_get

use std::fmt;

/// An object that can be used to traverse a `Node`.
///
/// `Cursor` is very lightweight. All operations are done entirely using stack memory -- no
/// heap allocations are made at any point.
///
/// Note: `Cursor` takes more than 200B on stack (exact size mainly depends on the size of `PI`)
#[derive(Clone)]
pub struct Cursor<'a, L: Leaf + 'a, NP: 'a, PI> {
    root: &'a Node<L, NP>,
    steps: CVec<CursorStep<'a, L, NP, PI>>,
}

#[derive(Clone)]
struct CursorStep<'a, L: Leaf + 'a, NP: 'a, PI> {
    nodes: &'a [Node<L, NP>],
    idx: usize, // index at which cursor descended
    path_info: PI,
}

impl<'a, L, NP, PI> fmt::Debug for CursorStep<'a, L, NP, PI>
    where L: Leaf + 'a,
          NP: NodesPtr<L> + 'a,
          PI: PathInfo<L::Info> + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "CursorStep {{ nodes.len: {}, idx: {}, path_info: {:?} }}",
                  self.nodes.len(), self.idx, self.path_info)
    }
}

impl<'a, L, NP, PI> Cursor<'a, L, NP, PI>
    where L: Leaf + 'a,
          NP: NodesPtr<L> + 'a,
          PI: PathInfo<L::Info>,
{
    /// Create a new cursor from a root node.
    pub fn new(node: &Node<L, NP>) -> Cursor<L, NP, PI> {
        Cursor {
            root: node,
            steps: CVec::new(),
        }
    }

    /// Returns a reference to the root node.
    pub fn root(&self) -> &'a Node<L, NP> {
        self.root
    }

    /// Returns a reference to the current node, where the cursor is at.
    pub fn current(&self) -> &'a Node<L, NP> {
        match self.steps.last() {
            Some(cstep) => unsafe { &cstep.nodes.boom_get(cstep.idx) },
            None => self.root,
        }
    }

    /// Returns a reference to the leaf's value if the current node is a leaf.
    pub fn leaf(&self) -> Option<&'a L> {
        self.current().leaf()
    }

    /// Height of the current node from leaves.
    pub fn height(&self) -> usize {
        self.current().height()
    }

    /// Descend the tree once, on the child for which `f` returns `true`.
    ///
    /// Returns `None` if cursor is at a leaf node, or if `f` returned `false` on all children.
    ///
    /// The arguments to `f` are treated exactly the same as in [`Node::path_traverse`].
    ///
    /// Panics if tree depth is greater than 8.
    ///
    /// [`Node::path_traverse`]: ../enum.Node.html#method.path_traverse
    pub fn descend_by<F>(&mut self, f: F, reversed: bool) -> Option<&'a Node<L, NP>>
        where F: FnMut(PI, L::Info, usize, usize) -> bool
    {
        let cur_node = self.current();
        let res = if reversed {
            cur_node.path_traverse_rev(self.path_info(), f)
        } else {
            cur_node.path_traverse(self.path_info(), f)
        };
        match res {
            Ok((index, path_info, child)) => {
                self.descend_raw(cur_node.children(), index, path_info);
                Some(child)
            }
            Err(_) => None,
        }
    }
}

impl<'a, L, NP, PI> Cursor<'a, L, NP, PI>
    where L: Leaf + 'a,
          NP: NodesPtr<L> + 'a,
          PI: PathInfo<L::Info>,
{
    fn descend_raw(&mut self, nodes: &'a [Node<L, NP>], idx: usize, path_info: PI) {
        // ArrayVec::push(e) returns Some(e) on overflow!
        assert!(self.steps.push(CursorStep { nodes, idx, path_info }).is_none());
    }
}

impl<'a, L, NP, PI> CursorNav for Cursor<'a, L, NP, PI>
    where L: Leaf + 'a,
          NP: NodesPtr<L> + 'a,
          PI: PathInfo<L::Info>,
{
    type Leaf = L;
    type NodesPtr = NP;
    type PathInfo = PI;

    fn is_root(&self) -> bool {
        self.steps.len() == 0
    }

    fn path_info(&self) -> PI {
        match self.steps.last() {
            Some(cstep) => cstep.path_info,
            None => PI::identity(),
        }
    }

    #[doc(hidden)]
    fn _leaf(&self) -> Option<&L> {
        self.leaf()
    }

    #[doc(hidden)]
    fn _height(&self) -> Option<usize> {
        Some(self.height())
    }

    #[doc(hidden)]
    fn _current(&self) -> Option<&Node<L, NP>> {
        Some(self.current())
    }

    #[doc(hidden)]
    fn _current_must(&self) -> &Node<L, NP> {
        self.current()
    }

    fn reset(&mut self) {
        self.steps.clear();
    }

    fn ascend(&mut self) -> Option<&Node<L, NP>> {
        self.steps.pop().map(|cstep| &cstep.nodes[cstep.idx])
    }

    fn descend_first(&mut self) -> Option<&Node<L, NP>> {
        self.descend_by(|_, _, _, _| true, false)
    }

    fn descend_last(&mut self) -> Option<&Node<L, NP>> {
        self.descend_by(|_, _, _, _| true, true)
    }

    fn left_sibling(&mut self) -> Option<&Node<L, NP>> {
        let &mut Cursor { ref root, ref mut steps } = self;
        match steps.last_mut() {
            Some(&mut CursorStep { nodes, ref mut idx, ref mut path_info }) => {
                if *idx > 0 {
                    *idx -= 1;
                    *path_info = path_info.extend_inv(nodes[*idx].info());
                    Some(root)
                } else {
                    None
                }
            }
            None => None, // at the root
        }
    }

    fn right_sibling(&mut self) -> Option<&Node<L, NP>> {
        let &mut Cursor { ref root, ref mut steps } = self;
        match steps.last_mut() {
            Some(&mut CursorStep { nodes, ref mut idx, ref mut path_info }) => {
                if *idx + 1 < nodes.len() {
                    *path_info = path_info.extend(nodes[*idx].info());
                    *idx += 1;
                    Some(root)
                } else {
                    None
                }
            }
            None => None, // at the root
        }
    }
}

impl<'a, L, NP, PI> IntoIterator for Cursor<'a, L, NP, PI>
    where L: Leaf + 'a,
          NP: NodesPtr<L> + 'a,
          PI: PathInfo<L::Info>,
{
    type IntoIter = LeafIter<'a, L, NP, PI>;
    type Item = &'a L;

    fn into_iter(mut self) -> LeafIter<'a, L, NP, PI> {
        self.reset();
        LeafIter {
            inner: self,
            init_done: false,
        }
    }
}

pub struct LeafIter<'a, L: 'a, NP: 'a, PI> where L: Leaf {
    inner: Cursor<'a, L, NP, PI>,
    init_done: bool,
}

impl<'a, L, NP, PI> Iterator for LeafIter<'a, L, NP, PI>
    where L: Leaf + 'a,
          NP: NodesPtr<L> + 'a,
          PI: PathInfo<L::Info>,
{
    type Item = &'a L;
    fn next(&mut self) -> Option<&'a L> {
        if !self.init_done {
            self.init_done = true;
            self.inner.first_leaf();
            self.inner.leaf()
        } else {
            self.inner.next_node();
            self.inner.leaf()
        }
    }
}

#[cfg(test)]
mod tests {
    use ::base::{Cursor, CursorNav};
    use ::test_help::*;

    #[test]
    fn leaf_traversal() {
        let tree: NodeRc<_> = (1..21).map(|i| ListLeaf(i)).collect();
        let mut leaf_iter = CursorT::new(&tree).into_iter();
        for i in 1..21 {
            assert_eq!(leaf_iter.next(), Some(&ListLeaf(i)));
        }
        assert_eq!(leaf_iter.next(), None);
        let mut cursor = CursorT::new(&tree);
        assert_eq!(cursor.last_leaf(), Some(&ListLeaf(20)));
        for i in (1..20).rev() {
            assert_eq!(cursor.prev_leaf(), Some(&ListLeaf(i)));
        }
        assert_eq!(cursor.prev_leaf(), None);
    }

    #[test]
    fn path_extend() {
        let tree: NodeRc<_> = (1..21).map(|i| ListLeaf(i)).collect();
        let mut cursor = Cursor::<_, _, ListPath>::new(&tree);
        assert_eq!(cursor.first_leaf().unwrap(), &ListLeaf(1));
        assert_eq!(cursor.path_info(), ListPath { index: 0, run: 0 });
        cursor.reset();
        assert_eq!(cursor.last_leaf().unwrap(), &ListLeaf(20));
        assert_eq!(cursor.path_info(), ListPath { index: 19, run: 19*20/2 });
    }

    // FIXME need more tests
}
