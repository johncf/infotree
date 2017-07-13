use super::conf::{CConf, Rc33M};
use super::CursorNav;
use node::Node;
use traits::{Leaf, PathInfo};
use mines::SliceExt; // for boom_get

use arrayvec::ArrayVec;

use std::fmt;

/// An object that can be used to traverse a `Node`.
///
/// `Cursor` is very lightweight. All operations are done entirely using stack memory -- no
/// heap allocations are made at any point.
///
/// Note: `Cursor` takes more than 200B on stack (exact size mainly depends on the size of `PI`)
#[derive(Clone)]
pub struct Cursor<'a, L, PI, CONF = Rc33M>
    where L: Leaf + 'a,
          CONF: CConf<'a, L, PI>,
          CONF::Ptr: 'a,
{
    root: &'a Node<L, CONF::Ptr>,
    steps: ArrayVec<CONF::StepsBuf>,
}

#[derive(Clone)]
pub struct CStep<'a, L, PI, CONF>
    where L: Leaf + 'a,
          CONF: CConf<'a, L, PI>,
          CONF::Ptr: 'a,
{
    nodes: &'a [Node<L, CONF::Ptr>],
    idx: usize, // index at which cursor descended
    path_info: PI,
}

impl<'a, L, PI, CONF> fmt::Debug for CStep<'a, L, PI, CONF>
    where L: Leaf + 'a,
          PI: fmt::Debug,
          CONF: CConf<'a, L, PI>,
          CONF::Ptr: 'a,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "CStep {{ nodes.len: {}, idx: {}, path_info: {:?} }}",
                  self.nodes.len(), self.idx, self.path_info)
    }
}

impl<'a, L, PI, CONF> Cursor<'a, L, PI, CONF>
    where L: Leaf + 'a,
          PI: PathInfo<L::Info>,
          CONF: CConf<'a, L, PI>,
          CONF::Ptr: 'a,
{
    /// Create a new cursor from a root node.
    pub fn new(node: &'a Node<L, CONF::Ptr>) -> Self {
        Cursor {
            root: node,
            steps: ArrayVec::new(),
        }
    }

    /// Returns a reference to the root node.
    pub fn root(&self) -> &'a Node<L, CONF::Ptr> {
        self.root
    }

    /// Returns a reference to the current node, where the cursor is at.
    pub fn current(&self) -> &'a Node<L, CONF::Ptr> {
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
    pub fn descend_by<F>(&mut self, f: F, reversed: bool) -> Option<&'a Node<L, CONF::Ptr>>
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

    fn descend_raw(&mut self, nodes: &'a [Node<L, CONF::Ptr>], idx: usize, path_info: PI) {
        // ArrayVec::push(e) returns Some(e) on overflow!
        assert!(self.steps.push(CStep { nodes, idx, path_info }).is_none());
    }
}

impl<'a, L, PI, CONF> CursorNav for Cursor<'a, L, PI, CONF>
    where L: Leaf + 'a,
          PI: PathInfo<L::Info>,
          CONF: CConf<'a, L, PI>,
          CONF::Ptr: 'a,
{
    type Leaf = L;
    type NodesPtr = CONF::Ptr;
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
    fn _current(&self) -> Option<&Node<L, CONF::Ptr>> {
        Some(self.current())
    }

    #[doc(hidden)]
    fn _current_must(&self) -> &Node<L, CONF::Ptr> {
        self.current()
    }

    fn reset(&mut self) {
        self.steps.clear();
    }

    fn ascend(&mut self) -> Option<&Node<L, CONF::Ptr>> {
        self.steps.pop().map(|cstep| &cstep.nodes[cstep.idx])
    }

    fn descend_first(&mut self) -> Option<&Node<L, CONF::Ptr>> {
        self.descend_by(|_, _, _, _| true, false)
    }

    fn descend_last(&mut self) -> Option<&Node<L, CONF::Ptr>> {
        self.descend_by(|_, _, _, _| true, true)
    }

    fn left_sibling(&mut self) -> Option<&Node<L, CONF::Ptr>> {
        let &mut Cursor { ref root, ref mut steps } = self;
        match steps.last_mut() {
            Some(&mut CStep { nodes, ref mut idx, ref mut path_info }) => {
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

    fn right_sibling(&mut self) -> Option<&Node<L, CONF::Ptr>> {
        let &mut Cursor { ref root, ref mut steps } = self;
        match steps.last_mut() {
            Some(&mut CStep { nodes, ref mut idx, ref mut path_info }) => {
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

impl<'a, L, PI, CONF> IntoIterator for Cursor<'a, L, PI, CONF>
    where L: Leaf + 'a,
          PI: PathInfo<L::Info>,
          CONF: CConf<'a, L, PI>,
          CONF::Ptr: 'a,
{
    type IntoIter = LeafIter<'a, L, PI, CONF>;
    type Item = &'a L;

    fn into_iter(mut self) -> Self::IntoIter {
        self.reset();
        LeafIter {
            inner: self,
            init_done: false,
        }
    }
}

pub struct LeafIter<'a, L, PI, CONF>
    where L: Leaf + 'a,
          CONF: CConf<'a, L, PI>,
          CONF::Ptr: 'a,
{
    inner: Cursor<'a, L, PI, CONF>,
    init_done: bool,
}

impl<'a, L, PI, CONF> Iterator for LeafIter<'a, L, PI, CONF>
    where L: Leaf + 'a,
          PI: PathInfo<L::Info>,
          CONF: CConf<'a, L, PI>,
          CONF::Ptr: 'a,
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
    use cursor::{Cursor, CursorNav};
    use test_help::*;

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
        let mut cursor = Cursor::<_, ListPath>::new(&tree);
        assert_eq!(cursor.first_leaf().unwrap(), &ListLeaf(1));
        assert_eq!(cursor.path_info(), ListPath { index: 0, run: 0 });
        cursor.reset();
        assert_eq!(cursor.last_leaf().unwrap(), &ListLeaf(20));
        assert_eq!(cursor.path_info(), ListPath { index: 19, run: 19*20/2 });
    }

    // FIXME need more tests
}
