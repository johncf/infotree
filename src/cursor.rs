use ::CVec;
use base::Node;
use traits::{Leaf, PathInfo};
use mines::SliceExt; // for boom_get

use std::fmt;

/// An object that can be used to traverse a `Node`.
///
/// `Cursor` is very lightweight. All operations are done entirely using stack memory -- no
/// heap allocations are made at any point.
///
/// Note: `Cursor` takes more than 200B on stack (exact size depends on the size of `P`)
#[derive(Clone)]
pub struct Cursor<'a, L: Leaf + 'a, P> {
    root: &'a Node<L>,
    steps: CVec<CursorStep<'a, L, P>>,
}

#[derive(Clone)]
struct CursorStep<'a, L: Leaf + 'a, P> {
    nodes: &'a [Node<L>],
    idx: usize, // index at which cursor descended
    path_info: P,
}

impl<'a, L, P> fmt::Debug for CursorStep<'a, L, P> where L: Leaf + 'a, P: PathInfo<L::Info> + fmt::Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "CursorStep {{ nodes.len: {}, idx: {}, path_info: {:?} }}",
                  self.nodes.len(), self.idx, self.path_info)
    }
}

impl<'a, L, P> Cursor<'a, L, P> where L: Leaf + 'a, P: PathInfo<L::Info> {
    /// Create a new cursor from a root node.
    pub fn new(node: &Node<L>) -> Cursor<L, P> {
        Cursor {
            root: node,
            steps: CVec::new(),
        }
    }

    /// Returns a reference to the root node.
    pub fn root(&self) -> &'a Node<L> {
        self.root
    }

    /// Returns a reference to the current node, where the cursor is at.
    pub fn current(&self) -> &'a Node<L> {
        match self.steps.last() {
            Some(cstep) => unsafe { &cstep.nodes.boom_get(cstep.idx) },
            None => self.root,
        }
    }

    /// Returns a reference to the leaf's value if the current node is a leaf.
    pub fn leaf(&self) -> Option<&'a L> {
        self.current().leaf()
    }

    /// Returns whether the cursor is currently at the root.
    pub fn is_root(&self) -> bool {
        self.steps.len() == 0
    }

    /// Height of the current node from leaves.
    pub fn height(&self) -> usize {
        self.current().height()
    }

    /// The cumulative info along the path from root to this node. Returns `P::identity()` if the
    /// current node is root.
    pub fn path_info(&self) -> P {
        match self.steps.last() {
            Some(cstep) => cstep.path_info,
            None => P::identity(),
        }
    }
}

// navigational methods
impl<'a, L, P> Cursor<'a, L, P> where L: Leaf + 'a, P: PathInfo<L::Info> {
    pub fn reset(&mut self) {
        self.steps.clear();
    }

    pub fn ascend(&mut self) -> Option<&'a Node<L>> {
        self.steps.pop().map(|cstep| &cstep.nodes[cstep.idx])
    }

    /// Descend the first child recursively till `height`.
    pub fn first_leaf(&mut self) -> &'a L {
        while self.descend_first().is_some() {}
        self.leaf().unwrap()
    }

    /// Descend the last child recursively till `height`.
    pub fn last_leaf(&mut self) -> &'a L {
        while self.descend_last().is_some() {}
        self.leaf().unwrap()
    }

    pub fn descend_first(&mut self) -> Option<&Node<L>> {
        self.descend_by(|_, _, _, _| true, false)
    }

    pub fn descend_last(&mut self) -> Option<&Node<L>> {
        self.descend_by(|_, _, _, _| true, true)
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
    pub fn descend_by<F>(&mut self, f: F, reversed: bool) -> Option<&'a Node<L>>
        where F: FnMut(P, L::Info, usize, usize) -> bool
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

    /// Make the cursor point to the next element at the same height.
    ///
    /// If there is no next element, it returns `None` and cursor resets to root.
    pub fn next_node(&mut self) -> Option<&'a Node<L>> {
        let mut depth_delta = 0;
        loop {
            match self.steps.pop() {
                Some(CursorStep { nodes, mut idx, mut path_info }) => {
                    if idx + 1 < nodes.len() {
                        path_info = path_info.extend(nodes[idx].info());
                        idx += 1;
                        self.steps.push(CursorStep { nodes, idx, path_info });
                        while depth_delta > 0 {
                            // descend the left-most element
                            self.descend_first().unwrap();
                            depth_delta -= 1;
                        }
                        return Some(self.current());
                    } else {
                        depth_delta += 1;
                    }
                }
                None => return None, // at the root
            }
        }
    }

    /// Make the cursor point to the previous element at the same height.
    ///
    /// If there is no previous element, it returns `None` and cursor resets to root.
    pub fn prev_node(&mut self) -> Option<&'a Node<L>> {
        let mut depth_delta = 0;
        loop {
            match self.steps.pop() {
                Some(CursorStep { nodes, mut idx, mut path_info }) => {
                    if idx > 0 {
                        idx -= 1;
                        path_info = path_info.extend_inv(nodes[idx].info());
                        self.steps.push(CursorStep { nodes, idx, path_info });
                        while depth_delta > 0 {
                            // descend the right-most element
                            self.descend_last().unwrap();
                            depth_delta -= 1;
                        }
                        return Some(self.current());
                    } else {
                        depth_delta += 1;
                    }
                }
                None => return None, // at the root
            }
        }
    }

    /// Calls `next_node` and returns the leaf value if it is a leaf node.
    pub fn next_leaf(&mut self) -> Option<&'a L> {
        self.next_node().and_then(|n| n.leaf())
    }

    /// Calls `prev_node` and returns the leaf value if it is a leaf node.
    pub fn prev_leaf(&mut self) -> Option<&'a L> {
        self.prev_node().and_then(|n| n.leaf())
    }
}

impl<'a, L, P> Cursor<'a, L, P> where L: Leaf + 'a, P: PathInfo<L::Info> {
    fn descend_raw(&mut self, nodes: &'a [Node<L>], idx: usize, path_info: P) {
        // ArrayVec::push(e) returns Some(e) on overflow!
        assert!(self.steps.push(CursorStep { nodes, idx, path_info }).is_none());
    }
}

impl<'a, L, P> IntoIterator for Cursor<'a, L, P> where L: Leaf + 'a, P: PathInfo<L::Info> {
    type IntoIter = LeafIter<'a, L, P>;
    type Item = &'a L;

    fn into_iter(mut self) -> LeafIter<'a, L, P> {
        self.reset();
        LeafIter {
            inner: self,
            init_done: false,
        }
    }
}

pub struct LeafIter<'a, L, P> where L: Leaf + 'a, P: PathInfo<L::Info> {
    inner: Cursor<'a, L, P>,
    init_done: bool,
}

impl<'a, L, P> Iterator for LeafIter<'a, L, P> where L: Leaf + 'a, P: PathInfo<L::Info> {
    type Item = &'a L;
    fn next(&mut self) -> Option<&'a L> {
        if !self.init_done {
            self.init_done = true;
            Some(self.inner.first_leaf())
        } else {
            self.inner.next_leaf()
        }
    }
}

#[cfg(test)]
mod tests {
    use ::base::{Cursor, Node};
    use ::test_help::*;

    #[test]
    fn leaf_traversal() {
        let tree: Node<_> = (1..21).map(|i| ListLeaf(i)).collect();
        let mut leaf_iter = CursorT::new(&tree).into_iter();
        for i in 1..21 {
            assert_eq!(leaf_iter.next(), Some(&ListLeaf(i)));
        }
        assert_eq!(leaf_iter.next(), None);

        let mut cursor = CursorT::new(&tree);
        assert_eq!(cursor.last_leaf(), &ListLeaf(20));
        for i in (1..20).rev() {
            assert_eq!(cursor.prev_leaf(), Some(&ListLeaf(i)));
        }
        assert_eq!(cursor.prev_leaf(), None);
    }

    #[test]
    fn path_extend() {
        let tree: Node<_> = (1..21).map(|i| ListLeaf(i)).collect();
        let mut cursor = Cursor::<_, ListPath>::new(&tree);
        assert_eq!(cursor.first_leaf(), &ListLeaf(1));
        assert_eq!(cursor.path_info(), ListPath { index: 0, run: 0 });
        cursor.reset();
        assert_eq!(cursor.last_leaf(), &ListLeaf(20));
        assert_eq!(cursor.path_info(), ListPath { index: 19, run: 19*20/2 });
    }

    // FIXME need more tests
}
