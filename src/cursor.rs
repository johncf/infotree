use super::*;
use std::fmt;

/// A useful type alias for easy initialization of `Cursor`.
pub type CursorT<'a, L> = Cursor<'a, L, ()>;

/// An object that can be used to traverse a `Node`.
///
/// `Cursor` is very lightweight. All operations are done entirely using stack memory -- no
/// heap allocations are made at any point.
pub struct Cursor<'a, L: Leaf + 'a, P> {
    root: &'a Node<L>,
    steps: CVec<CursorStep<'a, L, P>>,
}

#[derive(Clone)]
struct CursorStep<'a, L: Leaf + 'a, P> {
    nodes: &'a NVec<Node<L>>,
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

    /// Returns the current node the cursor is pointing to.
    pub fn current(&self) -> &'a Node<L> {
        match self.steps.last() {
            Some(cstep) => &cstep.nodes[cstep.idx],
            None => self.root,
        }
    }

    /// Returns whether the cursor is currently at the root of the tree.
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

    pub fn reset(&mut self) {
        self.steps.clear();
    }

    pub fn ascend(&mut self) -> Option<&'a Node<L>> {
        self.steps.pop().map(|cstep| &cstep.nodes[cstep.idx])
    }

    /// Descend on the `idx`-th child from left. The first child is numbered `0`.
    pub fn descend_first(&mut self, idx: usize) -> Option<&'a Node<L>> {
        self.descend_extended(|_, _, i, _| i == idx, false)
    }

    /// Descend on the `idx`-th child from right. The last child is numbered `0`.
    pub fn descend_last(&mut self, idx: usize) -> Option<&'a Node<L>> {
        self.descend_extended(|_, _, _, i| i == idx, true)
    }

    /// Descend the tree once, on the child for which `f` returns `true`. It internally calls
    /// `descend_extended` for path info book-keeping. (exists for convenience when `P=()`).
    ///
    /// Returns `None` if `f` returned `false` on all children, or if it was a leaf node.
    ///
    /// The arguments to `f` are treated exactly the same as in [`Node::traverse`].
    ///
    /// [`Node::traverse`]: ../enum.Node.html#method.traverse
    pub fn descend<F>(&mut self, mut f: F, reversed: bool) -> Option<&'a Node<L>>
        where F: FnMut(L::Info, usize, usize) -> bool
    {
        self.descend_extended(|_, a, i, j| f(a, i, j), reversed)
    }

    /// Similar to descend, with the arguments to `f` treated exactly the same as in
    /// [`Node::path_traverse`].
    ///
    /// [`Node::path_traverse`]: ../enum.Node.html#method.path_traverse
    ///
    /// Panics if tree depth is greater than 8.
    pub fn descend_extended<F>(&mut self, f: F, reversed: bool) -> Option<&'a Node<L>>
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
                self.descend_raw(cur_node.children_must(), index, path_info);
                Some(child)
            }
            Err(_) => None,
        }
    }

    fn descend_raw(&mut self, nodes: &'a NVec<Node<L>>, idx: usize, path_info: P) {
        // ArrayVec::push(e) returns Some(e) on overflow!
        assert!(self.steps.push(CursorStep { nodes, idx, path_info }).is_none());
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
                            self.descend_first(0).unwrap();
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
                            self.descend_last(0).unwrap();
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

    pub fn first_leaf_below(&mut self) -> &'a L {
        while let Some(_) = self.descend_first(0) {}
        self.current().leaf().unwrap()
    }

    pub fn last_leaf_below(&mut self) -> &'a L {
        while let Some(_) = self.descend_last(0) {}
        self.current().leaf().unwrap()
    }

    /// If the current node is a leaf, calls `next_node`, otherwise calls `first_leaf_below`.
    ///
    /// Thus at the last leaf of the tree, it returns `None` and cursor resets to root, therefore
    /// calling `next_leaf` again will return the first leaf of the tree.
    pub fn next_leaf(&mut self) -> Option<&'a L> {
        match self.current().leaf() {
            None => Some(self.first_leaf_below()),
            Some(_) => self.next_node().map(|node| node.leaf().unwrap()),
        }
    }

    /// If the current node is a leaf, calls `prev_node`, otherwise calls `last_leaf_below`.
    ///
    /// Thus at the first leaf of the tree, it returns `None` and cursor resets to root, therefore
    /// calling `prev_leaf` again will return the last leaf of the tree.
    pub fn prev_leaf(&mut self) -> Option<&'a L> {
        match self.current().leaf() {
            None => Some(self.last_leaf_below()),
            Some(_) => self.prev_node().map(|node| node.leaf().unwrap()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ::tests::*;

    #[test]
    fn leaf_traversal() {
        let tree: InfoTree<_> = (1..21).map(|i| TestLeaf(i)).collect();
        let mut cursor = CursorT::new(root_of(&tree));
        for i in 1..21 {
            assert_eq!(cursor.next_leaf(), Some(&TestLeaf(i)));
        }
        assert_eq!(cursor.next_leaf(), None);
        cursor.reset();
        for i in (1..21).rev() {
            assert_eq!(cursor.prev_leaf(), Some(&TestLeaf(i)));
        }
        assert_eq!(cursor.prev_leaf(), None);
    }

    #[test]
    fn path_extend() {
        let tree: InfoTree<_> = (1..21).map(|i| TestLeaf(i)).collect();
        let mut cursor = Cursor::<_, usize>::new(root_of(&tree));
        assert_eq!(*cursor.first_leaf_below(), TestLeaf(1));
        assert_eq!(cursor.path_info(), 0);
        cursor.reset();
        assert_eq!(*cursor.last_leaf_below(), TestLeaf(20));
        assert_eq!(cursor.path_info(), 19*20/2);
    }

    // FIXME need more tests
}
