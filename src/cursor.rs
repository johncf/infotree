use super::*;
use std::fmt;

/// A useful type alias for easy initialization of `CursorInner`.
///
/// Use `Cursor::new()` instead of `CursorInner::new()` since the latter would need annotations.
pub type Cursor<'a, L> = CursorInner<'a, L, ()>;

/// An object that can be used to traverse a `Node`.
///
/// `CursorInner` is very lightweight. All operations are done entirely using stack memory -- no
/// heap allocations are made at any point.
pub struct CursorInner<'a, L: Leaf + 'a, I> {
    root: &'a Node<L>,
    steps: CVec<CursorStep<'a, L, I>>,
}

#[derive(Clone)]
struct CursorStep<'a, L: Leaf + 'a, I> {
    nodes: &'a RC<NVec<Node<L>>>,
    idx: usize, // index at which cursor descended
    extra: I,
}

impl<'a, L, I> fmt::Debug for CursorStep<'a, L, I> where L: Leaf + 'a, I: InfoExt<L::Info> + fmt::Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "CursorStep {{ nodes.len: {}, idx: {}, extra: {:?} }}",
                  self.nodes.len(), self.idx, self.extra)
    }
}

impl<'a, L, I> CursorInner<'a, L, I> where L: Leaf + 'a, I: InfoExt<L::Info> {
    /// Create a new cursor from a root node.
    pub fn new(node: &Node<L>) -> CursorInner<L, I> {
        CursorInner {
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

    #[doc(hidden)]
    pub fn _extra(&self) -> I {
        match self.steps.last() {
            Some(cstep) => cstep.extra,
            None => I::identity(),
        }
    }

    /// The depth (distance from the root) at which the cursor is currently at.
    pub fn depth(&self) -> usize {
        self.steps.len()
    }

    pub fn reset(&mut self) {
        self.steps.clear();
    }

    pub fn ascend(&mut self) -> Option<&'a Node<L>> {
        self.steps.pop().map(|cstep| &cstep.nodes[cstep.idx])
    }

    /// Descend on the `idx`-th child from left. The first child is numbered `0`.
    pub fn descend(&mut self, idx: usize) -> Option<&'a Node<L>> {
        self._descend_by_ext(|_, _, i, _| i == idx, false)
    }

    /// Descend on the `idx`-th child from right. The last child is numbered `0`.
    pub fn descend_last(&mut self, idx: usize) -> Option<&'a Node<L>> {
        self._descend_by_ext(|_, _, _, i| i == idx, true)
    }

    /// Descend the tree once, on the child for which `f` returns `true`.
    ///
    /// Returns `None` if `f` returned `false` on all children, or if it was a leaf node.
    ///
    /// The arguments to `f` are exactly the same as in [`Node::traverse`].
    ///
    /// Panics if tree depth is greater than 8.
    ///
    /// [`Node::traverse`]: ../enum.Node.html#method.traverse
    pub fn descend_by<F>(&mut self, mut f: F, reversed: bool) -> Option<&'a Node<L>>
        where F: FnMut(L::Info, usize, usize) -> bool
    {
        self._descend_by_ext(|_, a, i, j| f(a, i, j), reversed)
    }

    // This function is crucial to avoid WET-ting in `CursorExt`.
    #[doc(hidden)]
    pub fn _descend_by_ext<F>(&mut self, mut f: F, reversed: bool) -> Option<&'a Node<L>>
        where F: FnMut(I, L::Info, usize, usize) -> bool
    {
        let cur_node = self.current();
        let mut extra = self._extra();
        let res = if reversed {
            extra = extra.gather_down(cur_node.info());
            cur_node.traverse_rev(|node_info, pos, rem| {
                extra = extra.gather_down_inv(node_info);
                let ret = f(extra, node_info, pos, rem);
                ret
            })
        } else {
            cur_node.traverse(|node_info, pos, rem| {
                match f(extra, node_info, pos, rem) {
                    true => true,
                    false => { extra = extra.gather_down(node_info); false }
                }
            })
        };
        match res {
            Ok((child, index)) => {
                self.descend_raw(cur_node.children_raw(), index, extra);
                Some(child)
            }
            Err(_) => None,
        }
    }

    fn descend_raw(&mut self, nodes: &'a RC<NVec<Node<L>>>, idx: usize, extra: I) {
        // ArrayVec::push(e) returns Some(e) on overflow!
        assert!(self.steps.push(CursorStep { nodes, idx, extra }).is_none());
    }

    /// Make the cursor point to the next element at the same depth.
    ///
    /// If there is no next element, the cursor remains in the original position.
    pub fn next_node(&mut self) -> Option<&'a Node<L>> {
        let mut steps_clone = self.steps.clone();
        let mut depth_delta = 0;
        loop {
            match steps_clone.pop() {
                Some(CursorStep { nodes, mut idx, mut extra }) => {
                    if idx + 1 < nodes.len() {
                        self.steps = steps_clone;
                        extra = extra.gather_down(nodes[idx].info());
                        idx += 1;
                        self.steps.push(CursorStep { nodes, idx, extra });
                        while depth_delta > 0 {
                            // descend the left-most element
                            self.descend(0).unwrap();
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

    /// Make the cursor point to the previous element at the same depth.
    ///
    /// If there is no previous element, the cursor remains in the original position.
    pub fn prev_node(&mut self) -> Option<&'a Node<L>> {
        let mut steps_clone = self.steps.clone();
        let mut depth_delta = 0;
        loop {
            match steps_clone.pop() {
                Some(CursorStep { nodes, mut idx, mut extra }) => {
                    if idx > 0 {
                        self.steps = steps_clone;
                        idx -= 1;
                        extra = extra.gather_down_inv(nodes[idx].info());
                        self.steps.push(CursorStep { nodes, idx, extra });
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
        while let Some(_) = self.descend(0) {}
        self.current().leaf().unwrap()
    }

    pub fn last_leaf_below(&mut self) -> &'a L {
        while let Some(_) = self.descend_last(0) {}
        self.current().leaf().unwrap()
    }

    /// If the current node is a leaf, try to fetch the next leaf in order, otherwise it calls
    /// `first_leaf_below`.
    pub fn next_leaf(&mut self) -> Option<&'a L> {
        match self.current().leaf() {
            None => Some(self.first_leaf_below()),
            Some(_) => self.next_node().map(|node| node.leaf().unwrap()),
        }
    }

    /// If the current node is a leaf, try to fetch the previous leaf in order, otherwise it calls
    /// `last_leaf_below`.
    ///
    /// Per the current implementation, `next_leaf` is more efficient than `prev_leaf`.
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
    use super::super::tests::*;

    #[test]
    fn leaf_traversal() {
        let tree: InfoTree<_> = (1..21).map(|i| TestLeaf(i)).collect();
        let mut cursor = Cursor::new(root_of(&tree));
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

    // FIXME need more tests
}
