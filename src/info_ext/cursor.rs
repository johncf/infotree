use ::*;
use ::cursor::CursorInner;

/// Extended version of `Cursor`.
pub struct CursorExt<'a, L> where L: Leaf + 'a, L::Info: InfoExt {
    inner: CursorInner<'a, L, L::Info>,
}

impl<'a, L> CursorExt<'a, L> where L: Leaf + 'a, L::Info: InfoExt {
    /// Create a new cursor from a root node.
    pub fn new(node: &Node<L>) -> CursorExt<L> {
        CursorExt {
            inner: CursorInner::new(node),
        }
    }

    pub fn current(&self) -> &'a Node<L> {
        self.inner.current()
    }

    /// Returns the cumulative info along the shortest path from root to the current node. This is
    /// an O(1) operation.
    ///
    /// Example 1: Cumulative info of the 4th node under root node is obtained by applying
    /// `Info::gather_down` to the infos of first 3 nodes in succession.
    ///
    /// Example 2: Cumulative info of the second node under the 4th node under root node is that of
    /// the 4th node (as in Example 1) `Info::gather_down`-ed with the first child node.
    pub fn path_info(&self) -> L::Info {
        self.inner._extra()
    }

    pub fn depth(&self) -> usize {
        self.inner.depth()
    }

    pub fn reset(&mut self) {
        self.inner.reset()
    }

    pub fn ascend(&mut self) -> Option<&'a Node<L>> {
        self.inner.ascend()
    }

    pub fn descend(&mut self, idx: usize) -> Option<&'a Node<L>> {
        self.inner.descend(idx)
    }

    pub fn descend_last(&mut self, idx: usize) -> Option<&'a Node<L>> {
        self.inner.descend_last(idx)
    }

    /// Traverse the current node conditioned on path info from root.
    ///
    /// Arguments to `f`:
    /// - cumulative info before this child
    /// - cumulative info after this child
    /// - position of child (zero-based from left)
    /// - remaining children = total - position - 1
    pub fn descend_by<F>(&mut self, mut f: F, reversed: bool) -> Option<&'a Node<L>>
        where F: FnMut(L::Info, L::Info, usize, usize) -> bool
    {
        self.inner._descend_by_ext(|c, a, i, j| f(c, c.gather_down(a), i, j), reversed)
    }

    pub fn next_node(&mut self) -> Option<&'a Node<L>> {
        self.inner.next_node()
    }

    pub fn prev_node(&mut self) -> Option<&'a Node<L>> {
        self.inner.prev_node()
    }

    pub fn first_leaf_below(&mut self) -> &'a L {
        self.inner.first_leaf_below()
    }

    pub fn last_leaf_below(&mut self) -> &'a L {
        self.inner.last_leaf_below()
    }

    pub fn next_leaf(&mut self) -> Option<&'a L> {
        self.inner.next_leaf()
    }

    pub fn prev_leaf(&mut self) -> Option<&'a L> {
        self.inner.prev_leaf()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ::tests::*;

    #[test]
    fn gather_down() {
        let tree: InfoTree<_> = (1..21).map(|i| TestLeaf(i)).collect();
        let mut cursor = CursorExt::new(root_of(&tree));
        assert_eq!(*cursor.first_leaf_below(), TestLeaf(1));
        assert_eq!(cursor.path_info(), 0);
        cursor.reset();
        assert_eq!(*cursor.last_leaf_below(), TestLeaf(20));
        assert_eq!(cursor.path_info(), 19*20/2);
    }

    // FIXME need more tests
}
