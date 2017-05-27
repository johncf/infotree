use super::*;

use std::fmt;

pub struct Cursor<'a, L: Leaf + 'a> {
    root: &'a Node<L>,
    steps: CVec<CursorStep<'a, L>>,
    info_zero: L::Info,
}

#[derive(Clone)]
struct CursorStep<'a, L: Leaf + 'a> {
    nodes: &'a RC<NVec<Node<L>>>,
    idx: usize, // index at which cursor descended
    path_info: L::Info, // cumulative info from the root node
}

impl<'a, L> fmt::Debug for CursorStep<'a, L> where L: Leaf, L::Info: fmt::Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "CursorStep {{ nodes.len: {}, idx: {}, info: {:?} }}",
                  self.nodes.len(), self.idx, self.path_info)
    }
}

impl<'a, L: Leaf + 'a> Cursor<'a, L> {
    /// Create a new cursor from a root node. `info_zero` will be the starting value of info at the
    /// root. Info is cumulatively gathered along the path from root to the node being pointed to
    /// by the cursor. Therefore, `info_zero` should probably be the zero value of that type (the
    /// identity element of `Info::plus` operation).
    pub fn new(node: &Node<L>, info_zero: L::Info) -> Cursor<L> {
        Cursor {
            root: node,
            steps: CVec::new(),
            info_zero: info_zero,
        }
    }

    /// Returns the current node the cursor is pointing to.
    pub fn current(&self) -> &'a Node<L> {
        match self.steps.last() {
            Some(cstep) => &cstep.nodes[cstep.idx],
            None => self.root,
        }
    }

    /// Returns the cumulative info along the shortest path from root to the current node. This is
    /// an O(1) operation.
    ///
    /// Example 1: Cumulative info of the 4th node under root node is obtained by applying
    /// `Info::gather_down` to the infos of first 3 nodes in succession, starting with `info_zero`.
    ///
    /// Example 2: Cumulative info of the second node under the 4th node under root node is that of
    /// the 4th node (as in Example 1) `Info::gather_down`-ed with the first child node.
    pub fn path_info(&self) -> L::Info {
        match self.steps.last() {
            Some(cstep) => cstep.path_info,
            None => self.info_zero,
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
        self.descend_by(|_, _, i, _| i == idx)
    }

    /// Descend on the `idx`-th child from right. The last child is numbered `0`.
    pub fn descend_last(&mut self, idx: usize) -> Option<&'a Node<L>> {
        self.descend_by(|_, _, _, i| i == idx)
    }

    /// Descend the tree once, on the child for which `f` returns `true`.
    ///
    /// Returns `None` if `f` returned `false` on all children, or if it was a leaf node.
    ///
    /// The arguments to `f` are exactly the same as in [`Node::gather_traverse`].
    ///
    /// Panics if tree depth is greater than 8.
    ///
    /// [`Node::gather_traverse`]: ../enum.Node.html#method.gather_traverse
    pub fn descend_by<F>(&mut self, mut f: F) -> Option<&'a Node<L>>
        where F: FnMut(L::Info, L::Info, usize, usize) -> bool
    {
        let cur_node = self.current();
        let cur_info = self.path_info();
        let traverse_result = cur_node.gather_traverse(cur_info, |a, b, i, j| f(a, b, i, j));
        match traverse_result {
            Ok(TraverseSummary { child, info, index }) => {
                self.descend_raw(cur_node.children_raw(), index, info);
                Some(child)
            }
            Err(_) => None,
        }
    }

    fn descend_raw(&mut self, nodes: &'a RC<NVec<Node<L>>>, idx: usize, path_info: L::Info) {
        // ArrayVec::push(e) returns Some(e) on overflow!
        assert!(self.steps.push(CursorStep { nodes, idx, path_info }).is_none());
    }

    /// Make the cursor point to the next element at the same depth.
    ///
    /// If there is no next element, the cursor remains in the original position.
    pub fn next_node(&mut self) -> Option<&'a Node<L>> {
        let mut steps_clone = self.steps.clone();
        let mut depth_delta = 0;
        loop {
            match steps_clone.pop() {
                Some(CursorStep { nodes, mut idx, mut path_info }) => {
                    if idx + 1 < nodes.len() {
                        self.steps = steps_clone;
                        path_info = path_info.gather_down(nodes[idx].info());
                        idx += 1;
                        self.steps.push(CursorStep { nodes, idx, path_info });
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
    /// Per the current implementation, `next_node` is more efficient than `prev_node`.
    pub fn prev_node(&mut self) -> Option<&'a Node<L>> {
        let mut steps_clone = self.steps.clone();
        let mut depth_delta = 0;
        loop {
            match steps_clone.pop() {
                Some(CursorStep { nodes, mut idx, .. }) => {
                    if idx > 0 {
                        self.steps = steps_clone;
                        idx -= 1;
                        let mut path_info = self.path_info();
                        for node in &nodes[..idx] {
                            path_info = path_info.gather_down(node.info());
                        }
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
    fn basics() {
        let tree: InfoTree<_> = (1..21).map(|i| TestLeaf(i)).collect();
        let mut cursor = Cursor::new(root_of(&tree), 0);
        assert_eq!(*cursor.first_leaf_below(), TestLeaf(1));
        assert_eq!(cursor.path_info(), 0);
        cursor.reset();
        assert_eq!(*cursor.last_leaf_below(), TestLeaf(20));
        assert_eq!(cursor.path_info(), 19*20/2, "{:?}", cursor.steps);
    }

    #[test]
    fn leaf_traversal() {
        let tree: InfoTree<_> = (1..21).map(|i| TestLeaf(i)).collect();
        let mut cursor = Cursor::new(root_of(&tree), 0);
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
