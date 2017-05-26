use super::*;

use std::fmt;

pub struct Cursor<'a, L: Leaf + 'a> {
    root: &'a Node<L>,
    steps: CVec<CursorStep<'a, L>>,
}

#[derive(Clone)]
struct CursorStep<'a, L: Leaf + 'a> {
    nodes: &'a RC<NVec<Node<L>>>,
    idx: usize, // index at which cursor descended
    info: Option<L::Info>, // cumulative info from the root node
}

impl<'a, L> fmt::Debug for CursorStep<'a, L> where L: Leaf, L::Info: fmt::Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "CursorStep {{ nodes.len: {}, idx: {}, info: {:?} }}",
                  self.nodes.len(), self.idx, self.info)
    }
}

impl<'a, L: Leaf + 'a> Cursor<'a, L> {
    /// Create a new cursor from a root node. `info` is cumulatively gathered along the path from
    /// root to the node being pointed to by the cursor.
    pub fn new(node: &Node<L>) -> Cursor<L> {
        Cursor {
            root: node,
            steps: CVec::new(),
        }
    }

    /// Returns the current node the cursor is pointing to.
    pub fn node(&self) -> &'a Node<L> {
        match self.steps.last() {
            Some(cstep) => &cstep.nodes[cstep.idx],
            None => self.root,
        }
    }

    /// Returns the cumulative info along the shortest path from root to the current node.
    ///
    /// Example 1: Cumulative info of the 4th node under root node is obtained by `Info::gather_down`
    /// the infos of first 3 nodes.
    ///
    /// Example 2: Cumulative info of the second node under the 4th node under root node is that of
    /// the 4th node (as in Example 1) `Info::gather_down` with the first child node.
    pub fn path_info(&self) -> Option<L::Info> {
        match self.steps.last() {
            Some(cstep) => cstep.info,
            None => None,
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

    /// Descend the tree once, on the child for which `f` returns `true`.
    ///
    /// Returns `None` if `f` returned `false` on all children, or if it was a leaf node.
    ///
    /// Panics if tree depth is greater than 8.
    pub fn descend<F>(&mut self, mut f: F, reverse: bool) -> Option<&'a Node<L>>
        where F: FnMut(Option<L::Info>, L::Info) -> bool
    {
        let cur_node = self.node();
        let cur_info = self.path_info();
        let traverse_result = if reverse {
            cur_node.gather_traverse_rev(cur_info, |i, j| f(i, j))
        } else {
            cur_node.gather_traverse(cur_info, |i, j| f(i, j))
        };
        match traverse_result {
            Ok(TraverseSummary { child, info, index }) => {
                // ArrayVec::push(e) returns Some(e) on overflow!
                assert!(self.steps.push(CursorStep {
                                            nodes: cur_node.children_raw(),
                                            idx: index,
                                            info: info,
                                        }).is_none(), "Tree depth greater than 8!");
                Some(child)
            }
            Err(_) => None,
        }
    }

    /// Make the cursor point to the next element at the same depth.
    ///
    /// If there is no next element, the cursor remains in the original position.
    pub fn next_node(&mut self) -> Option<&'a Node<L>> {
        let mut steps_clone = self.steps.clone();
        let mut depth_delta = 0;
        loop {
            match steps_clone.pop() {
                Some(CursorStep { nodes, mut idx, mut info }) => {
                    if idx + 1 < nodes.len() {
                        self.steps = steps_clone;
                        info = Some(Info::gather_down(info, nodes[idx].info()));
                        idx += 1;
                        self.steps.push(CursorStep { nodes, idx, info });
                        while depth_delta > 0 {
                            // descend the left-most element
                            self.first_child().unwrap();
                            depth_delta -= 1;
                        }
                        return Some(self.node());
                    } else {
                        depth_delta += 1;
                    }
                }
                None => return None, // at the root
            }
        }
    }

    /// Make the cursor point to the previous element at the same depth.
    pub fn prev_node(&mut self) -> Option<&'a Node<L>> {
        let mut steps_clone = self.steps.clone();
        let mut depth_delta = 0;
        loop {
            match steps_clone.pop() {
                Some(CursorStep { nodes, mut idx, .. }) => {
                    if idx > 0 {
                        self.steps = steps_clone;
                        idx -= 1;
                        let mut info = self.path_info();
                        for node in &nodes[..idx] {
                            info = Some(Info::gather_down(info, node.info()));
                        }
                        self.steps.push(CursorStep { nodes, idx, info });
                        while depth_delta > 0 {
                            // descend the right-most element
                            self.last_child().unwrap();
                            depth_delta -= 1;
                        }
                        return Some(self.node());
                    } else {
                        depth_delta += 1;
                    }
                }
                None => return None, // at the root
            }
        }
    }

    pub fn first_child(&mut self) -> Option<&'a Node<L>> {
        self.descend(|_, _| true, false)
    }

    pub fn last_child(&mut self) -> Option<&'a Node<L>> {
        self.descend(|_, _| true, true)
    }

    pub fn first_leaf_below(&mut self) -> &'a L {
        while let Some(_) = self.first_child() {}
        self.node().leaf().unwrap()
    }

    pub fn last_leaf_below(&mut self) -> &'a L {
        while let Some(_) = self.last_child() {}
        self.node().leaf().unwrap()
    }

    /// If the current node is a leaf, try to fetch the next leaf in order, otherwise it calls
    /// `first_leaf_below`.
    pub fn next_leaf(&mut self) -> Option<&'a L> {
        match self.node().leaf() {
            None => Some(self.first_leaf_below()),
            Some(_) => self.next_node().map(|node| node.leaf().unwrap()),
        }
    }

    /// If the current node is a leaf, try to fetch the previous leaf in order, otherwise it calls
    /// `last_leaf_below`.
    pub fn prev_leaf(&mut self) -> Option<&'a L> {
        match self.node().leaf() {
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
        let mut cursor = Cursor::new(root_of(&tree));
        assert_eq!(*cursor.first_leaf_below(), TestLeaf(1));
        assert_eq!(cursor.path_info(), None);
        cursor.reset();
        assert_eq!(*cursor.last_leaf_below(), TestLeaf(20));
        assert_eq!(cursor.path_info(), Some(19*20/2), "{:?}", cursor.steps);
    }

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
