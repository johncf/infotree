use super::*;

use std::fmt;

// Maximum height of tree that can be handled by the cursor.
// => Maximum number of elements = MAX_CHILDREN^CURSOR_P2R_SIZE = 16^8 = 2^32
const CURSOR_MAX_HT: usize = 8;

type CVec<T> = ArrayVec<[T; CURSOR_MAX_HT]>;

pub struct Cursor<'a, L: Leaf + 'a> {
    root: &'a Node<L>,
    steps: CVec<CursorStep<'a, L>>,
    info_zero: L::Info,
}

#[derive(Clone)]
struct CursorStep<'a, L: Leaf + 'a> {
    nodes: &'a RC<NVec<Node<L>>>,
    idx: usize, // index at which cursor descended
    info: L::Info, // cumulative info from the root node
}

impl<'a, L> fmt::Debug for CursorStep<'a, L> where L: Leaf, L::Info: fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "CursorStep {{ nodes.len: {}, idx: {}, info: {} }}", self.nodes.len(), self.idx, self.info)
    }
}

impl<'a, L: Leaf + 'a> Cursor<'a, L> {
    /// Create a new cursor from a root node. `info_zero` will be the starting value of info at the
    /// root. `info` is cumulatively gathered along the path to root for the node being pointed to
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
    pub fn node(&self) -> &'a Node<L> {
        match self.steps.last() {
            Some(cstep) => &cstep.nodes[cstep.idx],
            None => self.root,
        }
    }

    /// Returns the cumulative info (from the root) for the current node.
    pub fn info(&self) -> L::Info {
        match self.steps.last() {
            Some(cstep) => cstep.info,
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

    pub fn ascend(&mut self) -> Result<(), ()> {
        match self.steps.pop() {
            Some(_) => Ok(()),
            None => Err(()),
        }
    }

    /// Descend the tree once, on the child for which `f` returns `true`.
    ///
    /// Returns `None` if `f` returned `false` on all children, or if it was a leaf node.
    ///
    /// Panics if tree depth is greater than 8.
    pub fn descend<F>(&mut self, mut f: F, reverse: bool) -> Option<&'a Node<L>>
        where F: FnMut(L::Info, L::Info) -> bool
    {
        let cur_node = self.node();
        let cur_info = self.info();
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
                        info = info.plus(nodes[idx].info());
                        idx += 1;
                        steps_clone.push(CursorStep { nodes, idx, info });
                        self.steps = steps_clone;
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
                Some(CursorStep { nodes, mut idx, mut info }) => {
                    if idx > 0 {
                        idx -= 1;
                        info = info.minus(nodes[idx].info());
                        steps_clone.push(CursorStep { nodes, idx, info });
                        self.steps = steps_clone;
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

pub struct CursorMut<L: Leaf> {
    root: Option<Node<L>>,
    steps: CVec<CursorMutStep<L>>,
}

struct CursorMutStep<L: Leaf> {
    nodes: RC<NVec<Node<L>>>,
    idx: usize,
}

impl<L: Leaf> CursorMut<L> {
    pub fn new(node: Node<L>) -> CursorMut<L> {
        CursorMut {
            root: Some(node),
            steps: CVec::new(),
        }
    }

    pub fn current(&self) -> &Node<L> {
        match self.root {
            Some(ref node) => node,
            None => match self.steps.last() {
                Some(cstep) => &cstep.nodes[cstep.idx],
                None => unreachable!("Bad CursorMut"),
            }
        }
    }

    pub fn leaf_mut(&mut self) -> Option<LeafMut<L>> {
        match self.root {
            Some(ref mut node) => node.leaf_mut(),
            None => match self.steps.last_mut() {
                Some(cstep) => RC::make_mut(&mut cstep.nodes)[cstep.idx].leaf_mut(),
                None => unreachable!("Bad CursorMut"),
            }
        }
    }
}

impl<L: Leaf> From<CursorMut<L>> for Node<L> {
    fn from(mut cursor: CursorMut<L>) -> Node<L> {
        match cursor.root {
            Some(node) => node,
            None => match cursor.steps.pop() {
                Some(CursorMutStep { nodes, .. }) => {
                    let mut root = Node::from_nodes(nodes);
                    for CursorMutStep { mut nodes, idx } in cursor.steps.into_iter().rev() {
                        RC::make_mut(&mut nodes)[idx] = root;
                        root = Node::from_nodes(nodes)
                    }
                    root
                }
                None => unreachable!("Bad CursorMut"),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::tests::*;

    #[test]
    fn basics() {
        let mut tree = UniTree::new();
        for i in 1..21 {
            tree.push_back(Node::from_leaf(TestLeaf(i)));
        }
        let mut cursor = Cursor::new(root_of(&tree), 0);
        assert_eq!(*cursor.first_leaf_below(), TestLeaf(1));
        assert_eq!(cursor.info(), 0);
        cursor.reset();
        assert_eq!(*cursor.last_leaf_below(), TestLeaf(20));
        assert_eq!(cursor.info(), 19*20/2, "{:?}", cursor.steps);
    }

    #[test]
    fn leaf_traversal() {
        let mut tree = UniTree::new();
        for i in 1..21 {
            tree.push_back(Node::from_leaf(TestLeaf(i)));
        }
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
