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
    /// identity element of `Info::gather` operation).
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

    /// Descend the tree once, on the child for which `f` returns `true`. If `f` returned `false`
    /// on all children, descends on the last child.
    ///
    /// Panics if tree depth is greater than 8.
    pub fn descend<F>(&mut self, mut f: F) -> Result<(), ()>
        where F: FnMut(L::Info, L::Info) -> bool
    {
        let cur_node = self.node();
        let cur_info = self.info();
        match cur_node.traverse_with_default_end(cur_info, |i, j| f(i, j)) {
            Ok((idx, next_info)) => {
                if self.steps.push(CursorStep {
                                       nodes: cur_node.children_raw(),
                                       idx: idx,
                                       info: next_info,
                                   }).is_some() { // ArrayVec::push(e) returns Some(e) on overflow!
                    panic!("Depth greater than 8!")
                }
                Ok(())
            }
            Err(()) => Err(()),
        }
    }

    /// Recursively descend the tree while cumulatively gathering info, until either:
    /// - `f` returns `true` on a leaf node (current node is set to that leaf), or
    /// - `f` returns `false` on all leaf nodes (current node is set to the last leaf).
    ///
    /// Panics if tree depth is greater than 8.
    pub fn recursive_descend<F>(&mut self, mut f: F)
        where F: FnMut(L::Info, L::Info) -> bool
    {
        loop {
            match self.descend(|i, j| f(i, j)) {
                Ok(_) => {}
                Err(_) => return,
            }
        }
    }

    pub fn first_leaf_below(&mut self) -> &'a L {
        self.recursive_descend(|_, _| true);
        self.node().leaf().unwrap()
    }

    pub fn last_leaf_below(&mut self) -> &'a L {
        self.recursive_descend(|_, _| false);
        self.node().leaf().unwrap()
    }

    /// If the current node is a leaf, try to fetch the next leaf in order, otherwise it calls
    /// `first_leaf_below`.
    pub fn next_leaf(&mut self) -> Option<&'a L> {
        match self.node().leaf() {
            None => Some(self.first_leaf_below()),
            Some(_) => { // TODO
                unimplemented!()
            }
        }
    }

    /// If the current node is a leaf, try to fetch the next leaf in order, otherwise it calls
    /// `last_leaf_below`.
    pub fn prev_leaf(&mut self) -> Option<&'a L> {
        match self.node().leaf() {
            None => Some(self.last_leaf_below()),
            Some(_) => { // TODO
                unimplemented!()
            }
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

    // FIXME need more tests
}
