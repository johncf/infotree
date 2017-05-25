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
    nodes: &'a Arc<NVec<Node<L>>>,
    idx: usize, // index at which cursor descended
    info: L::Info, // accumulated info until current node
}

impl<'a, L> fmt::Debug for CursorStep<'a, L> where L: Leaf, L::Info: fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "CursorStep {{ nodes.len: {}, idx: {}, info: {} }}", self.nodes.len(), self.idx, self.info)
    }
}

impl<'a, L: Leaf + 'a> Cursor<'a, L> {
    /// Create a new cursor from a root node. `info_zero` will be the starting value of info when
    /// accumulating it while traversing the tree. It should probably be the zero value of that
    /// type (the identity element for the accumulate operation).
    pub fn new(node: &Node<L>, info_zero: L::Info) -> Cursor<L> {
        Cursor {
            root: node,
            steps: CVec::new(),
            info_zero: info_zero,
        }
    }

    /// Get the current node the cursor is pointing to.
    pub fn node(&self) -> &'a Node<L> {
        match self.steps.last() {
            Some(cstep) => &cstep.nodes[cstep.idx],
            None => self.root,
        }
    }

    /// Get the accumulated info for the current node.
    pub fn info(&self) -> &L::Info {
        match self.steps.last() {
            Some(cstep) => &cstep.info,
            None => &self.info_zero,
        }
    }

    /// The depth (distance from the root) at which the cursor is currently at.
    pub fn depth(&self) -> usize {
        self.steps.len()
    }

    /// Recursively descend the tree while accumulating info. It descends the child on which `f`
    /// returned `Ok(true)`, keeps iterating the current node as long as `f` returns `Ok(false)`,
    /// and descends the last child if `f` returned `Ok(false)` for all children.
    ///
    /// Descent stops when either:
    /// - `f` returns `Ok(true)` on a leaf node (current node is set to that leaf), or
    /// - `f` returned `Ok(false)` on all leaf nodes (current node is set to the last leaf), or
    /// - `f` returns `Err(E)` in which case, the function bubbles it up (current node remains to
    ///   be the parent node of the node on which `f` returned `Err(E)`).
    ///
    /// Returns `Ok(info)` where `info` is the accumulated info at the end of descent.
    pub fn recursive_descend<F, E>(&mut self, mut f: F) -> Result<(), E>
        where F: FnMut(L::Info, L::Info) -> Result<bool, E>
    {
        loop {
            let cur_info = self.info().clone();
            let cur_node: &'a Node<L> = self.node();
            if cur_node.is_leaf() { return Ok(()); }
            match cur_node.accu_info_with_default_end(cur_info, &mut f) {
                Ok((idx, next_info)) => {
                    // ArrayVec::push(e) returns Some(e) on overflow!
                    if self.steps.push(CursorStep {
                                           nodes: cur_node.children_raw(),
                                           idx: idx,
                                           info: next_info,
                                       }).is_some() {
                        panic!("Depth greater than 8!") // likely to OOM before this happens
                    }
                }
                Err(e) => return Err(e),
            }
        }
    }

    pub fn first_leaf_below(&mut self) -> &'a L {
        self.recursive_descend::<_, ()>(|_, _| Ok(true)).unwrap();
        self.node().leaf().unwrap()
    }

    pub fn last_leaf_below(&mut self) -> &'a L {
        self.recursive_descend::<_, ()>(|_, _| Ok(false)).unwrap();
        self.node().leaf().unwrap()
    }

    pub fn reset(&mut self) {
        self.steps.clear();
    }
}

pub struct CursorMut<L: Leaf> {
    root: Option<Node<L>>,
    steps: CVec<CursorMutStep<L>>,
}

struct CursorMutStep<L: Leaf> {
    nodes: Arc<NVec<Node<L>>>,
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
                Some(cstep) => Arc::make_mut(&mut cstep.nodes)[cstep.idx].leaf_mut(),
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
                        Arc::make_mut(&mut nodes)[idx] = root;
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
        assert_eq!(*cursor.info(), 0);
        cursor.reset();
        assert_eq!(*cursor.last_leaf_below(), TestLeaf(20));
        assert_eq!(*cursor.info(), 19*20/2, "{:?}", cursor.steps);
    }

    // FIXME need more tests
}
