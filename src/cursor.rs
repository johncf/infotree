use super::*;

// Maximum height of tree that can be handled by the cursor.
// => Maximum number of elements = MAX_CHILDREN^CURSOR_P2R_SIZE = 16^8 = 2^32
const CURSOR_MAX_HT: usize = 8;

type CVec<T> = ArrayVec<[T; CURSOR_MAX_HT]>;

struct CursorStep<'a, L: Leaf + 'a> {
    nodes: &'a Arc<NVec<Node<L>>>,
    idx: usize, // index at which cursor descended
}

pub struct Cursor<'a, L: Leaf + 'a> {
    root: &'a Node<L>,
    steps: CVec<CursorStep<'a, L>>,
}

impl<'a, L: Leaf + 'a> Cursor<'a, L> {
    pub fn new(node: &Node<L>) -> Cursor<L> {
        Cursor {
            root: node,
            steps: CVec::new(),
        }
    }

    pub fn current(&self) -> &Node<L> {
        match self.steps.last() {
            Some(cstep) => &cstep.nodes[cstep.idx],
            None => self.root,
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
    pub fn accu_recursive_descend<E, F>(&self, mut f: F) -> Result<L::Info, E>
        where F: FnMut(L::Info, L::Info) -> Result<bool, E>
    {
        unimplemented!()
    }
}

struct CursorMutStep<L: Leaf> {
    nodes: Arc<NVec<Node<L>>>,
    idx: usize,
}

pub struct CursorMut<L: Leaf> {
    root: Option<Node<L>>,
    steps: CVec<CursorMutStep<L>>,
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
    fn from(mut cur: CursorMut<L>) -> Node<L> {
        match cur.root {
            Some(node) => node,
            None => match cur.steps.pop() {
                Some(CursorMutStep { nodes, .. }) => {
                    let mut root = Node::from_nodes(nodes);
                    for CursorMutStep { mut nodes, idx } in cur.steps.into_iter().rev() {
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

