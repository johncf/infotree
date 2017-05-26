use super::*;

pub struct CursorMut<L: Leaf> {
    root: Option<Node<L>>,
    steps: CVec<CursorMutStep<L>>,
    info_zero: L::Info,
}

struct CursorMutStep<L: Leaf> {
    nodes: RC<NVec<Node<L>>>,
    idx: usize,
    info: L::Info,
}

impl<L: Leaf> CursorMut<L> {
    pub fn new(node: Node<L>, info_zero: L::Info) -> CursorMut<L> {
        CursorMut {
            root: Some(node),
            steps: CVec::new(),
            info_zero: info_zero,
        }
    }

    pub fn node(&mut self) -> Option<&mut Node<L>> {
        match self.root {
            Some(ref mut node) => Some(node),
            None => match self.steps.last_mut() {
                Some(cstep) => Some(&mut RC::make_mut(&mut cstep.nodes)[cstep.idx]),
                None => None,
            }
        }
    }

    /// Returns the cumulative info along the shortest path from root to the current node.
    ///
    /// See `Cursor` for detailed explanation.
    pub fn path_info(&self) -> L::Info {
        match self.steps.last() {
            Some(cstep) => cstep.info,
            None => self.info_zero,
        }
    }

    pub fn ascend(&mut self) -> Option<&mut Node<L>> {
        match self.root {
            Some(_) => None,
            None => match self.steps.pop() {
                Some(CursorMutStep { nodes, .. }) => {
                    let parent = Node::from_nodes(nodes);
                    if self.steps.len() > 0 {
                        self.node().map(|node| { *node = parent; node })
                    } else {
                        self.root = Some(parent);
                        self.root.as_mut()
                    }
                }
                None => None,
            }
        }
    }

    pub fn reset(&mut self) {
        while let Some(_) = self.ascend() {}
    }

    //for both insert operations, the cursor should point to the inserted node.
    //pub fn insert(&mut self) {}
    //pub fn insert_after(&mut self) {}

    //the cursor should point to the adjacent node (preferrably the right, with no change in position)
    //pub fn delete(&mut self) {}

    //split the tree into two trees; the current node and all leaves to its right should be
    //included in the second tree.
    //pub fn split(self) -> (Node<L>, Node<L>) {}
}
