use super::*;

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

    pub fn node(&mut self) -> Option<&mut Node<L>> {
        match self.root {
            Some(ref mut node) => Some(node),
            None => match self.steps.last_mut() {
                Some(cstep) => Some(&mut RC::make_mut(&mut cstep.nodes)[cstep.idx]),
                None => None,
            }
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
}
