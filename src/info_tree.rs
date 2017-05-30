use super::*;
use std::iter::FromIterator;

/// A self-balancing copy-on-write tree. For testing purposes only.
#[derive(Clone)]
pub struct InfoTree<L: Leaf> {
    pub root: Option<Node<L>>,
}

impl<L: Leaf> InfoTree<L> {
    pub fn new() -> InfoTree<L> {
        InfoTree { root: None }
    }

    pub fn push_front(&mut self, leaf: L) {
        self.concat_first(Node::from_leaf(leaf));
    }

    pub fn push_back(&mut self, leaf: L) {
        self.concat_last(Node::from_leaf(leaf));
    }

    pub fn pop_front(&mut self) -> Option<L> {
        match self.root.take() {
            Some(root) => {
                let mut cm = CursorMutT::from_node(root);
                let res = cm.remove_first();
                self.root = cm.into_root();
                res
            },
            None => None,
        }
    }

    pub fn concat_last(&mut self, node: Node<L>) {
        let root = match self.root.take() {
            Some(root) => Node::concat(root, node),
            None => node,
        };
        self.root = Some(root);
    }

    pub fn concat_first(&mut self, node: Node<L>) {
        let root = match self.root.take() {
            Some(root) => Node::concat(node, root),
            None => node,
        };
        self.root = Some(root);
    }
}

impl<L: Leaf> From<Node<L>> for InfoTree<L> {
    fn from(node: Node<L>) -> InfoTree<L> {
        InfoTree { root: Some(node) }
    }
}

impl<L: Leaf> FromIterator<L> for InfoTree<L> {
    fn from_iter<I: IntoIterator<Item=L>>(iter: I) -> Self {
        let cursor_mut: CursorMutT<_> = iter.into_iter().collect();
        InfoTree {
            root: cursor_mut.into_root()
        }
    }
}
