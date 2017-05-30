use super::*;
use std::iter::FromIterator;

/// A self-balancing copy-on-write tree data structure.
///
/// All major operations are defined in either the `Node` structure, and the cursor types.
///
/// See [`Node`](struct.InfoTree.html) for more details.
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
        let mut tree = InfoTree::new();
        let mut iter = iter.into_iter().map(|e| Node::from_leaf(e));

        loop {
            let nodes: NVec<_> = iter.by_ref().take(MAX_CHILDREN).collect();
            if nodes.len() > 0 {
                tree.concat_last(Node::from_children(RC::new(nodes)));
            } else {
                break;
            }
        }
        tree
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ::tests::*;

    #[test]
    fn basics() {
        let mut tree = InfoTree::new();
        tree.push_back(TestLeaf(1));
        assert_eq!(height_of(&tree), 0);
        assert_eq!(info_of(&tree), 1);
        tree.push_back(TestLeaf(2));
        assert_eq!(height_of(&tree), 1);
        assert_eq!(info_of(&tree), 3);
        for i in 3..17 {
            tree.push_back(TestLeaf(i));
        }
        assert_eq!(height_of(&tree), 1);
        assert_eq!(info_of(&tree), 8 * 17);
        tree.push_back(TestLeaf(17));
        assert_eq!(height_of(&tree), 2);
        assert_eq!(info_of(&tree), 9 * 17);
    }
}
