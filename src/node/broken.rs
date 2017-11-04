use traits::Leaf;
use super::{Node, NodesPtr};

use arrayvec::ArrayVec;

pub enum BrokenNode<L: Leaf, NP: NodesPtr<L>> {
    Empty,
    Single(Node<L, NP>),
    Multi {
        children: ArrayVec<NP::Array>,
        height: usize,
    },
}

impl<L, NP> BrokenNode<L, NP> where L: Leaf, NP: NodesPtr<L> {
    pub fn new() -> Self {
        BrokenNode::Empty
    }

    fn multi_two(node1: Node<L, NP>, node2: Node<L, NP>) -> Self {
        let height = node1.height();
        debug_assert_eq!(height, node2.height());
        let mut children = ArrayVec::new();
        children.push(node1);
        children.push(node2);
        BrokenNode::Multi { children, height }
    }

    fn merge_two(node1: Node<L, NP>, node2: Node<L, NP>) -> Self {
        if node1.height() != node2.height() || !(node1.has_min_size() && node2.has_min_size()) {
            match Node::maybe_concat(node1, node2) {
                (node, None) => BrokenNode::Single(node),
                (node1, Some(node2)) => Self::multi_two(node1, node2),
            }
        } else {
            Self::multi_two(node1, node2)
        }
    }

    pub fn into_node(self) -> Node<L, NP> {
        match self {
            BrokenNode::Empty => panic!("Node cannot be empty!"),
            BrokenNode::Single(node) => node,
            BrokenNode::Multi { children, .. } => Node::from_children(NP::new(children)),
        }
    }

    pub fn is_empty(&self) -> bool {
        match *self {
            BrokenNode::Empty => true,
            _ => false,
        }
    }

    pub fn push_child(self, newnode: Node<L, NP>) -> Self {
        use self::BrokenNode::{Empty, Single, Multi};
        match self {
            Empty => Single(newnode),
            Single(child) => Self::merge_two(child, newnode),
            Multi { mut children, height } => {
                if height < newnode.height() {
                    debug_assert_eq!(children.len(), 2, "This must be a bug!");
                    let parent = Node::from_children(NP::new(children));
                    Self::merge_two(parent, newnode)
                } else if newnode.height() < height || !newnode.has_min_size() {
                    let last_child = children.pop().unwrap();
                    match Node::maybe_concat(last_child, newnode) {
                        (node, None) => children.push(node),
                        (node1, Some(node2)) => {
                            children.push(node1);
                            children.push(node2);
                        }
                    }
                    Multi { children, height }
                } else {
                    children.push(newnode);
                    Multi { children, height }
                }
            }
        }
    }
}
