use traits::Leaf;
use super::Node;

use arrayvec::{Array, ArrayVec};

use std::sync::Arc;
use std::rc::Rc;
use std::ops::Deref;

pub trait NodesPtr<L: Leaf>: Clone + Deref<Target=[Node<L, Self>]> {
    type Array: Array<Item=Node<L, Self>>;

    fn new(nodes: ArrayVec<Self::Array>) -> Self;
    fn make_mut(this: &mut Self) -> &mut ArrayVec<Self::Array>;

    fn max_size() -> usize {
        <Self::Array as Array>::capacity()
    }

    fn min_size() -> usize {
        Self::max_size()/2
    }
}

def_nodes_ptr_rc!(Arc16, Arc, 16);
def_nodes_ptr_rc!(Rc16, Rc, 16);
def_nodes_ptr_box!(Box16, 16);
