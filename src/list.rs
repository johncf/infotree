use traits::Leaf;

#[derive(Clone)]
struct ListLeaf<T: Clone>(T);

impl<T: Clone> Leaf for ListLeaf<T> {
    type Info = usize;
    fn compute_info(&self) -> usize { 1 }
}
