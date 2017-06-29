use base::Cursor;
use traits::Leaf;

/// A useful type alias for easy initialization of `Cursor`.
pub type CursorT<'a, L> = Cursor<'a, L, ()>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TestLeaf(pub usize);

impl Leaf for TestLeaf {
    type Info = usize;
    fn compute_info(&self) -> usize {
        self.0
    }
}

//#[test]
//fn print() {
//    use ::std::mem; use ::{CursorMut};
//    panic!("printed {}", mem::size_of::<CursorMut<TestLeaf, usize>>());
//}
