use super::Info;

mod cursor;
//mod cursor_mut;

pub use self::cursor::CursorExt;
//pub use self::cursor_mut::CursorMutExt;

pub trait InfoExt<RHS=Self>: Copy where RHS: Info {
    /// Used when traversing down the tree for computing the cumulative info from root.
    fn gather_down(self, prev: RHS) -> Self;

    /// Inverse of `gather_down`. If the info gathered on a nodes is `x`, and `c0` is the
    /// cumulative info till that node, then the following condition should hold:
    ///
    /// `c0 == c0.gather_down(x).gather_down_inv(x)`
    fn gather_down_inv(self, curr: RHS) -> Self;

    /// The identity element of `gather_up` operation. I.e., the following condition should hold:
    ///
    /// `x.gather_up(Info::identity()) == x`
    fn identity() -> Self;
}

impl<T> InfoExt<T> for () where T: Info {
    #[inline]
    fn gather_down(self, _: T) { }

    #[inline]
    fn gather_down_inv(self, _: T) { }

    #[inline]
    fn identity() { }
}

impl InfoExt for usize {
    #[inline]
    fn gather_down(self, other: usize) -> usize { self + other }

    #[inline]
    fn gather_down_inv(self, other: usize) -> usize { self - other }

    #[inline]
    fn identity() -> usize { 0 }
}
