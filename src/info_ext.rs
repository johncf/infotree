use super::Info;

pub trait PathInfo<RHS=Self>: Copy where RHS: Info {
    /// Used when traversing down the tree for computing the cumulative info from root.
    fn extend(self, prev: RHS) -> Self;

    /// The inverse of `extend` operation. If the info gathered on a node is `x`, and `c0` is the
    /// cumulative path info to that node, then the following condition should hold:
    ///
    /// `c0.extend(x).extend_inv(x) == c0`
    fn extend_inv(self, curr: RHS) -> Self;

    /// The identity element of `extend` operation. I.e., the following condition should hold:
    ///
    /// `c0.extend(PathInfo::identity()) == c0`
    fn identity() -> Self;
}

impl<T> PathInfo<T> for () where T: Info {
    #[inline]
    fn extend(self, _: T) { }

    #[inline]
    fn extend_inv(self, _: T) { }

    #[inline]
    fn identity() { }
}

impl PathInfo for usize {
    #[inline]
    fn extend(self, other: usize) -> usize { self + other }

    #[inline]
    fn extend_inv(self, other: usize) -> usize { self - other }

    #[inline]
    fn identity() -> usize { 0 }
}
