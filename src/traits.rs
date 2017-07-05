use std::cmp::Ordering;

/// The value stored in a leaf node should implement this trait.
///
/// Note: If cloning a leaf is expensive, consider wrapping it in `Arc`.
pub trait Leaf: Clone {
    type Info: Info;

    fn compute_info(&self) -> Self::Info;
}

/// Metadata that need to be gathered hierarchically over the tree.
pub trait Info: Copy {
    /// Used when gathering info from children to parent nodes. Should probably be commutative and
    /// associative.
    fn gather(self, other: Self) -> Self;
}

pub trait PathInfo<RHS=Self>: Copy where RHS: Info {
    /// Used when traversing down the tree for computing the cumulative info from root.
    fn extend(self, prev: RHS) -> Self;

    /// The inverse of `extend` operation. If the info gathered on a node is `x`, and `c0` is the
    /// cumulative path info to that node, then the following condition should hold:
    ///
    /// `c0.extend(x).extend_inv(x) == c0`
    fn extend_inv(self, curr: RHS) -> Self;

    /// The identity value of `extend` operation. I.e., the following condition should hold:
    ///
    /// `c0.extend(identity) == c0.extend_inv(identity) == c0`
    fn identity() -> Self;
}

/// Substructure ordering.
///
/// Useful for comparing a structure having multiple fields with another having a subset of those
/// fields. This trait should only be implemented by the substructure types. There's a default
/// implementation for the same type comparing itself.
///
/// The constrain for correctness is that the fields in substructure types should follow the same
/// priority rules when determining the ordering.
pub trait SubOrd<T> {
    fn sub_cmp(&self, rhs: &T) -> Ordering;
}

// == End of Trait Definitions ==

impl Info for () {
    #[inline]
    fn gather(self, _: ()) { }
}

impl Info for usize {
    #[inline]
    fn gather(self, other: usize) -> usize { self + other }
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

// Implement `SubOrd<T>` for all fully ordered `T`.
impl<T: Ord> SubOrd<T> for T {
    fn sub_cmp(&self, rhs: &T) -> Ordering {
        self.cmp(rhs)
    }
}
