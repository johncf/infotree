use std::cmp::Ordering;

/// Metadata that would be gathered hierarchically over the tree.
pub trait SumInfo: Copy {
    /// Used when summarizing info from children by parent nodes.
    ///
    /// This operation must be associative, but not necessarily commutative.
    fn gather(self, rhs: Self) -> Self;
}

/// The value stored in a leaf node should implement this trait.
///
/// Note: If cloning a leaf is expensive, consider wrapping it in `Arc`.
pub trait Leaf: Clone {
    type Info: SumInfo;

    fn compute_info(&self) -> Self::Info;

    /// If `self` and `right` can be merged into a single leaf, then merge it and return `None`,
    /// otherwise redistribute the values so that both `self` and `right` has minimum required
    /// size. Default behavior is to return `Some(right)`.
    ///
    /// If this method chooses to merge them into one, must satisfy the following condition:
    /// ```text
    /// new_self.info = old_self.info.gather(right.info)
    /// ```
    /// On the other hand, if it chooses to split, then both the modified `self` and the returned
    /// `Leaf` must have `has_min_size` to be true.
    fn merge_maybe_split(&mut self, right: Self) -> Option<Self> {
        Some(right)
    }

    /// Return whether the leaf has minimum required size. If false, the tree will try to merge it
    /// with an adjacent leaf using `merge_maybe_split`. Default behavior is to always return true.
    ///
    /// This should preferrably be a fast constant-time check.
    fn has_min_size(&self) -> bool {
        true
    }
}

pub trait PathInfo<Info>: Copy where Info: SumInfo {
    /// Used when traversing down the tree for computing the cumulative info from root.
    fn extend(self, prev: Info) -> Self;

    /// The inverse of `extend` operation. If the info gathered on a node is `x`, and `c0` is the
    /// cumulative path info to that node, then the following condition should hold:
    ///
    /// `c0.extend(x).extend_inv(x) == c0`
    fn extend_inv(self, curr: Info) -> Self;
}

/// Substructure ordering.
///
/// Useful for comparing a structure having multiple fields with another having a subset of those
/// fields. This trait should only be implemented by the substructure types. A default
/// implementation is provided for the types implementing `Ord` for comparing itself.
///
/// The constrain for correctness is that the fields in substructure types should follow the same
/// priority rules when determining the ordering.
pub trait SubOrd<T> {
    fn sub_cmp(&self, rhs: &T) -> Ordering;
}

impl<T> SubOrd<T> for T where T: Ord {
    fn sub_cmp(&self, rhs: &Self) -> Ordering {
        self.cmp(rhs)
    }
}

/// Superstructure ordering. (The mirror of `SubOrd`.)
///
/// This trait must not be directly implemented. A default implementation based on `SubOrd` is
/// provided and must not be overridden.
pub trait SupOrd<T> {
    fn sup_cmp(&self, rhs: &T) -> Ordering;
}

impl<T, U> SupOrd<U> for T where U: SubOrd<T> {
    fn sup_cmp(&self, rhs: &U) -> Ordering {
        match rhs.sub_cmp(self) {
            Ordering::Less => Ordering::Greater,
            Ordering::Equal => Ordering::Equal,
            Ordering::Greater => Ordering::Less,
        }
    }
}

// == End of Trait Definitions ==

impl SumInfo for () {
    #[inline]
    fn gather(self, _: ()) { }
}

impl SumInfo for usize {
    #[inline]
    fn gather(self, other: usize) -> usize { self + other }
}

impl<T: SumInfo> PathInfo<T> for () {
    #[inline]
    fn extend(self, _: T) { }

    #[inline]
    fn extend_inv(self, _: T) { }
}

impl PathInfo<usize> for usize {
    #[inline]
    fn extend(self, other: usize) -> usize { self + other }

    #[inline]
    fn extend_inv(self, other: usize) -> usize { self - other }
}
