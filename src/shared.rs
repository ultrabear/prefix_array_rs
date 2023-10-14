//! Shared implementations between [`PrefixArray`](super::PrefixArray) and
//! [`PrefixArraySet`](super::PrefixArraySet).
extern crate alloc;

use alloc::vec::Vec;

mod sealed {

    use core::borrow::Borrow;

    pub trait PrefixMapOrSet {
        type Item;
    }

    impl<K: Borrow<str>, V> PrefixMapOrSet for crate::PrefixArray<K, V> {
        type Item = (K, V);
    }

    impl<K: Borrow<str>> PrefixMapOrSet for crate::PrefixArraySet<K> {
        type Item = (K, ());
    }
}

use sealed::PrefixMapOrSet;

/// Scratch space for the `extend_with` methods on [`PrefixArray`](super::PrefixArray) and [`PrefixArraySet`](super::PrefixArraySet)
///
/// Using this scratch space allows you to potentially call extend multiple times without
/// allocating, as the default `Extend` method will allocate to avoid severe time penalties
pub struct ScratchSpace<T: PrefixMapOrSet>(pub(crate) Vec<(usize, T::Item)>);

impl<T: PrefixMapOrSet> ScratchSpace<T> {
    /// Creates a new empty scratch space
    ///
    /// # Examples
    /// ```rust
    /// # use prefix_array::{PrefixArraySet, shared::ScratchSpace};
    /// // equivalent to .extend(["foo", "bar"]) as we dont preallocate
    /// PrefixArraySet::new().extend_with(&mut ScratchSpace::new(), ["foo", "bar"]);
    /// ```
    #[must_use]
    pub const fn new() -> Self {
        Self(Vec::new())
    }

    /// Creates a scratch space with room to insert at least n elements before reallocating
    #[must_use]
    pub fn with_capacity(n: usize) -> Self {
        Self(Vec::with_capacity(n))
    }
}
