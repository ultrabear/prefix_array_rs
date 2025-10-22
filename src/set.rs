//! A Set API based on a prefix array, this module contains the [`PrefixArraySet`] type.

#[cfg(any(test, feature = "std"))]
extern crate std;

extern crate alloc;

use alloc::{borrow::ToOwned, vec::Vec};
use core::{borrow::Borrow, fmt, ops::Deref};

mod iter;
pub use iter::{Drain, IntoIter, Iter};

use crate::shared::{PrefixBorrowed, PrefixOwned, ScratchSpace};

/// A generic search-by-prefix array designed to find strings with common prefixes in `O(log n)` time, and easily search on subslices to refine a previous search.
///
/// The generic parameter is mainly in place so that `&'a str`, `String`, and `&'static str` may all be used for the backing storage.
///  It is a logical error for an implementer of `AsRef<str>` to return different data across multiple calls while it remains in this container.
///  Doing so renders the datastructure useless (but will NOT cause UB).
///
/// The main downside of a [`PrefixArraySet`] over a trie type datastructure is that insertions have a significant `O(n)` cost,
/// so if you are adding multiple values over the lifetime of the [`PrefixArraySet`] it may become less efficient overall than a traditional tree.
#[derive(PartialEq, Eq)]
pub struct PrefixArraySet<K: Borrow<str>>(pub(crate) Vec<K>);

impl<K: Borrow<str> + fmt::Debug> fmt::Debug for PrefixArraySet<K> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "PrefixArraySet")?;
        f.debug_set().entries(self.iter()).finish()
    }
}

// Manually impl to get clone_from
impl<K: Borrow<str> + Clone> Clone for PrefixArraySet<K> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }

    fn clone_from(&mut self, other: &Self) {
        self.0.clone_from(&other.0);
    }
}

impl<K: Borrow<str>> Default for PrefixArraySet<K> {
    fn default() -> Self {
        PrefixArraySet::new()
    }
}

impl<K: Borrow<str>> PrefixArraySet<K> {
    /// Create a new empty [`PrefixArraySet`].
    ///
    /// This function will not allocate anything.
    #[must_use]
    pub const fn new() -> Self {
        Self(Vec::new())
    }

    /// Creates a new empty [`PrefixArraySet`] with space for at least `capacity` elements.
    ///
    /// See [`Vec::with_capacity`] for additional notes.
    ///
    /// # Panics:
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self(Vec::with_capacity(capacity))
    }

    /// Reserves capacity for at least `additional` more elements to be inserted, the collection may reserve additional space as a speculative optimization.
    /// Does nothing if capacity is already sufficient.
    ///
    /// See [`Vec::reserve`] for additional notes.
    ///
    /// # Panics:
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    pub fn reserve(&mut self, additional: usize) {
        self.0.reserve(additional);
    }

    /// Reserves the minimum capacity to append `additional` more elements. Or, will not speculatively over-allocate like [`reserve`][PrefixArraySet::reserve].
    /// Does nothing if capacity is already sufficient.
    ///
    /// See [`Vec::reserve_exact`] for additional notes.
    ///
    /// # Panics:
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    pub fn reserve_exact(&mut self, additional: usize) {
        self.0.reserve_exact(additional);
    }

    /// Creates a new [`PrefixArraySet`] from a `Vec<K>`, removing any duplicate keys.
    ///
    /// This operation is `O(n log n)`.
    #[must_use]
    pub fn from_vec_lossy(v: Vec<K>) -> Self {
        Self::from_vec_lossy_impl(v)
    }

    /// Inserts the given K into the [`PrefixArraySet`], returning true if the key was not already in the set
    ///
    /// This operation is `O(n)`.
    pub fn insert(&mut self, key: K) -> bool {
        self.insert_impl(key).is_none()
    }

    /// Adds a value to the set, replacing the existing value, if any, that is equal to the given one.  
    /// Returns the replaced value.
    pub fn replace(&mut self, key: K) -> Option<K> {
        self.insert_replace_impl(key)
    }

    /// Removes all values with the prefix provided, shifting the array in the process to account for the empty space.
    ///
    /// This operation is `O(n)`.
    ///
    /// # Examples
    /// ```rust
    /// # use prefix_array::PrefixArraySet;
    /// let mut set = PrefixArraySet::from_iter(["a", "b", "c"]);
    ///
    /// set.drain_all_with_prefix("b");
    ///
    /// assert_eq!(set.to_vec(), &["a", "c"]);
    /// ```
    pub fn drain_all_with_prefix<'a>(&'a mut self, prefix: &str) -> Drain<'a, K> {
        let range = self.find_all_with_prefix_idx_impl(prefix);

        Drain(self.0.drain(range))
    }

    /// Drains all elements of the [`PrefixArraySet`], returning them in an iterator.
    /// Keeps the backing allocation intact, unlike [`IntoIter`].
    ///
    /// When this iterator is dropped it drops all remaining elements.
    pub fn drain(&mut self) -> Drain<K> {
        Drain(self.0.drain(..))
    }

    /// Removes the value that matches the given key, returning true if it was present in the set
    ///
    /// This operation is `O(log n)` if the key was not found, and `O(n)` if it was.
    pub fn remove(&mut self, key: &str) -> bool {
        self.remove_entry_impl(key).is_some()
    }

    /// Returns the total capacity that the [`PrefixArraySet`] has.
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    /// Clears the [`PrefixArraySet`], removing all values.
    ///
    /// Capacity will not be freed.
    pub fn clear(&mut self) {
        self.0.clear();
    }

    /// Shrinks the capacity of this collection as much as possible.
    ///
    /// Additional capacity may still be left over after this operation.
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit();
    }

    /// Shrinks the capacity of this collection with a lower limit. It will drop down no lower than the supplied limit.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.0.shrink_to(min_capacity);
    }

    /// Extends the collection with items from an iterator, this is functionally equivalent to the
    /// `Extend` implementation and carries the same edge cases, but it allows passing a scratch
    /// space to potentially avoid reallocations when calling `extend_with` multiple times.
    pub fn extend_with<I>(&mut self, scratch: &mut ScratchSpace<Self>, iter: I)
    where
        I: IntoIterator<Item = K>,
    {
        self.extend_with_impl(&mut scratch.0, iter);
    }

    /// Makes a `PrefixArraySet` from an iterator in which all key items are unique
    fn from_unique_iter<T: IntoIterator<Item = K>>(v: T) -> Self {
        Self::from_unique_iter_impl(v)
    }
}

impl<K: Borrow<str>> Extend<K> for PrefixArraySet<K> {
    /// Extends the [`PrefixArraySet`] with more values, skipping updating any duplicates.
    ///
    /// It is currently unspecified if two identical values are given, who are not already in the set, which value will be kept.
    ///
    /// This operation is `O(n + k log k)` where k is the number of elements in the iterator.
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = K>,
    {
        self.extend_with(&mut ScratchSpace::new(), iter);
    }
}

#[cfg(feature = "std")]
impl<K: Borrow<str>, H> From<std::collections::HashSet<K, H>> for PrefixArraySet<K> {
    /// Performs a lossless conversion from a `HashSet<K>` to a `PrefixArraySet<K>` in `O(n log n)` time.
    fn from(v: std::collections::HashSet<K, H>) -> Self {
        Self::from_unique_iter(v)
    }
}

impl<K: Borrow<str>> From<alloc::collections::BTreeSet<K>> for PrefixArraySet<K> {
    /// Performs a lossless conversion from a `BTreeSet<K>` to a `PrefixArraySet<K>` in `O(n log n)` time.
    fn from(v: alloc::collections::BTreeSet<K>) -> Self {
        Self::from_unique_iter(v)
    }
}

impl<K: Borrow<str>> From<PrefixArraySet<K>> for Vec<K> {
    fn from(v: PrefixArraySet<K>) -> Vec<K> {
        v.0
    }
}

impl<K: Borrow<str>> Deref for PrefixArraySet<K> {
    type Target = SetSubSlice<K>;

    fn deref(&self) -> &Self::Target {
        SetSubSlice::cast_from_slice_core(&self.0)
    }
}

impl<K: Borrow<str>> core::borrow::Borrow<SetSubSlice<K>> for PrefixArraySet<K> {
    fn borrow(&self) -> &SetSubSlice<K> {
        self
    }
}

impl<K: Borrow<str> + Clone> ToOwned for SetSubSlice<K> {
    type Owned = PrefixArraySet<K>;

    fn to_owned(&self) -> PrefixArraySet<K> {
        // here we can assert the invariants were upheld
        PrefixArraySet(self.to_vec())
    }

    fn clone_into(&self, target: &mut PrefixArraySet<K>) {
        self.0.clone_into(&mut target.0);
    }
}

impl<K: Borrow<str> + fmt::Debug> fmt::Debug for SetSubSlice<K> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "SetSubSlice")?;
        f.debug_set().entries(self.iter()).finish()
    }
}

/// A subslice of a [`PrefixArraySet`] in which all items contain a common prefix (which may be the unit prefix `""`).
///
/// The [`SetSubSlice`] does not store what that common prefix is for performance reasons (but it can be computed, see: [`SetSubSlice::common_prefix`]), it is up to the user to keep track of.
// SAFETY: this type must remain repr(transparent) to [K] for cast_from_slice(_mut)_core invariants
#[repr(transparent)]
#[derive(PartialEq, Eq)]
pub struct SetSubSlice<K: Borrow<str>>(pub(crate) [K]);

impl<K: Borrow<str>> SetSubSlice<K> {
    /// creates a shared ref to Self from a ref to backing storage
    pub(crate) fn cast_from_slice_core(v: &[K]) -> &Self {
        // SAFETY: this type is repr(transparent), and the lifetimes are both &'a
        unsafe { &*(v as *const [K] as *const Self) }
    }

    /// creates an owned ref to Self from a ref to backing storage
    pub(crate) fn cast_from_slice_mut_core(v: &mut [K]) -> &mut Self {
        // SAFETY: this type is repr(transparent), and the lifetimes are both &'a
        unsafe { &mut *(v as *mut [K] as *mut Self) }
    }

    /// Returns an iterator over all of the elements of this [`SetSubSlice`]
    pub fn iter(&self) -> Iter<K> {
        Iter(self.0.iter())
    }

    /// Creates an owned copy of this [`SetSubSlice`] as a [`Vec`].
    /// If you wish to preserve [`PrefixArraySet`] semantics consider using [`ToOwned`] instead.
    pub fn to_vec(&self) -> Vec<K>
    where
        K: Clone,
    {
        self.0.to_vec()
    }

    /// Returns the `SetSubSlice` where all `K` have the same prefix `prefix`.
    ///
    /// Will return an empty array if there are no matches.
    ///
    /// This operation is `O(log n)`
    ///
    /// # Examples
    /// ```rust
    /// # use prefix_array::PrefixArraySet;
    /// let set = PrefixArraySet::from_iter(["foo", "bar", "baz"]);
    ///
    /// assert_eq!(set.find_all_with_prefix("b").to_vec(), vec!["bar", "baz"]);
    /// ```
    pub fn find_all_with_prefix<'a>(&'a self, prefix: &str) -> &'a Self {
        let range = self.find_all_with_prefix_idx_impl(prefix);
        self.reslice(range)
    }

    /// Compute the common prefix of this [`SetSubSlice`] from the data.
    /// Will return an empty string if this subslice is empty.
    ///
    /// Note that this may be more specific than what was searched for, i/e:
    /// ```rust
    /// # use prefix_array::PrefixArraySet;
    /// let arr = PrefixArraySet::from_iter(["12346", "12345", "12341"]);
    /// // Common prefix is *computed*, so even though we only
    /// //  searched for "12" we got something more specific
    /// assert_eq!(arr.find_all_with_prefix("12").common_prefix(), "1234");
    /// ```
    ///
    /// This operation is `O(1)`, but it is not computationally free.
    pub fn common_prefix(&self) -> &str {
        self.common_prefix_impl()
    }

    /// Returns whether this [`SetSubSlice`] contains the given key
    ///
    /// This operation is `O(log n)`.
    pub fn contains(&self, key: &str) -> bool {
        self.contains_key_impl(key)
    }

    /// Returns whether this [`SetSubSlice`] is empty
    pub const fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns the length of this [`SetSubSlice`]
    pub const fn len(&self) -> usize {
        self.0.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use alloc::vec;

    #[test]
    fn replace_replaces() {
        #[derive(Debug)]
        struct TrackerStr<'a>(&'a str, u64);

        impl core::borrow::Borrow<str> for TrackerStr<'_> {
            fn borrow(&self) -> &str {
                self.0
            }
        }

        let mut parray = PrefixArraySet::from_iter([TrackerStr("abc", 0)]);

        assert!(matches!(
            parray.replace(TrackerStr("abc", 1)),
            Some(TrackerStr("abc", 0))
        ));

        assert!(parray.contains("abc"));
    }

    #[test]
    fn submatches() {
        let parray = PrefixArraySet::from_vec_lossy(vec![
            "abcde", "234234", "among", "we", "weed", "who", "what", "why", "abde", "abch",
            "america",
        ]);

        assert_eq!(
            &["abcde", "abch", "abde"],
            &*parray.find_all_with_prefix("ab").to_vec()
        );

        assert_eq!("ab", parray.find_all_with_prefix("ab").common_prefix());

        let mut parraysingle = PrefixArraySet::from_vec_lossy(vec!["abcde"]);

        assert_eq!("abcde", parraysingle.to_vec()[0]);
        assert_eq!(
            &["abcde"],
            &*parraysingle.find_all_with_prefix("a").to_vec()
        );

        assert!(parraysingle.find_all_with_prefix("b").is_empty());

        _ = parraysingle.drain_all_with_prefix("a");

        assert!(parraysingle.is_empty());
    }

    #[test]
    fn is_eq() {
        let arr1 = PrefixArraySet::from_iter(["abcde", "among"]);
        let arr2 = PrefixArraySet::from_iter(["abcde", "among"]);

        assert_eq!(arr1, arr2);

        let arr3 = PrefixArraySet::new();

        assert_ne!(&*arr3, &*arr2);
    }
}
