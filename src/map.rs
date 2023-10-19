//! A Map API based on a prefix array, this module contains the [`PrefixArray`] type.

#[cfg(any(test, feature = "std"))]
extern crate std;

extern crate alloc;

use alloc::{borrow::ToOwned, vec::Vec};
use core::{
    borrow::Borrow,
    fmt,
    ops::{Deref, DerefMut},
};

mod iter;
pub use iter::{Drain, IntoIter, Iter, IterMut};

use crate::shared::{PrefixBorrowed, PrefixOwned, ScratchSpace};

/// A generic search-by-prefix array designed to find strings with common prefixes in `O(log n)` time, and easily search on subslices to refine a previous search.
///
/// The generic parameter is mainly in place so that `&'a str`, `String`, and `&'static str` may all be used for the backing storage.
///  It is a logical error for an implementer of `AsRef<str>` to return different data across multiple calls while it remains in this container.
///  Doing so renders the datastructure useless (but will NOT cause UB).
///
/// The main downside of a [`PrefixArray`] over a trie type datastructure is that insertions have a significant `O(n)` cost,
/// so if you are adding multiple values over the lifetime of the [`PrefixArray`] it may become less efficient overall than a traditional tree.
#[derive(PartialEq, Eq)]
pub struct PrefixArray<K: Borrow<str>, V>(pub(crate) Vec<(K, V)>);

impl<K: Borrow<str> + fmt::Debug, V: fmt::Debug> fmt::Debug for PrefixArray<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "PrefixArray")?;
        f.debug_map().entries(self.iter()).finish()
    }
}

// Manually impl to get clone_from
impl<K: Borrow<str> + Clone, V: Clone> Clone for PrefixArray<K, V> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }

    fn clone_from(&mut self, other: &Self) {
        self.0.clone_from(&other.0);
    }
}

impl<K: Borrow<str>, V> Default for PrefixArray<K, V> {
    fn default() -> Self {
        PrefixArray::new()
    }
}

impl<K: Borrow<str>, V> PrefixArray<K, V> {
    /// Create a new empty [`PrefixArray`].
    ///
    /// This function will not allocate anything.
    #[must_use]
    pub const fn new() -> Self {
        Self(Vec::new())
    }

    /// Creates a new empty [`PrefixArray`] with space for at least `capacity` elements.
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

    /// Reserves the minimum capacity to append `additional` more elements. Or, will not speculatively over-allocate like [`reserve`][PrefixArray::reserve].
    /// Does nothing if capacity is already sufficient.
    ///
    /// See [`Vec::reserve_exact`] for additional notes.
    ///
    /// # Panics:
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    pub fn reserve_exact(&mut self, additional: usize) {
        self.0.reserve_exact(additional);
    }

    /// Creates a new [`PrefixArray`] from a `Vec<(K, V)>`, removing any duplicate keys.
    ///
    /// This operation is `O(n log n)`.
    #[must_use]
    pub fn from_vec_lossy(v: Vec<(K, V)>) -> Self {
        Self::from_vec_lossy_impl(v)
    }

    /// Inserts the given K/V pair into the [`PrefixArray`], returning the old V if one was present for this K.
    ///
    /// This will not update the K in the map if one was already present.
    ///
    /// This operation is `O(n)`.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.insert_impl((key, value))
    }

    /// Removes all values with the prefix provided, shifting the array in the process to account for the empty space.
    ///
    /// This operation is `O(n)`.
    pub fn drain_all_with_prefix<'a>(&'a mut self, prefix: &str) -> Drain<'a, K, V> {
        let range = self.find_all_with_prefix_idx(prefix);

        Drain(self.0.drain(range))
    }

    /// Drains all elements of the [`PrefixArray`], returning them in an iterator.
    /// Keeps the backing allocation intact, unlike [`IntoIter`].
    ///
    /// When this iterator is dropped it drops all remaining elements.
    pub fn drain(&mut self) -> Drain<K, V> {
        Drain(self.0.drain(..))
    }

    /// Removes the value that matches the given key and returns it,
    /// returns None if there was no value matching the key.
    ///
    /// This operation is `O(log n)` if the key was not found, and `O(n)` if it was.
    pub fn remove(&mut self, key: &str) -> Option<V> {
        self.remove_entry(key).map(|(_, v)| v)
    }

    /// Removes the value that matches the given key and returns it and the key,
    /// returns None if there was no value matching the key.
    ///
    /// This operation is `O(log n)` if the key was not found, and `O(n)` if it was.
    pub fn remove_entry(&mut self, key: &str) -> Option<(K, V)> {
        self.remove_entry_impl(key)
    }

    /// Returns the total capacity that the [`PrefixArray`] has.
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    /// Clears the [`PrefixArray`], removing all values.
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

    /// Inner method of `extend_with` that allows passing [`PrefixArraySet`](super::PrefixArraySet)
    /// values in.
    pub(crate) fn extend_with_raw<I>(&mut self, insert: &mut Vec<(usize, (K, V))>, iter: I)
    where
        I: IntoIterator<Item = (K, V)>,
    {
        self.extend_with_impl(insert, iter);
    }

    /// Extends the collection with items from an iterator, this is functionally equivalent to the
    /// `Extend` implementation and carries the same edge cases, but it allows passing a scratch
    /// space to potentially avoid reallocations when calling `extend_with` multiple times.
    pub fn extend_with<I>(&mut self, scratch: &mut ScratchSpace<Self>, iter: I)
    where
        I: IntoIterator<Item = (K, V)>,
    {
        self.extend_with_raw(&mut scratch.0, iter);
    }

    /// Makes a `PrefixArray` from an iterator in which all key items are unique
    pub(crate) fn from_unique_iter<T: IntoIterator<Item = (K, V)>>(v: T) -> Self {
        Self::from_unique_iter_impl(v)
    }
}

impl<K: Borrow<str>, V> Extend<(K, V)> for PrefixArray<K, V> {
    /// Extends the [`PrefixArray`] with more values, overwriting any duplicate key's values in the map (will not update the key).
    ///
    /// It is currently unspecified if two identical keys are given, who are not already in the set, which K/V pair will be kept.
    ///
    /// This operation is `O(n + k log k)` where k is the number of elements in the iterator.
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = (K, V)>,
    {
        self.extend_with(&mut ScratchSpace::new(), iter);
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl<K: Borrow<str>, V, H> From<std::collections::HashMap<K, V, H>> for PrefixArray<K, V> {
    /// Performs a lossless conversion from a `HashMap<K, V>` to a `PrefixArray<K, V>` in `O(n log n)` time.
    fn from(v: std::collections::HashMap<K, V, H>) -> Self {
        Self::from_unique_iter(v)
    }
}

impl<K: Borrow<str>, V> From<alloc::collections::BTreeMap<K, V>> for PrefixArray<K, V> {
    /// Performs a lossless conversion from a `BTreeMap<K, V>` to a `PrefixArray<K, V>` in `O(n log n)` time.
    fn from(v: alloc::collections::BTreeMap<K, V>) -> Self {
        Self::from_unique_iter(v)
    }
}

impl<K: Borrow<str>, V> From<PrefixArray<K, V>> for Vec<(K, V)> {
    fn from(v: PrefixArray<K, V>) -> Vec<(K, V)> {
        v.0
    }
}

impl<K: Borrow<str>, V> Deref for PrefixArray<K, V> {
    type Target = SubSlice<K, V>;

    fn deref(&self) -> &Self::Target {
        SubSlice::cast_from_slice(self.0.as_slice())
    }
}

impl<K: Borrow<str>, V> DerefMut for PrefixArray<K, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        SubSlice::cast_from_slice_mut(self.0.as_mut_slice())
    }
}

impl<K: Borrow<str>, V> core::borrow::Borrow<SubSlice<K, V>> for PrefixArray<K, V> {
    fn borrow(&self) -> &SubSlice<K, V> {
        self
    }
}

impl<K: Borrow<str>, V> core::borrow::BorrowMut<SubSlice<K, V>> for PrefixArray<K, V> {
    fn borrow_mut(&mut self) -> &mut SubSlice<K, V> {
        self
    }
}

impl<K: Borrow<str> + Clone, V: Clone> ToOwned for SubSlice<K, V> {
    type Owned = PrefixArray<K, V>;

    fn to_owned(&self) -> PrefixArray<K, V> {
        // here we can assert the invariants were upheld
        PrefixArray(self.to_vec())
    }

    fn clone_into(&self, target: &mut PrefixArray<K, V>) {
        self.0.clone_into(&mut target.0);
    }
}

impl<K: Borrow<str> + fmt::Debug, V: fmt::Debug> fmt::Debug for SubSlice<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "SubSlice")?;
        f.debug_map().entries(self.iter()).finish()
    }
}

/// A [`SubSlice`] of a [`PrefixArray`] in which all items contain a common prefix (which may be the unit prefix `""`).
///
/// The [`SubSlice`] does not store what that common prefix is for performance reasons, it is up to the user to keep track of.
// SAFETY: this type must remain repr(transparent) to [(K, V)] for from_slice(_mut) invariants
#[repr(transparent)]
#[derive(PartialEq, Eq)]
pub struct SubSlice<K: Borrow<str>, V>(pub(crate) [(K, V)]);

#[derive(Debug)]
/// Error indicating that duplicate entries were present in a slice passed to [`SubSlice::from_mut_slice`].
/// This error also contains the duplicate string in question.
pub struct DuplicatesPresent<'a>(&'a str);

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl std::error::Error for DuplicatesPresent<'_> {}

impl fmt::Display for DuplicatesPresent<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "duplicate key found while attempting conversion to SubSlice: {}",
            self.0
        )
    }
}

impl<K: Borrow<str>, V> SubSlice<K, V> {
    /// Generates a Self from a ref to backing storage
    pub(crate) const fn cast_from_slice_core(v: &[(K, V)]) -> &Self {
        // SAFETY: we are repr(transparent) with [(K, V)], and the lifetime/mutability remains identical
        unsafe { &*(v as *const [(K, V)] as *const Self) }
    }

    /// Generates a Self from a mut ref to backing storage
    pub(crate) fn cast_from_slice_mut_core(v: &mut [(K, V)]) -> &mut Self {
        // SAFETY: we are repr(transparent) with [(K, V)], and the lifetime/mutability remains identical
        unsafe { &mut *(v as *mut [(K, V)] as *mut Self) }
    }

    /// Returns inner contents as immutable slice
    const fn as_slice(&self) -> &[(K, V)] {
        &self.0
    }

    /// Makes a mutable ref to a `SubSlice` from a raw data slice. Sorts data internally.
    ///
    /// This operation is `O(n log n)`.
    ///
    /// # Errors
    /// This will return `DuplicatesPresent` if any duplicate keys are present in the slice.
    ///
    /// # Examples
    /// ```rust
    /// # use prefix_array::SubSlice;
    /// // Find items with prefix "a" using a stack allocated array
    /// let mut data = [("abcde", 0), ("foo", 1), ("baz", 2)];
    ///
    /// let subslice = SubSlice::from_mut_slice(&mut data).unwrap();
    ///
    /// assert_eq!(subslice.find_all_with_prefix("a").to_vec(), &[("abcde", 0)]);
    /// ```
    /// ```rust
    /// # use prefix_array::SubSlice;
    /// // Duplicates will raise an error
    /// let mut data = [("a", 5), ("b", 2), ("a", 6)];
    ///
    /// assert!(SubSlice::from_mut_slice(&mut data).is_err());
    /// ```
    ///
    pub fn from_mut_slice(data: &mut [(K, V)]) -> Result<&mut Self, DuplicatesPresent<'_>> {
        Self::from_mut_slice_impl(data).map_err(|e| DuplicatesPresent(e.0))
    }

    /// An immutable iterator over all the elements in this slice in sorted-by-key order.
    pub fn iter(&self) -> Iter<K, V> {
        Iter(self.as_slice().iter())
    }

    /// Creates an owned copy of this [`SubSlice`] as a [`Vec`].
    /// If you wish to preserve [`PrefixArray`] semantics consider using [`ToOwned`] instead.
    pub fn to_vec(&self) -> Vec<(K, V)>
    where
        K: Clone,
        V: Clone,
    {
        self.as_slice().to_vec()
    }

    /// Finds all items with the given prefix using binary search
    fn find_all_with_prefix_idx(&self, prefix: &str) -> core::ops::Range<usize> {
        self.find_all_with_prefix_idx_impl(prefix)
    }

    /// Returns the `SubSlice` where all `K` have the same prefix `prefix`.
    ///
    /// Will return an empty array if there are no matches.
    ///
    /// This operation is `O(log n)`
    ///
    /// # Examples
    /// ```rust
    /// # use prefix_array::PrefixArray;
    /// let arr: PrefixArray<&str, u8>;
    /// # arr = PrefixArray::from_iter([("abcde", 3), ("among", 56), ("aba", 3)]);
    ///
    /// let slice = arr.find_all_with_prefix("a");
    /// /* do something with items starting with a */
    ///
    /// // instead of searching `arr` again, we can narrow what we
    /// //  already searched and stored in `slice` for efficiency
    /// for (ab, _) in slice.find_all_with_prefix("ab") {
    ///     assert!(ab.starts_with("ab"));
    /// }
    /// ```
    pub fn find_all_with_prefix<'a>(&'a self, prefix: &str) -> &'a Self {
        let range = self.find_all_with_prefix_idx(prefix);
        self.reslice(range)
    }

    /// Returns a mutable `SubSlice` where all `K` have the same prefix `prefix`.
    ///
    /// Will return an empty array if there are no matches.
    ///
    /// This operation is `O(log n)`
    ///
    /// # Examples
    /// ```rust
    /// # use prefix_array::PrefixArray;
    /// let mut arr: PrefixArray<&str, u8>;
    /// # arr = PrefixArray::from_iter([("abcde", 3), ("among", 56), ("aba", 3)]);
    ///
    /// for (_, v) in arr.find_all_with_prefix_mut("ab") {
    ///     *v += 1;
    /// }
    /// ```
    pub fn find_all_with_prefix_mut<'a>(&'a mut self, prefix: &str) -> &'a mut Self {
        let range = self.find_all_with_prefix_idx(prefix);
        self.reslice_mut(range)
    }

    /// Compute the common prefix of this [`SubSlice`] from the data.
    /// Will return an empty string if this subslice is empty.
    ///
    /// Note that this may be more specific than what was searched for, i/e:
    /// ```rust
    /// # use prefix_array::PrefixArray;
    /// let arr = PrefixArray::from_iter([("abcde", 0), ("abcdef", 1)]);
    /// // Common prefix is *computed*, so even though we only
    /// //  searched for "a" we got something more specific
    /// assert_eq!(arr.find_all_with_prefix("a").common_prefix(), "abcde");
    /// ```
    ///
    /// This operation is `O(1)`, but it is not computationally free.
    pub fn common_prefix(&self) -> &str {
        self.common_prefix_impl()
    }

    /// Returns whether this [`SubSlice`] contains the given key
    ///
    /// This operation is `O(log n)`.
    ///
    /// # Examples
    /// ```rust
    /// # use prefix_array::PrefixArray;
    /// let arr = PrefixArray::from_iter([("1234", "abcde")]);
    ///
    /// assert!(arr.contains_key("1234"));
    /// ```
    pub fn contains_key(&self, key: &str) -> bool {
        self.contains_key_impl(key)
    }

    /// Gets an immutable ref to the value behind the given key if it exists
    ///
    /// This operation is `O(log n)`.
    pub fn get(&self, key: &str) -> Option<&V> {
        self.get_impl(key).map(|(_k, v)| v)
    }

    /// Gets a mutable ref to the value behind the given key if it exists.
    ///
    /// This operation is `O(log n)`.
    pub fn get_mut(&mut self, key: &str) -> Option<&mut V> {
        self.get_mut_impl(key).map(|(_k, v)| v)
    }

    /// Returns the key value pair corresponding to the given key.
    ///
    /// This operation is `O(log n)`.
    pub fn get_key_value(&self, key: &str) -> Option<(&K, &V)> {
        self.get_impl(key).map(|(k, v)| (k, v))
    }

    /// An iterator visiting all key value pairs in sorted-by-key order, with mutable references to the values.
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut(self.0.iter_mut())
    }

    /// Returns whether this [`SubSlice`] is empty
    ///
    /// # Examples
    /// ```rust
    /// # use prefix_array::PrefixArray;
    /// let arr = PrefixArray::<&str, ()>::new();
    ///
    /// assert!(arr.is_empty());
    /// ```
    pub const fn is_empty(&self) -> bool {
        self.as_slice().is_empty()
    }

    /// Returns the length of this [`SubSlice`]
    pub const fn len(&self) -> usize {
        self.as_slice().len()
    }

    #[cfg(test)]
    fn assert_invariants(&self) {
        let mut last = None::<&K>;

        for (k, _) in self.as_slice() {
            if let Some(prev) = last {
                assert!(prev.borrow() < k.borrow());
            }

            last = Some(k);
        }
    }
}

#[cfg(test)]
mod test {

    use super::*;

    #[test]
    fn mutate() {
        let mut v = PrefixArray::from_iter([("among", 4i32), ("foo", 6)]);

        *v.get_mut("among").unwrap() = 24;

        assert_eq!(v.common_prefix(), "");

        assert_eq!(Some(&24), v.get("among"));

        assert_eq!(v.remove_entry("among"), Some(("among", 24)));

        assert_eq!(v.len(), 1);

        v.extend([("amongus", 324), ("asdfsaf", 234)]);

        assert_eq!(v.len(), 3);

        assert_eq!(v.find_all_with_prefix("a").common_prefix(), "a");

        v.extend([("0", 324), ("01", 234)]);

        assert_eq!(v.len(), 5);

        v.assert_invariants();

        v.extend(Some(("0", 12)));

        // extend should overwrite values
        assert_eq!(v.get("0"), Some(&12));
    }

    #[test]
    fn weird_lifetimes() {
        let v = PrefixArray::from_iter([("we".to_owned(), 1), ("woo".into(), 2)]);

        let res: &i32;

        {
            let s = "we".to_owned();
            // ensure get(&self, &str) -> Option<&V> elides properly
            res = v.get(&s).unwrap();
            drop(s);
        }

        assert_eq!(res, &1);
    }

    #[test]
    fn extend() {
        let mut v = PrefixArray::new();

        v.extend([("a", 0), ("a", 1)]);

        assert_eq!(v.len(), 1);
    }

    #[test]
    fn extend_with() {
        let mut v = PrefixArray::from_iter([("a", 0), ("b", 2)]);
        let mut scratch = ScratchSpace::with_capacity(2);

        v.extend_with(&mut scratch, [("c", 4), ("d", 4)]);

        assert_eq!(v.len(), 4);

        assert!(scratch.0.is_empty());
        assert_eq!(scratch.0.capacity(), 2);
    }

    #[test]
    fn insert_wont_update_key() {
        #[derive(Debug)]
        struct TrackerStr<'a>(&'a str, u64);

        impl core::borrow::Borrow<str> for TrackerStr<'_> {
            fn borrow(&self) -> &str {
                self.0
            }
        }

        let mut arr = PrefixArray::<TrackerStr<'static>, u8>::new();

        arr.insert(TrackerStr("abc", 0), 0);

        assert_eq!(arr.get("abc"), Some(&0));

        arr.insert(TrackerStr("abc", 1), 1);

        assert!(matches!(
            arr.get_key_value("abc"),
            Some((TrackerStr("abc", 0), 1))
        ));
    }
}
