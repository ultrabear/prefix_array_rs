//! A Map API based on a prefix array, this module contains the [`PrefixArray`] type.

#[cfg(any(test, feature = "std"))]
extern crate std;

extern crate alloc;

use alloc::{borrow::ToOwned, vec::Vec};
use core::{
    cmp::Ordering,
    ops::{Deref, DerefMut},
};
use ref_cast::{ref_cast_custom, RefCastCustom};

mod vec_ext;
use vec_ext::InsertMany;
mod iter;
pub use iter::{Drain, IntoIter, Iter, IterMut};

/// A generic search-by-prefix array designed to find strings with common prefixes in `O(log n)` time, and easily search on subslices to refine a previous search.
///
/// The generic parameter is mainly in place so that `&'a str`, `String`, and `&'static str` may all be used for the backing storage.
///  It is a logical error for an implementer of `AsRef<str>` to return different data across multiple calls while it remains in this container.
///  Doing so renders the datastructure useless (but will NOT cause UB).
///
/// The main downside of a [`PrefixArray`] over a trie type datastructure is that insertions have a significant `O(n)` cost,
/// so if you are adding multiple values over the lifetime of the [`PrefixArray`] it may become less efficient overall than a traditional tree
#[derive(Debug)]
pub struct PrefixArray<K: AsRef<str>, V>(pub(crate) Vec<(K, V)>);

// Manually impl to get clone_from
impl<K: AsRef<str> + Clone, V: Clone> Clone for PrefixArray<K, V> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }

    fn clone_from(&mut self, other: &Self) {
        self.0.clone_from(&other.0);
    }
}

impl<K: AsRef<str>, V> Default for PrefixArray<K, V> {
    fn default() -> Self {
        PrefixArray::new()
    }
}

impl<K: AsRef<str>, V> PrefixArray<K, V> {
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
    pub fn from_vec_lossy(mut v: Vec<(K, V)>) -> Self {
        v.sort_unstable_by(|f, s| f.0.as_ref().cmp(s.0.as_ref()));
        v.dedup_by(|f, s| f.0.as_ref() == s.0.as_ref());

        Self(v)
    }

    /// Inserts the given K/V pair into the [`PrefixArray`], returning the old V if one was present for this K
    ///
    /// This operation is `O(n)`.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        match self.0.binary_search_by_key(&key.as_ref(), |s| s.0.as_ref()) {
            Err(idx) => {
                self.0.insert(idx, (key, value));
                None
            }
            Ok(idx) => {
                let mut sbox = (key, value);
                core::mem::swap(&mut self.0[idx], &mut sbox);

                Some(sbox.1)
            }
        }
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
        if let Ok(idx) = self.0.binary_search_by_key(&key, |s| s.0.as_ref()) {
            Some(self.0.remove(idx))
        } else {
            None
        }
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
}

impl<K: AsRef<str>, V> Extend<(K, V)> for PrefixArray<K, V> {
    /// Extends the [`PrefixArray`] with more values, skipping any duplicates.
    ///
    /// This operation is `O(n + k log k)` where k is the number of elements in the iterator.
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = (K, V)>,
    {
        let mut extra = iter
            .into_iter()
            .filter_map(|k| {
                self.0
                    .binary_search_by_key(&k.0.as_ref(), |s| s.0.as_ref())
                    .err()
                    .map(|idx| (idx, k))
            })
            .collect::<Vec<(usize, (K, V))>>();

        // presort by string so that identical indexes are mapped correctly
        extra.sort_unstable_by(|(_, a), (_, b)| a.0.as_ref().cmp(b.0.as_ref()));

        self.0.insert_many(extra);
    }
}

#[cfg(feature = "std")]
impl<K: AsRef<str>, V, H> From<std::collections::HashMap<K, V, H>> for PrefixArray<K, V> {
    /// Performs a lossless conversion from a `HashMap<K, V>` to a `PrefixArray<K, V>` in `O(n log n)` time.
    fn from(v: std::collections::HashMap<K, V, H>) -> Self {
        let mut unsorted = v.into_iter().collect::<Vec<(K, V)>>();
        // can't use by_key because of lifetime issues with as_ref
        unsorted.sort_unstable_by(|f, s| f.0.as_ref().cmp(s.0.as_ref()));

        Self(unsorted)
    }
}

impl<K: AsRef<str>, V> From<PrefixArray<K, V>> for Vec<(K, V)> {
    fn from(v: PrefixArray<K, V>) -> Vec<(K, V)> {
        v.0
    }
}

impl<K: AsRef<str>, V> Deref for PrefixArray<K, V> {
    type Target = SubSlice<K, V>;

    fn deref(&self) -> &Self::Target {
        SubSlice::from_slice(self.0.as_slice())
    }
}

impl<K: AsRef<str>, V> DerefMut for PrefixArray<K, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        SubSlice::from_slice_mut(self.0.as_mut_slice())
    }
}

impl<K: AsRef<str>, V> core::borrow::Borrow<SubSlice<K, V>> for PrefixArray<K, V> {
    fn borrow(&self) -> &SubSlice<K, V> {
        self
    }
}

impl<K: AsRef<str> + Clone, V: Clone> ToOwned for SubSlice<K, V> {
    type Owned = PrefixArray<K, V>;

    fn to_owned(&self) -> PrefixArray<K, V> {
        // here we can assert the invariants were upheld
        PrefixArray(self.to_vec())
    }
}

/// A [`SubSlice`] of a [`PrefixArray`] in which all items contain a common prefix (which may be the unit prefix `""`).
///
/// The [`SubSlice`] does not store what that common prefix is for performance reasons, it is up to the user to keep track of.
#[derive(RefCastCustom, Debug)]
#[repr(transparent)]
pub struct SubSlice<K: AsRef<str>, V>([(K, V)]);

impl<K: AsRef<str>, V> SubSlice<K, V> {
    // ref cast needs that unsafe block
    // not public as it violates encapsulation
    #[allow(unsafe_code)]
    #[ref_cast_custom]
    const fn from_slice(v: &[(K, V)]) -> &Self;

    // ref cast needs that unsafe block
    // not public as it violates encapsulation
    #[allow(unsafe_code)]
    #[ref_cast_custom]
    // transmute is handled by a macro, and ref-cast asserts it is safe
    #[allow(clippy::transmute_ptr_to_ptr)]
    fn from_slice_mut(v: &mut [(K, V)]) -> &mut Self;

    /// reslices self, panics on oob
    fn reslice<I: core::slice::SliceIndex<[(K, V)], Output = [(K, V)]>>(&self, i: I) -> &Self {
        Self::from_slice(&self.as_slice()[i])
    }

    /// reslices self, panics on oob
    fn reslice_mut<I: core::slice::SliceIndex<[(K, V)], Output = [(K, V)]>>(
        &mut self,
        i: I,
    ) -> &mut Self {
        Self::from_slice_mut(&mut self.0[i])
    }

    /// Returns inner contents as immutable slice
    const fn as_slice(&self) -> &[(K, V)] {
        &self.0
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
        // skip comparisons if we have a unit prefix
        if prefix.is_empty() {
            return 0..self.len();
        }

        if let Ok(start) = self.as_slice().binary_search_by(|s| {
            if s.0.as_ref().starts_with(prefix) {
                Ordering::Equal
            } else {
                s.0.as_ref().cmp(prefix)
            }
        }) {
            let min =
                self.as_slice()[..start].partition_point(|s| !s.0.as_ref().starts_with(prefix));
            let max = self.as_slice()[start..]
                .partition_point(|s| s.0.as_ref().starts_with(prefix))
                + start;

            min..max
        } else {
            0..0
        }
    }

    /// Returns the `SubSlice` where all `K` have the same prefix `prefix`.
    ///
    /// Will return an empty array if there are no matches.
    ///
    /// This operation is `O(log n)`
    pub fn find_all_with_prefix<'a>(&'a self, prefix: &str) -> &'a Self {
        let range = self.find_all_with_prefix_idx(prefix);
        self.reslice(range)
    }

    /// Returns a mutable `SubSlice` where all `K` have the same prefix `prefix`.
    ///
    /// Will return an empty array if there are no matches.
    ///
    /// This operation is `O(log n)`
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
        let Some(first) = self.as_slice().first().map(|s| s.0.as_ref()) else { return ""; };

        let Some(last) = self.as_slice().last().map(|s| s.0.as_ref()) else { return "" };

        let last_idx = first.len().min(last.len());

        let mut end_idx = 0;

        for ((idx, fch), lch) in first
            .char_indices()
            .zip(last.chars())
            .chain([((last_idx, ' '), ' ')])
        {
            end_idx = idx;
            if fch != lch {
                break;
            }
        }

        &first[..end_idx]
    }

    /// Returns whether this [`SubSlice`] contains the given key
    ///
    /// This operation is `O(log n)`.
    pub fn contains_key(&self, key: &str) -> bool {
        self.as_slice()
            .binary_search_by_key(&key, |s| s.0.as_ref())
            .is_ok()
    }

    /// Gets an immutable ref to the value behind the given key if it exists
    ///
    /// This operation is `O(log n)`.
    pub fn get(&self, key: &str) -> Option<&V> {
        match self.as_slice().binary_search_by_key(&key, |s| s.0.as_ref()) {
            Ok(idx) => Some(&self.as_slice()[idx].1),
            Err(_) => None,
        }
    }

    /// Gets a mutable ref to the value behind the given key if it exists.
    ///
    /// This operation is `O(log n)`.
    pub fn get_mut(&mut self, key: &str) -> Option<&mut V> {
        match self.0.binary_search_by_key(&key, |s| s.0.as_ref()) {
            Ok(idx) => Some(&mut self.0[idx].1),
            Err(_) => None,
        }
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
                assert!(prev.as_ref() < k.as_ref());
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
    }
}
