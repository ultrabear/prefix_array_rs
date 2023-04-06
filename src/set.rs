//! A Set API based on a prefix array, this module contains the [`PrefixArraySet`] type.

#[cfg(any(test, feature = "std"))]
extern crate std;

extern crate alloc;

use alloc::{borrow::ToOwned, vec::Vec};
use core::ops::Deref;

mod iter;
pub use iter::{Drain, IntoIter, Iter};

use super::map;

/// A generic search-by-prefix array designed to find strings with common prefixes in `O(log n)` time, and easily search on subslices to refine a previous search.
///
/// The generic parameter is mainly in place so that `&'a str`, `String`, and `&'static str` may all be used for the backing storage.
///  It is a logical error for an implementer of `AsRef<str>` to return different data across multiple calls while it remains in this container.
///  Doing so renders the datastructure useless (but will NOT cause UB).
///
/// The main downside of a [`PrefixArraySet`] over a trie type datastructure is that insertions have a significant `O(n)` cost,
/// so if you are adding multiple values over the lifetime of the [`PrefixArraySet`] it may become less efficient overall than a traditional tree
#[derive(Debug)]
pub struct PrefixArraySet<K: AsRef<str>>(map::PrefixArray<K, ()>);

// Manually impl to get clone_from
impl<K: AsRef<str> + Clone> Clone for PrefixArraySet<K> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }

    fn clone_from(&mut self, other: &Self) {
        self.0.clone_from(&other.0);
    }
}

impl<K: AsRef<str>> Default for PrefixArraySet<K> {
    fn default() -> Self {
        PrefixArraySet::new()
    }
}

impl<K: AsRef<str>> PrefixArraySet<K> {
    /// Create a new empty [`PrefixArraySet`].
    ///
    /// This function will not allocate anything.
    #[must_use]
    pub const fn new() -> Self {
        Self(map::PrefixArray::new())
    }

    /// Creates a new empty [`PrefixArraySet`] with space for at least `capacity` elements.
    ///
    /// See [`Vec::with_capacity`] for additional notes.
    ///
    /// # Panics:
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self(map::PrefixArray::with_capacity(capacity))
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
        Self(map::PrefixArray::from_vec_lossy(
            v.into_iter().map(|v| (v, ())).collect(),
        ))
    }

    /// Inserts the given K into the [`PrefixArraySet`], returning true if the key was not already in the set
    ///
    /// This operation is `O(n)`.
    pub fn insert(&mut self, key: K) -> bool {
        self.0.insert(key, ()).is_none()
    }

    /// Adds a value to the set, replacing the existing value, if any, that is equal to the given one.  
    /// Returns the replaced value.
    pub fn replace(&mut self, key: K) -> Option<K> {
        // This functionality is not available in the HashMap api so we will make it ourself
        match (self.0)
            .0
            .binary_search_by_key(&key.as_ref(), |s| s.0.as_ref())
        {
            Ok(idx) => Some(core::mem::replace(&mut (self.0).0[idx].0, key)),
            Err(idx) => {
                (self.0).0.insert(idx, (key, ()));
                None
            }
        }
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
        Drain(self.0.drain_all_with_prefix(prefix))
    }

    /// Drains all elements of the [`PrefixArraySet`], returning them in an iterator.
    /// Keeps the backing allocation intact, unlike [`IntoIter`].
    ///
    /// When this iterator is dropped it drops all remaining elements.
    pub fn drain(&mut self) -> Drain<K> {
        Drain(self.0.drain())
    }

    /// Removes the value that matches the given key, returning true if it was present in the set
    ///
    /// This operation is `O(log n)` if the key was not found, and `O(n)` if it was.
    pub fn remove(&mut self, key: &str) -> bool {
        self.0.remove(key).is_some()
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

    /// Makes a `PrefixArraySet` from an iterator in which all key items are unique
    fn from_unique_iter<T: IntoIterator<Item = K>>(v: T) -> Self {
        Self(map::PrefixArray::from_unique_iter(
            v.into_iter().map(|k| (k, ())),
        ))
    }
}

impl<K: AsRef<str>> Extend<K> for PrefixArraySet<K> {
    /// Extends the [`PrefixArraySet`] with more values, overwriting any duplicates with the new values.
    ///
    /// This operation is `O(n + k log k)` where k is the number of elements in the iterator.
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = K>,
    {
        self.0.extend(iter.into_iter().map(|k| (k, ())));
    }
}

#[cfg(feature = "std")]
impl<K: AsRef<str>, H> From<std::collections::HashSet<K, H>> for PrefixArraySet<K> {
    /// Performs a lossless conversion from a `HashSet<K>` to a `PrefixArraySet<K>` in `O(n log n)` time.
    ///
    /// This assumes the implementation of `AsRef<str>` is derived from the same data that the `Eq + Hash` implementation uses.
    /// It is a logic error if this is untrue, and will render this datastructure useless.
    fn from(v: std::collections::HashSet<K, H>) -> Self {
        Self::from_unique_iter(v)
    }
}

impl<K: AsRef<str>> From<alloc::collections::BTreeSet<K>> for PrefixArraySet<K> {
    /// Performs a lossless conversion from a `BTreeSet<K>` to a `PrefixArraySet<K>` in `O(n log n)` time.
    ///
    /// This assumes the implementation of `AsRef<str>` is derived from the same data that the `Ord` implementation uses.
    /// It is a logic error if this is untrue, and will render this datastructure useless.
    fn from(v: std::collections::BTreeSet<K>) -> Self {
        Self::from_unique_iter(v)
    }
}

impl<K: AsRef<str>> From<PrefixArraySet<K>> for Vec<K> {
    fn from(v: PrefixArraySet<K>) -> Vec<K> {
        Vec::from(v.0).into_iter().map(|(k, _)| k).collect()
    }
}

impl<K: AsRef<str>> Deref for PrefixArraySet<K> {
    type Target = SetSubSlice<K>;

    fn deref(&self) -> &Self::Target {
        SetSubSlice::from_map_slice(&*self.0)
    }
}

impl<K: AsRef<str>> core::borrow::Borrow<SetSubSlice<K>> for PrefixArraySet<K> {
    fn borrow(&self) -> &SetSubSlice<K> {
        self
    }
}

impl<K: AsRef<str> + Clone> ToOwned for SetSubSlice<K> {
    type Owned = PrefixArraySet<K>;

    fn to_owned(&self) -> PrefixArraySet<K> {
        // here we can assert the invariants were upheld
        PrefixArraySet(map::PrefixArray(self.0.to_vec()))
    }

    fn clone_into(&self, target: &mut PrefixArraySet<K>) {
        self.0.clone_into(&mut target.0);
    }
}

/// A subslice of a [`PrefixArraySet`] in which all items contain a common prefix (which may be the unit prefix `""`).
///
/// The [`SetSubSlice`] does not store what that common prefix is for performance reasons (but it can be computed, see: [`SetSubSlice::common_prefix`]), it is up to the user to keep track of.
#[derive(Debug)]
// SAFETY: this type must remain repr(transparent) to map::SubSlice<K, ()> for from_map_slice invariants
#[repr(transparent)]
pub struct SetSubSlice<K: AsRef<str>>(map::SubSlice<K, ()>);

impl<K: AsRef<str>> SetSubSlice<K> {
    /// creates a ref to Self from a ref to backing storage
    // bypass lint level
    #[allow(unsafe_code)]
    fn from_map_slice(v: &map::SubSlice<K, ()>) -> &Self {
        // SAFETY: this type is repr(transparent), and the lifetimes are both &'a
        unsafe { &*(v as *const map::SubSlice<K, ()> as *const SetSubSlice<K>) }
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
        (self.0).0.iter().map(|(k, _)| k.clone()).collect()
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
        Self::from_map_slice(self.0.find_all_with_prefix(prefix))
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
        self.0.common_prefix()
    }

    /// Returns whether this [`SetSubSlice`] contains the given key
    ///
    /// This operation is `O(log n)`.
    pub fn contains(&self, key: &str) -> bool {
        self.0.contains_key(key)
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

    use std::vec;

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
}
