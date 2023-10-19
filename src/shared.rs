//! Shared implementations between [`PrefixArray`](super::PrefixArray) and
//! [`PrefixArraySet`](super::PrefixArraySet).
extern crate alloc;

use core::{borrow::Borrow, cmp::Ordering, mem};

use alloc::vec::Vec;

mod vec_ext;
use vec_ext::InsertMany;

/// Sealed module to prevent `PrefixMapOrSet` leaking
mod sealed {

    use core::borrow::Borrow;

    /// private-public bounding trait representing any valid `PrefixArray` or `PrefixArraySet`
    pub trait PrefixMapOrSet {
        /// The Data that this collection stores for scratch space
        type Item;
    }

    impl<K: Borrow<str>, V> PrefixMapOrSet for crate::PrefixArray<K, V> {
        type Item = (K, V);
    }

    impl<K: Borrow<str>> PrefixMapOrSet for crate::PrefixArraySet<K> {
        type Item = K;
    }
}

use sealed::PrefixMapOrSet;

use crate::{PrefixArray, PrefixArraySet, SetSubSlice, SubSlice};

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

/// A trait that abstracts over `PrefixArray` and `PrefixArraySet` owned variants
/// This allows defining implementations once
pub(crate) trait PrefixOwned<V>: Sized {
    /// The data that this `PrefixOwned` stores internally
    type Data;

    /// Builds a new owned instance from a Vec of backing Data
    fn construct(v: Vec<Self::Data>) -> Self;

    /// Replaces only the value portion in a Data, may be a no op for valueless data
    fn replace_value(dst: &mut Self::Data, src: Self::Data) -> V;

    /// Returns the indexable string from this Data
    fn as_str(v: &Self::Data) -> &str;

    /// Gets mutable reference to inner Vec
    fn get_vec_mut(&mut self) -> &mut Vec<Self::Data>;

    /// Convenience fn to compare two Data by their string repr
    fn cmp(a: &Self::Data, b: &Self::Data) -> Ordering {
        Self::as_str(a).cmp(Self::as_str(b))
    }

    /// Convenience fn to compare two Data by their string repr
    fn eq(a: &Self::Data, b: &Self::Data) -> bool {
        Self::cmp(a, b).is_eq()
    }

    /// Implements the `from_vec_lossy` impl that sorts and discards duplicates
    fn from_vec_lossy_impl(mut v: Vec<Self::Data>) -> Self {
        v.sort_unstable_by(|f, s| Self::as_str(f).cmp(Self::as_str(s)));
        v.dedup_by(|f, s| Self::as_str(f) == Self::as_str(s));

        Self::construct(v)
    }

    /// Implements an `insert` impl that calls a replacer function when a value was already in the
    /// collection
    fn insert_internal<F: Fn(&mut Self::Data, Self::Data) -> T, T>(
        &mut self,
        replacer: F,
        data: Self::Data,
    ) -> Option<T> {
        let vec = self.get_vec_mut();

        match vec.binary_search_by_key(&Self::as_str(&data), |s| Self::as_str(s)) {
            Err(idx) => {
                vec.insert(idx, data);
                None
            }
            Ok(idx) => Some(replacer(&mut vec[idx], data)),
        }
    }

    /// Implements the `insert` impl that inserts new key value pairs, and on a preexisting key only
    /// updates the value
    fn insert_impl(&mut self, data: Self::Data) -> Option<V> {
        self.insert_internal(Self::replace_value, data)
    }

    /// Implements the `insert_replace` impl that inserts a new value and always replaces all of
    /// the previous value if there was one
    fn insert_replace_impl(&mut self, data: Self::Data) -> Option<Self::Data> {
        self.insert_internal(mem::replace, data)
    }

    /// Implements the `remove_entry` impl that removes something fully with the given key if it exists
    fn remove_entry_impl(&mut self, key: &str) -> Option<Self::Data> {
        if let Ok(idx) = self
            .get_vec_mut()
            .binary_search_by_key(&key, |s| Self::as_str(s))
        {
            Some(self.get_vec_mut().remove(idx))
        } else {
            None
        }
    }

    /// Implements the `extend_with` impl that takes a scratch space and an iterator of addable data
    /// to extend the collection
    fn extend_with_impl<I>(&mut self, insert: &mut Vec<(usize, Self::Data)>, iter: I)
    where
        I: IntoIterator<Item = Self::Data>,
    {
        let iter = iter.into_iter();

        // clear for correctness, a scratchspace should become empty after an insert_many call and
        // there is no other way to push to it than this method, but we should prevent the
        // possibility here anyways
        insert.clear();

        // speculative optimization, assume that most items are going to be newly inserted
        // this will over allocate when that is untrue
        insert.reserve(iter.size_hint().0);

        for k in iter {
            match self
                .get_vec_mut()
                .binary_search_by_key(&Self::as_str(&k), |s| Self::as_str(s))
            {
                // add to insertion set
                Err(idx) => insert.push((idx, k)),
                // replace old value
                Ok(idx) => {
                    Self::replace_value(&mut self.get_vec_mut()[idx], k);
                }
            }
        }

        // presort by string so that identical indexes are mapped correctly
        insert.sort_unstable_by(|(_, a), (_, b)| Self::cmp(a, b));

        // avoid duplicate K being inserted
        insert.dedup_by(|(_, a), (_, b)| Self::eq(a, b));

        self.get_vec_mut().insert_many(insert);
    }

    /// Implements the `from_unique_iter` impl that builds a collection from an iterator that is
    /// guaranteed to have unique key items
    fn from_unique_iter_impl<T: IntoIterator<Item = Self::Data>>(v: T) -> Self {
        let mut unsorted = v.into_iter().collect::<Vec<Self::Data>>();
        unsorted.sort_unstable_by(|f, s| Self::cmp(f, s));

        Self::construct(unsorted)
    }
}

impl<K: Borrow<str>, V> PrefixOwned<V> for PrefixArray<K, V> {
    type Data = (K, V);

    fn construct(v: Vec<Self::Data>) -> Self {
        Self(v)
    }

    fn get_vec_mut(&mut self) -> &mut Vec<Self::Data> {
        &mut self.0
    }

    fn replace_value(dst: &mut Self::Data, src: Self::Data) -> V {
        core::mem::replace(&mut dst.1, src.1)
    }

    fn as_str(v: &Self::Data) -> &str {
        v.0.borrow()
    }
}

impl<K: Borrow<str>> PrefixOwned<()> for PrefixArraySet<K> {
    type Data = K;

    fn construct(v: Vec<Self::Data>) -> Self {
        Self(v)
    }

    fn as_str(v: &Self::Data) -> &str {
        v.borrow()
    }

    // no op
    fn replace_value(_dst: &mut Self::Data, _src: Self::Data) {}

    fn get_vec_mut(&mut self) -> &mut Vec<Self::Data> {
        &mut self.0
    }
}

use core::slice::SliceIndex;

/// Internal `DuplicatesPresent` error, this location may become public in the future to allow
/// map/set to both define `from_mut_slice` more seamlessly
pub(crate) struct DuplicatesPresent<'a>(pub(crate) &'a str);

/// A trait that abstracts over `PrefixArray` and `PrefixArraySet` borrowed variants
/// This allows defining implementations once
pub(crate) trait PrefixBorrowed {
    /// The data that this `PrefixBorrowed` stores internally
    type Data;

    /// gets inner slice mutably
    fn get_mut_slice(&mut self) -> &mut [Self::Data];
    /// gets inner slice
    fn get_slice(&self) -> &[Self::Data];

    /// Builds Self from a mutable slice
    fn cast_from_slice_mut(s: &mut [Self::Data]) -> &mut Self;
    /// Builds Self from a slice
    fn cast_from_slice(s: &[Self::Data]) -> &Self;

    /// Gets the indexable string from the given Data
    fn as_str(v: &Self::Data) -> &str;

    /// Convenience fn to compare Data by its indexable string
    fn cmp(a: &Self::Data, b: &Self::Data) -> Ordering {
        Self::as_str(a).cmp(Self::as_str(b))
    }

    /// Convenience fn to compare Data by its indexable string
    fn eq(a: &Self::Data, b: &Self::Data) -> bool {
        Self::cmp(a, b).is_eq()
    }

    /// reslices self, panics on oob
    fn reslice<I: SliceIndex<[Self::Data], Output = [Self::Data]>>(&self, i: I) -> &Self {
        Self::cast_from_slice(&self.get_slice()[i])
    }

    /// reslices self, panics on oob
    fn reslice_mut<I: SliceIndex<[Self::Data], Output = [Self::Data]>>(
        &mut self,
        i: I,
    ) -> &mut Self {
        Self::cast_from_slice_mut(&mut self.get_mut_slice()[i])
    }

    /// Implements builds a &mut Self from a slice of Data, validating that it can be a Self and
    /// sorting internally
    fn from_mut_slice_impl(data: &mut [Self::Data]) -> Result<&mut Self, DuplicatesPresent<'_>> {
        data.sort_unstable_by(|a, b| Self::cmp(a, b));

        if data.len() <= 1 {
            return Ok(Self::cast_from_slice_mut(data));
        }

        let mut error = None;

        for (idx, d) in data.windows(2).enumerate() {
            if Self::eq(&d[0], &d[1]) {
                error = Some(idx);
                break;
            }
        }

        match error {
            Some(idx) => Err(DuplicatesPresent(Self::as_str(&data[idx]))),
            None => Ok(Self::cast_from_slice_mut(data)),
        }
    }

    /// Finds all items with the given prefix using binary search
    fn find_all_with_prefix_idx_impl(&self, prefix: &str) -> core::ops::Range<usize> {
        // skip comparisons if we have a unit prefix
        if prefix.is_empty() {
            return 0..self.get_slice().len();
        }

        if let Ok(start) = self.get_slice().binary_search_by(|s| {
            if Self::as_str(s).starts_with(prefix) {
                Ordering::Equal
            } else {
                Self::as_str(s).cmp(prefix)
            }
        }) {
            let min =
                self.get_slice()[..start].partition_point(|s| !Self::as_str(s).starts_with(prefix));
            let max = self.get_slice()[start..]
                .partition_point(|s| Self::as_str(s).starts_with(prefix))
                + start;

            min..max
        } else {
            0..0
        }
    }

    /// Returns the common prefix of all of the keys in the collection
    fn common_prefix_impl(&self) -> &str {
        let Some(first) = self.get_slice().first().map(|s| Self::as_str(s)) else {
            return "";
        };

        let Some(last) = self.get_slice().last().map(|s| Self::as_str(s)) else {
            return "";
        };

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

    /// Returns whether the collection contains the given key
    fn contains_key_impl(&self, key: &str) -> bool {
        self.get_slice()
            .binary_search_by_key(&key, |s| Self::as_str(s))
            .is_ok()
    }

    /// View the contents of an entry if there is one by the given key
    fn get_impl(&self, key: &str) -> Option<&Self::Data> {
        match self
            .get_slice()
            .binary_search_by_key(&key, |s| Self::as_str(s))
        {
            Ok(idx) => Some(&self.get_slice()[idx]),
            Err(_) => None,
        }
    }

    /// View the contents of an entry mutably if there is one by the given key
    fn get_mut_impl(&mut self, key: &str) -> Option<&mut Self::Data> {
        match self
            .get_slice()
            .binary_search_by_key(&key, |s| Self::as_str(s))
        {
            Ok(idx) => Some(&mut self.get_mut_slice()[idx]),
            Err(_) => None,
        }
    }
}

impl<K: Borrow<str>, V> PrefixBorrowed for SubSlice<K, V> {
    type Data = (K, V);

    fn get_mut_slice(&mut self) -> &mut [Self::Data] {
        &mut self.0
    }
    fn get_slice(&self) -> &[Self::Data] {
        &self.0
    }

    fn cast_from_slice_mut(s: &mut [Self::Data]) -> &mut Self {
        Self::cast_from_slice_mut_core(s)
    }
    fn cast_from_slice(s: &[Self::Data]) -> &Self {
        Self::cast_from_slice_core(s)
    }

    fn as_str(v: &Self::Data) -> &str {
        v.0.borrow()
    }
}

impl<K: Borrow<str>> PrefixBorrowed for SetSubSlice<K> {
    type Data = K;

    fn get_mut_slice(&mut self) -> &mut [Self::Data] {
        &mut self.0
    }

    fn get_slice(&self) -> &[Self::Data] {
        &self.0
    }

    fn cast_from_slice_mut(s: &mut [Self::Data]) -> &mut Self {
        Self::cast_from_slice_mut_core(s)
    }

    fn cast_from_slice(s: &[Self::Data]) -> &Self {
        Self::cast_from_slice_core(s)
    }

    fn as_str(v: &Self::Data) -> &str {
        v.borrow()
    }
}
