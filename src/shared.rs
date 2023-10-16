//! Shared implementations between [`PrefixArray`](super::PrefixArray) and
//! [`PrefixArraySet`](super::PrefixArraySet).
extern crate alloc;

use core::{borrow::Borrow, cmp::Ordering};

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
    type Data;

    fn construct(v: Vec<Self::Data>) -> Self;

    fn replace_value(src: Self::Data, dst: &mut Self::Data) -> V;

    fn as_str(v: &Self::Data) -> &str;

    fn get_vec_mut(&mut self) -> &mut Vec<Self::Data>;

    fn cmp(a: &Self::Data, b: &Self::Data) -> Ordering {
        Self::as_str(a).cmp(Self::as_str(b))
    }

    fn eq(a: &Self::Data, b: &Self::Data) -> bool {
        Self::cmp(a, b).is_eq()
    }

    fn from_vec_lossy_impl(mut v: Vec<Self::Data>) -> Self {
        v.sort_unstable_by(|f, s| Self::as_str(f).cmp(Self::as_str(s)));
        v.dedup_by(|f, s| Self::as_str(f) == Self::as_str(s));

        Self::construct(v)
    }

    fn insert_impl(&mut self, data: Self::Data) -> Option<V> {
        match self
            .get_vec_mut()
            .binary_search_by_key(&Self::as_str(&data), |s| Self::as_str(s))
        {
            Err(idx) => {
                self.get_vec_mut().insert(idx, data);
                None
            }
            Ok(idx) => Some(Self::replace_value(data, &mut self.get_vec_mut()[idx])),
        }
    }

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

    fn extend_with_impl<I>(&mut self, insert: &mut Vec<(usize, Self::Data)>, iter: I)
    where
        I: IntoIterator<Item = Self::Data>,
    {
        use crate::map::vec_ext::InsertMany;

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
                    Self::replace_value(k, &mut self.get_vec_mut()[idx]);
                }
            }
        }

        // presort by string so that identical indexes are mapped correctly
        insert.sort_unstable_by(|(_, a), (_, b)| Self::cmp(a, b));

        // avoid duplicate K being inserted
        insert.dedup_by(|(_, a), (_, b)| Self::eq(a, b));

        self.get_vec_mut().insert_many(insert);
    }

    fn from_unique_iter_impl<T: IntoIterator<Item = Self::Data>>(v: T) -> Self {
        let mut unsorted = v.into_iter().collect::<Vec<Self::Data>>();
        // can't use by_key because of lifetime issues with as_ref
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

    fn replace_value(src: Self::Data, dst: &mut Self::Data) -> V {
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
    fn replace_value(_src: Self::Data, _dst: &mut Self::Data) {}

    fn get_vec_mut(&mut self) -> &mut Vec<Self::Data> {
        &mut self.0
    }
}

use core::slice::SliceIndex;

pub(crate) struct DuplicatesPresent<'a>(pub(crate) &'a str);

pub(crate) trait PrefixBorrowed {
    type Data;

    fn get_mut_slice(&mut self) -> &mut [Self::Data];
    fn get_slice(&self) -> &[Self::Data];

    fn cast_from_slice_mut(s: &mut [Self::Data]) -> &mut Self;
    fn cast_from_slice(s: &[Self::Data]) -> &Self;

    fn as_str(v: &Self::Data) -> &str;

    fn cmp(a: &Self::Data, b: &Self::Data) -> Ordering {
        Self::as_str(a).cmp(Self::as_str(b))
    }

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

    fn contains_key_impl(&self, key: &str) -> bool {
        self.get_slice()
            .binary_search_by_key(&key, |s| Self::as_str(s))
            .is_ok()
    }

    fn get_impl(&self, key: &str) -> Option<&Self::Data> {
        match self
            .get_slice()
            .binary_search_by_key(&key, |s| Self::as_str(s))
        {
            Ok(idx) => Some(&self.get_slice()[idx]),
            Err(_) => None,
        }
    }

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
