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
        type Item = (K, ());
    }
}

use sealed::PrefixMapOrSet;

use crate::PrefixArray;

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
        core::mem::replace(dst, src).1
    }

    fn as_str(v: &Self::Data) -> &str {
        v.0.borrow()
    }
}
