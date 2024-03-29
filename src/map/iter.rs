//! Iterator types for `PrefixArray`/`SubSlice` types
extern crate alloc;

use core::{borrow::Borrow, iter::FusedIterator};

// TODO: impl TrustedLen when it becomes stable

/// Asserts double ended
const fn is_double_ended<T: DoubleEndedIterator>() {}
/// Asserts fused
const fn is_fused<T: FusedIterator>() {}
/// Asserts exactsize
const fn is_exactsize<T: ExactSizeIterator>() {}

// we dont repeat this code to `set/iter.rs` because those iterators point here and we know we impl the traits
/// Asserts that the iterator type is `Fused`, `DoubleEnded`, and `ExactSize`
macro_rules! assert_ty {
    ($t:ty) => {
        #[allow(unused)]
        const _: () = {
            is_double_ended::<$t>();
            is_fused::<$t>();
            is_exactsize::<$t>();
        };
    };
}

/// Consuming Iterator from a [`PrefixArray`][super::PrefixArray]
pub struct IntoIter<K, V>(alloc::vec::IntoIter<(K, V)>);

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }

    #[inline]
    fn count(self) -> usize {
        self.0.count()
    }

    // TODO impl next_chunk when feature(iter_next_chunk) is stabilized
    // TODO impl advance_by when feature(iter_advance_by) is stabilized
}

assert_ty!(alloc::vec::IntoIter<()>);
impl<K, V> FusedIterator for IntoIter<K, V> {}
impl<K, V> ExactSizeIterator for IntoIter<K, V> {}

impl<K, V> DoubleEndedIterator for IntoIter<K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }
}

/// Immutable view Iterator from a [`PrefixArray`][super::PrefixArray] or [`SubSlice`][super::SubSlice]
pub struct Iter<'a, K, V>(pub(super) core::slice::Iter<'a, (K, V)>);

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, v)| (k, v))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }

    #[inline]
    fn count(self) -> usize {
        self.0.count()
    }

    // TODO impl next_chunk when feature(iter_next_chunk) is stabilized
    // TODO impl advance_by when feature(iter_advance_by) is stabilized
}

assert_ty!(core::slice::Iter<'_, ()>);
impl<'a, K, V> FusedIterator for Iter<'a, K, V> {}
impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> {}

impl<'a, K, V> DoubleEndedIterator for Iter<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|(k, v)| (k, v))
    }
}

/// Mutable view Iterator from a [`PrefixArray`][super::PrefixArray] or [`SubSlice`][super::SubSlice]
pub struct IterMut<'a, K, V>(pub(super) core::slice::IterMut<'a, (K, V)>);

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, v)| (&*k, v))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }

    #[inline]
    fn count(self) -> usize {
        self.0.count()
    }

    // TODO impl next_chunk when feature(iter_next_chunk) is stabilized
    // TODO impl advance_by when feature(iter_advance_by) is stabilized
}

assert_ty!(core::slice::IterMut<'_, ()>);
impl<'a, K, V> FusedIterator for IterMut<'a, K, V> {}
impl<'a, K, V> ExactSizeIterator for IterMut<'a, K, V> {}

impl<'a, K, V> DoubleEndedIterator for IterMut<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|(k, v)| (&*k, v))
    }
}

/// A Draining Iterator of some or all elements of a [`PrefixArray`][super::PrefixArray].
///  Holds a mutable reference to the parent `PrefixArray`
pub struct Drain<'a, K, V>(pub(super) alloc::vec::Drain<'a, (K, V)>);

impl<'a, K, V> Iterator for Drain<'a, K, V> {
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }

    #[inline]
    fn count(self) -> usize {
        self.0.count()
    }
    // TODO impl next_chunk when feature(iter_next_chunk) is stabilized
    // TODO impl advance_by when feature(iter_advance_by) is stabilized
}

assert_ty!(alloc::vec::Drain<'_, ()>);
impl<'a, K, V> FusedIterator for Drain<'a, K, V> {}
impl<'a, K, V> ExactSizeIterator for Drain<'a, K, V> {}

impl<'a, K, V> DoubleEndedIterator for Drain<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }
}

impl<K: Borrow<str>, V> IntoIterator for super::PrefixArray<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.0.into_iter())
    }
}

/// Generates `IntoIterator` implementations for `PrefixArray` types
macro_rules! into_iter_gen {
    (for $t:ty where Item = $item:ty, IntoIter = $into_iter:ty, do $code:tt ) => {
        impl<'a, K: Borrow<str>, V> IntoIterator for $t {
            type Item = $item;
            type IntoIter = $into_iter;

            fn into_iter(self) -> Self::IntoIter {
                self.$code()
            }
        }
    };
}

into_iter_gen!(for &'a super::PrefixArray<K, V> where Item = (&'a K, &'a V), IntoIter = Iter<'a, K, V>, do iter);
into_iter_gen!(for &'a mut super::PrefixArray<K, V> where Item = (&'a K, &'a mut V), IntoIter = IterMut<'a, K, V>, do iter_mut);

into_iter_gen!(for &'a super::SubSlice<K, V> where Item = (&'a K, &'a V), IntoIter = Iter<'a, K, V>, do iter);
into_iter_gen!(for &'a mut super::SubSlice<K, V> where Item = (&'a K, &'a mut V), IntoIter = IterMut<'a, K, V>, do iter_mut);

impl<K: Borrow<str>, V> core::iter::FromIterator<(K, V)> for super::PrefixArray<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        Self::from_vec_lossy(iter.into_iter().collect())
    }
}

#[test]
fn is_into_iter() {
    let mut parr = super::PrefixArray::from_iter([("among", 2i32), ("we", 4)]);

    for (_, v) in &mut parr {
        *v += 1;
    }

    let mut sum = 0;

    for (_, v) in &parr {
        sum += v;
    }

    assert_eq!(sum, 8);

    for (_, v) in parr.find_all_with_prefix_mut("amon") {
        *v += 1;
    }

    assert_eq!(parr.get("among"), Some(&4));

    drop(parr);
}
