extern crate alloc;

use core::{borrow::Borrow, iter::FusedIterator};

/// Iterator from a [`PrefixArraySet`][super::PrefixArraySet].
pub struct IntoIter<K>(alloc::vec::IntoIter<K>);

impl<K> Iterator for IntoIter<K> {
    type Item = K;

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

impl<K> FusedIterator for IntoIter<K> {}
impl<K> ExactSizeIterator for IntoIter<K> {}

impl<K> DoubleEndedIterator for IntoIter<K> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }
}

/// Immutable view Iterator from a [`PrefixArraySet`][super::PrefixArraySet] or [`SetSubSlice`][super::SetSubSlice]
pub struct Iter<'a, K>(pub(super) core::slice::Iter<'a, K>);

impl<'a, K> Iterator for Iter<'a, K> {
    type Item = &'a K;

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

impl<'a, K> FusedIterator for Iter<'a, K> {}
impl<'a, K> ExactSizeIterator for Iter<'a, K> {}

impl<'a, K> DoubleEndedIterator for Iter<'a, K> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }
}

/// A Draining Iterator of some or all elements of a [`PrefixArraySet`][super::PrefixArraySet].
///  Holds a mutable reference to the parent `PrefixArraySet`
pub struct Drain<'a, K>(pub(super) alloc::vec::Drain<'a, K>);

impl<'a, K> Iterator for Drain<'a, K> {
    type Item = K;

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

impl<'a, K> FusedIterator for Drain<'a, K> {}
impl<'a, K> ExactSizeIterator for Drain<'a, K> {}

impl<'a, K> DoubleEndedIterator for Drain<'a, K> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }
}

impl<K: Borrow<str>> IntoIterator for super::PrefixArraySet<K> {
    type Item = K;
    type IntoIter = IntoIter<K>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.0.into_iter())
    }
}

impl<'a, K: Borrow<str>> IntoIterator for &'a super::PrefixArraySet<K> {
    type Item = &'a K;
    type IntoIter = Iter<'a, K>;

    fn into_iter(self) -> Self::IntoIter {
        Iter(self.0.iter())
    }
}

impl<'a, K: Borrow<str>> IntoIterator for &'a super::SetSubSlice<K> {
    type Item = &'a K;
    type IntoIter = Iter<'a, K>;

    fn into_iter(self) -> Self::IntoIter {
        Iter(self.0.iter())
    }
}

impl<K: Borrow<str>> core::iter::FromIterator<K> for super::PrefixArraySet<K> {
    fn from_iter<T: IntoIterator<Item = K>>(iter: T) -> Self {
        Self::from_vec_lossy(iter.into_iter().collect())
    }
}
