extern crate alloc;

use core::iter::FusedIterator;

/// Iterator from a [`PrefixArraySet`][super::PrefixArraySet].
pub struct IntoIter<K: AsRef<str>>(crate::map::IntoIter<K, ()>);

impl<K: AsRef<str>> Iterator for IntoIter<K> {
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, _)| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K: AsRef<str>> FusedIterator for IntoIter<K> {}
impl<K: AsRef<str>> ExactSizeIterator for IntoIter<K> {}

impl<K: AsRef<str>> DoubleEndedIterator for IntoIter<K> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|(k, _)| k)
    }
}

/// Immutable view Iterator from a [`PrefixArraySet`][super::PrefixArraySet] or [`SetSubSlice`][super::SetSubSlice]
pub struct Iter<'a, K: AsRef<str>>(pub(super) crate::map::Iter<'a, K, ()>);

impl<'a, K: AsRef<str>> Iterator for Iter<'a, K> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, _)| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a, K: AsRef<str>> FusedIterator for Iter<'a, K> {}
impl<'a, K: AsRef<str>> ExactSizeIterator for Iter<'a, K> {}

impl<'a, K: AsRef<str>> DoubleEndedIterator for Iter<'a, K> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|(k, _)| k)
    }
}

impl<K: AsRef<str>> IntoIterator for super::PrefixArraySet<K> {
    type Item = K;
    type IntoIter = IntoIter<K>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.0.into_iter())
    }
}

impl<'a, K: AsRef<str>> IntoIterator for &'a super::PrefixArraySet<K> {
    type Item = &'a K;
    type IntoIter = Iter<'a, K>;

    fn into_iter(self) -> Self::IntoIter {
        Iter(self.0.iter())
    }
}

impl<K: AsRef<str>> core::iter::FromIterator<K> for super::PrefixArraySet<K> {
    fn from_iter<T: IntoIterator<Item = K>>(iter: T) -> Self {
        Self::from_vec_lossy(iter.into_iter().collect())
    }
}
