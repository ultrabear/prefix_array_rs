extern crate alloc;

use core::iter::FusedIterator;

/// Consuming Iterator from a [`PrefixArray`][super::PrefixArray]
pub struct IntoIter<K: AsRef<str>, V>(alloc::vec::IntoIter<(K, V)>);

impl<K: AsRef<str>, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K: AsRef<str>, V> FusedIterator for IntoIter<K, V> {}
impl<K: AsRef<str>, V> ExactSizeIterator for IntoIter<K, V> {}

impl<K: AsRef<str>, V> DoubleEndedIterator for IntoIter<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }
}

/// Immutable view Iterator from a [`PrefixArray`][super::PrefixArray] or [`SubSlice`][super::SubSlice]
pub struct Iter<'a, K: AsRef<str>, V>(core::slice::Iter<'a, (K, V)>);

impl<'a, K: AsRef<str>, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, v)| (k, v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a, K: AsRef<str>, V> FusedIterator for Iter<'a, K, V> {}
impl<'a, K: AsRef<str>, V> ExactSizeIterator for Iter<'a, K, V> {}

impl<'a, K: AsRef<str>, V> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|(k, v)| (k, v))
    }
}

/// Mutable view Iterator from a [`PrefixArray`][super::PrefixArray] or [`SubSlice`][super::SubSlice]
pub struct IterMut<'a, K: AsRef<str>, V>(core::slice::IterMut<'a, (K, V)>);

impl<'a, K: AsRef<str>, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, v)| (&*k, v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a, K: AsRef<str>, V> FusedIterator for IterMut<'a, K, V> {}
impl<'a, K: AsRef<str>, V> ExactSizeIterator for IterMut<'a, K, V> {}

impl<'a, K: AsRef<str>, V> DoubleEndedIterator for IterMut<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|(k, v)| (&*k, v))
    }
}

impl<K: AsRef<str>, V> IntoIterator for super::PrefixArray<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.0.into_iter())
    }
}

impl<K: AsRef<str>, V> core::iter::FromIterator<(K, V)> for super::PrefixArray<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        Self::from_vec_lossy(iter.into_iter().collect())
    }
}
