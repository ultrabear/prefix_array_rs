extern crate alloc;

/// Iterator from a [`PrefixArray`][super::PrefixArray]
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

impl<K: AsRef<str>, V> core::iter::FusedIterator for IntoIter<K, V> {}
impl<K: AsRef<str>, V> ExactSizeIterator for IntoIter<K, V> {}

impl<K: AsRef<str>, V> DoubleEndedIterator for IntoIter<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
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
