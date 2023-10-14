extern crate alloc;

use alloc::vec::Vec;

use core::mem::MaybeUninit;
use core::ptr;

/// A trait to insert many items into one Vec at once
pub(super) trait InsertMany<T> {
    /// Inserts many T at any index, will insert in a stable sorted order.
    ///
    /// Each index is inserted via the original lists order, or, this is functionally equivalent to:
    /// ```rust
    /// let mut src: Vec<(usize, i32)>;
    /// # src = vec![(0, 4), (0, 3)];
    /// let mut dst: Vec<i32>;
    /// # dst = Vec::new();
    ///
    /// src.sort_by_key(|(idx, _)| *idx);
    ///
    /// for (idx, i) in src.into_iter().rev() {
    ///   dst.insert(idx, i);
    /// }
    /// # assert_eq!(dst, &[4, 3]);
    /// ```
    ///
    /// # Panics
    /// This will panic if any index passed is **greater** than the length of the source list
    ///  (it may be **equal** to the length of the list to be appended to the end though (see: [`Vec::extend`] if you wish to do only that)).
    ///
    /// This will panic if self.len() + insert.len() overflows.
    fn insert_many(&mut self, insert: &mut Vec<(usize, T)>);
}

impl<T> InsertMany<T> for Vec<T> {
    fn insert_many(&mut self, insert: &mut Vec<(usize, T)>) {
        // PRECOND: we need enough space to add the new values
        self.reserve(insert.len());

        // PRECOND: list must be stable sorted by the usize key
        insert.sort_by_key(|d| d.0);

        // PRECOND: lengths cannot overflow
        let new_len = self
            .len()
            .checked_add(insert.len())
            .expect("<Vec<T> as InsertMany>: New len overflows usize");

        // PRECOND: greatest idx length cannot be greater than self.len()
        if let Some((idx, _)) = insert.last() {
            assert!(
                *idx <= self.len(),
                "<Vec<T> as InsertMany>: an index passed was greater than the length of the list"
            );
        }

        // bypass lint level
        // welcome to the Fun Zone
        #[allow(unsafe_code)]
        {
            // Set length to zero so we can treat everything as uninitialized
            // SAFETY: 0 is always <= capacity
            unsafe { self.set_len(0) };

            // this is the entire vec
            let raw_vec = self.spare_capacity_mut();

            let mut insert_left = insert.len();
            // raw_vec[written_to..] is written to
            let mut written_to = new_len;

            for (idx, t) in insert.drain(..).rev() {
                // idx will never be greater than original_len because we sorted and checked the max value
                // this relies on TrustedOrd with usize, but that must be true
                insert_left -= 1;

                let my_idx = insert_left + idx;

                // PRECOND: use *mut for stacked borrows compliance
                let v_ptr = (raw_vec as *mut [MaybeUninit<T>]).cast::<MaybeUninit<T>>();

                // we need this check, because if it happens to be 0, my_idx+1 could be out of bounds (and violate the safety contract of copy)
                if (written_to - (my_idx + 1)) != 0 {
                    // Final preflight checks
                    debug_assert!(my_idx + 1 < new_len);
                    debug_assert!(written_to <= new_len);
                    debug_assert!(idx < new_len);

                    // SAFETY: my_idx is less than new_len (our max capacity) because we reserved at least enough,
                    // so written_to(bounded<=new_len) (-(my_idx + 1) cancels out +my_idx+1) is always writable
                    // we must move the memory greater than idx but lower than the previously placed value up
                    // we move written_to - (my_idx + 1) values as we want to fill the data starting after my_idx
                    // and before the last written to point
                    //
                    // This is safe because even if at some point the raw bytes of a T exists twice, it will eventually be overwritten by extra writes
                    // if any panics occur, recall that we set length to 0, so memory will be leaked instead of causing UB
                    //
                    // We use copy here and NOT copy_nonoverlapping intentionally, as the two regions may overlap
                    unsafe {
                        ptr::copy(
                            v_ptr.add(idx) as *const _,
                            v_ptr.add(my_idx + 1),
                            written_to - (my_idx + 1),
                        );
                    }
                }

                // write our special little value to its special little index
                // and mark it as the last written_to point
                raw_vec[my_idx].write(t);
                written_to = my_idx;
            }

            // SAFETY: We have written up till this point
            unsafe { self.set_len(new_len) };
        }
    }
}

#[test]
fn oh_boy() {
    extern crate std;

    let mut v = std::vec![1, 2, 3, 4];

    v.insert_many(&mut std::vec![
        (0, 8i32),
        (0, 7),
        (1, 6),
        (4, 5),
        (4, 10),
        (3, 11)
    ]);

    assert_eq!(v, &[8, 7, 1, 6, 2, 3, 11, 4, 5, 10]);

    v.insert_many(&mut [(0, 0)].into());

    assert_eq!(v, &[0, 8, 7, 1, 6, 2, 3, 11, 4, 5, 10]);

    v.insert_many(&mut std::vec![(v.len(), 32)]);

    assert_eq!(v, &[0, 8, 7, 1, 6, 2, 3, 11, 4, 5, 10, 32]);

    Vec::<u8>::new().insert_many(&mut Vec::new());

    Vec::<u8>::new().insert_many(&mut std::vec![(0, 1), (0, 2), (0, 3)]);

    Vec::<u8>::from([1, 2, 3]).insert_many(&mut Vec::new());

    Vec::<u8>::from([1]).insert_many(&mut Vec::new());
}

#[test]
#[should_panic]
fn size_overflow() {
    extern crate std;
    use alloc::vec;

    vec![].insert_many(&mut vec![(1, 2u8)]);
}

#[test]
fn assert_zsts() {
    use alloc::vec;

    vec![(), (), ()].insert_many(&mut vec![(0, ()), (1, ()), (2, ()), (3, ()), (1, ())]);

    vec![(), ()].insert_many(&mut vec![(0, ()), (1, ()), (2, ()), (1, ())]);

    vec![].insert_many(&mut vec![(0, ())]);
}
