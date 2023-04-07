#![no_std]
#![deny(unsafe_code)]
#![warn(clippy::pedantic)]
#![warn(clippy::cargo)]
#![warn(missing_docs)]
#![allow(clippy::module_name_repetitions)]
#![warn(clippy::alloc_instead_of_core, clippy::std_instead_of_alloc)]
//! `prefix_array` is a crate consisting of datastructures that aid in querying data based on prefixes of string keys,
//!  the main feature being searching and refining on subgroups with common prefixes.
//!
//!  Use [`PrefixArray`] when you want a HashMap-like structure, and [`PrefixArraySet`] for a HashSet-like structure.
//!
//! ## Creating a PrefixArray(Set)
//! For creating a new collection, ideally you can use the `FromIterator` implementation, this has `O(n log n)` complexity and with an `ExactSizeIterator` will allocate once.
//!  If you cannot use `FromIterator` it is recommended to use `PrefixArray(Set)::from_vec_lossy` instead, as this is what `FromIterator` calls under the hood.
//!
//! It is ill advised to use `insert` in a loop to create a `PrefixArray(Set)`, as this has `O(n^2)` complexity.
//!
//! For an already partially filled `PrefixArray(Set)` that you wish to insert multiple items into, consider the `Extend` implementation, which is specifically designed for this purpose.
//!
//! ## Basic usage
//! ```rust
//! use prefix_array::PrefixArray;
//!
//! // construct a new prefix array from an iterator
//! let arr = PrefixArray::from_iter([("abcde", 123), ("absgh", 1234)]);
//!
//! // borrow a subslice of all data with the prefix 'ab'
//! let mut subslice = arr.find_all_with_prefix("ab");
//!
//! assert_eq!(subslice.len(), 2);
//!
//! // we can refine the subslice
//! subslice = subslice.find_all_with_prefix("abc");
//!
//! assert_eq!(subslice.len(), 1);
//!
//! // and find when something doesn't exist
//! assert!(subslice.find_all_with_prefix("ba").is_empty());
//! ```

pub mod map;
pub use map::{PrefixArray, SubSlice};

pub mod set;
pub use set::{PrefixArraySet, SetSubSlice};
