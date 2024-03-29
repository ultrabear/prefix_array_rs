// STOP! Are you trying to read this crates source code?
//
// shared.rs contains the primary implementations of PrefixArray* and *SubSlice in a trait form.
// Its done this way so that PrefixArray can be a Vec<(K, V)> and PrefixArraySet can be a Vec<K>,
// instead of having PrefixArraySet be a PrefixArray<K, ()> under the hood (this allows some extra
// safe guarantees like being able to expose &[K] safely in public apis).
//
// Unsafe code worth auditing is in shared/vec_ext.rs, which houses the only significant unsafe
// code in the crate (and is the only place where a safety bug could potentially be, as other
// unsafe uses are trivial).
//
// map.rs and set.rs contain public api and public impls for PrefixArray/Set and Set/SubSlice
// while the associated (map|set)/iter.rs contains boilerplate for the iterators they implement.
//
// Most test cases live in map.rs where they are tested against the public api of PrefixArray, as
// it shares logic with PrefixArraySet; if it is correct PrefixArraySet (a subset of it) should also
// be correct. We do need more test cases to comprehensively prove some behaviours still.
//
#![no_std]
#![warn(clippy::alloc_instead_of_core, clippy::std_instead_of_alloc)]
#![warn(clippy::pedantic, clippy::cargo)]
#![allow(clippy::module_name_repetitions)]
#![warn(missing_docs, clippy::missing_docs_in_private_items)]
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
//! If you have a partially filled `PrefixArray(Set)` and need to call `Extend` multiple times, but
//! can share state between each call, consider using `ScratchSpace` and the `extend_with` method.
//! This can avoid excessive allocations that the `Extend` method would otherwise have (as it needs
//! to allocate to insert many items at once).
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

pub mod shared;
