#![no_std]
#![deny(unsafe_code)]
#![warn(clippy::pedantic)]
#![warn(clippy::cargo)]
#![warn(missing_docs)]
#![allow(clippy::module_name_repetitions)]
//! `prefix_array` is a crate consisting of datastructures that aid in querying data based on prefixes of string keys,
//!  the main feature being searching and refining on subgroups with common prefixes.
//!
//!  Use [`PrefixArray`] when you want a HashMap-like structure, and [`PrefixArraySet`] for a HashSet-like structure.

pub mod map;
pub use map::{PrefixArray, SubSlice};

pub mod set;
pub use set::{PrefixArraySet, SetSubSlice};
