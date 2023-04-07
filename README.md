# prefix\_array
This crate provides the `PrefixArray` and `PrefixArraySet` datastructures that implement some Map-like and Set-like interfaces, while also being capable of querying data based on what it starts with (its prefix).  

prefix\_array boasts zero memory overhead, `log n` searching, and searching on subsets of the main array. This crate also has the advantage of cache locality over a tree type datastructure.  

# `no_std` Support
This crate is no\_std capable, but has the `std` feature enabled by default (currently this adds From impls for `HashMap` and `HashSet`).

# License
This crate is licensed under MPL-2.0 (less common for rust crates), broadly this implies that you may use this crate in a closed source project, and statically link it, but any modifications to the crate itself must be made public. This is not legal advice.
