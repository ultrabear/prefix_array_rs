# prefix\_array
This crate provides the `PrefixArray` and `PrefixArraySet` datastructures that implement some Map-like and Set-like interfaces, while also being capable of querying data based on what it starts with (its prefix).  
This crate is no\_std capable, but has the `std` feature enabled by default (currently this adds From impls for `HashMap` and `HashSet`).

