# soavec

A vector-like data-structure for convenient growable Struct-of-Arrays
creation and manipulation.

The [`SoAVec`] type is recommended for use in places where multiple structs
need to be stored on the heap and their access to or iteration of is done
mostly field-wise as opposed to all-fields-together.

# Basic usage

The [`SoAble`] trait can be derived on structs to conveniently split them
up into Struct-of-Arrays format field-wise and to generate wrapper types
for the [`as_ref`], [`as_mut`], [`as_slice`], and [`as_mut_slice`] methods'
return types. For advanced usage, the [`SoAble`] trait can be implemented
manually.

When deriving the [`SoAble`] trait it is recommended to write the struct
definition in order of alignment and size, eg. a `u64` field should come
before a `[u32; 3]` field. If the [`SoAble`] trait is implemented manually
then the struct's layout ordering does not matter but the chosen
[tuple representation] should still uphold this same order. This ensures
that the `SoAVec` does not need to add extra padding between field slices.

# Example

```rust
use soavec::soavec;
use soavec_derive::SoAble;

#[derive(Clone, SoAble)]
struct Basic {
  a: Vec<u32>,
  b: usize,
  c: u16,
  d: bool,
}

let mut vec = soavec![Basic { a: vec![1, 2, 3], b: 55, c: 4, d: false }; 32].unwrap();
let BasicSlice {
  a,
  b,
  c,
  d,
} = vec.as_slice();
assert_eq!(a, vec![vec![1, 2, 3]; 32]);
assert_eq!(b, vec![55usize; 32]);
assert_eq!(c, vec![4u16; 32]);
assert_eq!(d, vec![false; 32]);
```

[`SoAVec`]: https://docs.rs/soavec/latest/soavec/struct.SoAVec.html
[`SoAble`]: docs.rs/soavec/latest/soavec/trait.SoAble.html
[`as_ref`]: https://docs.rs/soavec/latest/soavec/struct.SoAVec.html#method.as_ref
[`as_mut`]: https://docs.rs/soavec/latest/soavec/struct.SoAVec.html#method.as_mut
[`as_slice`]: https://docs.rs/soavec/latest/soavec/struct.SoAVec.html#method.as_slice
[`as_mut_slice`]: https://docs.rs/soavec/latest/soavec/struct.SoAVec.html#method.as_mut_slice
