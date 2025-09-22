// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! A vector-like data-structure for convenient growable Struct-of-Arrays
//! creation and manipulation.
//!
//! The [`SoAVec`] type is recommended for use in places where multiple structs
//! need to be stored on the heap and their access to or iteration of is done
//! mostly field-wise as opposed to all-fields-together.
//!
//! # Basic usage
//!
//! The [`SoAble`] trait can be derived on structs to conveniently split them
//! up into Struct-of-Arrays format field-wise and to generate wrapper types
//! for the [`as_ref`], [`as_mut`], [`as_slice`], and [`as_mut_slice`] methods'
//! return types. For advanced usage, the [`SoAble`] trait can be implemented
//! manually.
//!
//! When deriving the [`SoAble`] trait it is recommended to write the struct
//! definition in order of alignment and size, eg. a `u64` field should come
//! before a `[u32; 3]` field. If the [`SoAble`] trait is implemented manually
//! then the struct's layout ordering does not matter but the chosen
//! [tuple representation] should still uphold this same order. This ensures
//! that the `SoAVec` does not need to add extra padding between field slices.
//!
//! # Example
//!
//! ```rust
//! use soavec::soavec;
//! use soavec_derive::SoAble;
//!
//! #[derive(Clone, SoAble)]
//! struct Basic {
//!   a: Vec<u32>,
//!   b: usize,
//!   c: u16,
//!   d: bool,
//! }
//!
//! let mut vec = soavec![Basic { a: vec![1, 2, 3], b: 55, c: 4, d: false }; 32].unwrap();
//! let BasicSlice {
//!   a,
//!   b,
//!   c,
//!   d,
//! } = vec.as_slice();
//! assert_eq!(a, vec![vec![1, 2, 3]; 32]);
//! assert_eq!(b, vec![55usize; 32]);
//! assert_eq!(c, vec![4u16; 32]);
//! assert_eq!(d, vec![false; 32]);
//! ```
//!
//! [`SoAVec`]: SoAVec
//! [`SoAble`]: SoAble
//! [`as_ref`]: SoAVec::as_ref
//! [`as_mut`]: SoAVec::as_mut
//! [`as_slice`]: SoAVec::as_slice
//! [`as_mut_slice`]: SoAVec::as_mut_slice

mod macros;
mod raw_vec;
mod raw_vec_inner;
mod soable;

use core::marker::PhantomData;
use std::ptr::NonNull;

use raw_vec::RawSoAVec;
use raw_vec_inner::AllocError;
pub use soable::{SoATuple, SoAble};

#[cfg(feature = "derive")]
pub use soavec_derive::*;

/// A contiguous growable Struct-of-Arrays type, written as `SoAVec<T>`, short
/// for ‘Struct-of-Arrays vector’.
///
/// The API and layout is purposefully very similar to a standard library
/// `Vec`, with the exception that the capacity is capped at 32-bit unsigned
/// values.
///
/// # Examples
///
/// ```
/// use soavec::SoAVec;
///
/// let mut vec = SoAVec::new();
/// vec.push((1, 1)).unwrap();
/// vec.push((2, 2)).unwrap();
///
/// assert_eq!(vec.len(), 2);
/// assert_eq!(vec.get(0).unwrap(), (&1, &1));
///
/// assert_eq!(vec.pop(), Some((2, 2)));
/// assert_eq!(vec.len(), 1);
///
/// let m = vec.get_mut(0).unwrap();
/// *m.0 = 7;
/// *m.1 = 7;
/// assert_eq!(vec.get(0).unwrap(), (&7, &7));
/// ```
///
/// The [`soavec!`] macro is provided for convenient initialization:
///
/// ```
/// use soavec::soavec;
///
/// let mut vec1 = soavec![(1, 1), (2, 2), (3, 3)].unwrap();
/// vec1.push((4, 4));
/// ```
///
/// It can also initialize each element of a `Vec<T>` with a given value.
///
/// ```
/// use soavec::soavec;
///
/// let vec = soavec![(0, 0); 5];
/// ```
///
/// For more information, see
/// [Capacity and Reallocation](#capacity-and-reallocation).
///
/// # Indexing
///
/// The `SoAVec` type does not allow access to values by index currently.
///
/// Use [`get`] and [`get_mut`] if you want to access an index in the `SoAVec`.
///
/// # Slicing
///
/// A `SoAVec` can be mutable. On the other hand, slices are read-only objects.
/// To get a [slice][prim@slice], use [`as_slice`] or [`as_mut_slice`]. Note
/// that these methods give out multiple slices, one for each field in the
/// struct. Example:
///
/// ```
/// use soavec::soavec;
///
/// fn read_slice(slice: &[usize]) {
///     // ...
/// }
///
/// let v = soavec![(0, 1), (0, 1)].unwrap();
/// let (zeros_slice, ones_slice) = v.as_slice();
/// read_slice(v.as_slice().0);
/// read_slice(v.as_slice().1);
/// ```
///
/// # Capacity and reallocation
///
/// The capacity of a Struct-of-Arrays vector is the amount of space allocated
/// for any future elements that will be added onto the vector. This is not to
/// be confused with the *length* of a vector, which specifies the number of
/// actual elements within the vector. If a vector's length exceeds its
/// capacity, its capacity will automatically be increased, but its elements
/// will have to be reallocated. The reallocation may also fail due to OOM or
/// other reasons, and these failures are exposed by the APIs. Thus methods
/// such as [`push`] and [`SoAVec::with_capacity`] may fail.
///
/// For example, a vector with capacity 10 and length 0 would be an empty
/// vector with space for 10 more elements. Pushing 10 or fewer elements onto
/// the vector will not change its capacity or cause reallocation to occur.
/// However, if the vector's length is increased to 11, it will have to
/// reallocate, which can be slow. For this reason, it is recommended to use
/// [`SoAVec::with_capacity`] whenever possible to specify how big the vector
/// is expected to get. This is even more important than with a traditional
/// `Vec`, as during reallocation `SoAVec` must also move all element data
/// except for the first fields.
///
/// # Guarantees
///
/// `SoAVec` is guaranteed to be a (pointer, capacity, length) triplet where
/// the capacity and length are 32-bit values regardless of architecture (note:
/// 16-bit systems are not supported but there the capacity and length would be
/// 16-bit values). The order of these fields is completely unspecified, and
/// you should use the appropriate methods to modify these. The pointer will
/// never be null, so this type is null-pointer-optimized.
///
/// However, the pointer might not actually point to allocated memory. In
/// particular, if you construct a `SoAVec` with capacity 0 via
/// [`SoAVec::new`], [`soavec![]`][`soavec!`],
/// [`SoAVec::with_capacity(0)`][`SoAVec::with_capacity`], it will not allocate
/// memory. Similarly, if you store zero-sized types inside a `SoAVec`, it will
/// not allocate space for them. *Note that in this case the `Vec` might not
/// report a [`capacity`] of 0*. `SoAVec` will allocate if and only if
/// <code>[size_of::\<T>]\() * [capacity]\() > 0</code>. In general, `SoAVec`'s
/// allocation details are very subtle indeed --- if you intend to allocate
/// memory using a `SoAVec` and use it for something else (either to pass to
/// unsafe code, or to build your own memory-backed collection), don't.
///
/// If a `SoAVec` *has* allocated memory, then the memory it points to is on
/// the heap (as defined by the allocator Rust is configured to use by
/// default), and its pointer points to a number of field slices determined by
/// the contained type, with each field slice containing [`len`] initialized,
/// contiguous field elements in order (what you would see if you call
/// `as_slice` or `as_mut_slice`), followed by <code>[capacity] - [len]</code>
/// logically uninitialized, contiguous field elements.
///
/// A vector containing two struct elements `'a'` and `'b'` with fields `'x'`
/// and `'y'`, and with capacity 4 can be visualized as below. The top part is
/// the `SoAVec` struct, it contains a pointer to the head of the allocation in
/// the heap, length and capacity. The bottom part is the allocation on the
/// heap, a contiguous memory block.
///
/// ```text
///             ptr      len  capacity
///        +--------+--------+--------+
///        | 0x0123 |      2 |      4 |
///        +--------+--------+--------+
///             |
///             v
/// Heap   +--------+--------+--------+--------+--------+--------+--------+--------+
///        |  'a.x' |  'b.x' | uninit | uninit |  'a.y' |  'b.y' | uninit | uninit |
///        +--------+--------+--------+--------+--------+--------+--------+--------+
/// ```
///
/// - **uninit** represents memory that is not initialized, see [`MaybeUninit`].
/// - Note: the ABI is not stable and `SoAVec` makes no guarantees about its
///   memory layout (including the order of fields).
///
/// `SoAVec` will never perform a "small optimization" where elements are
/// actually stored on the stack.
///
/// `SoAVec` will never automatically shrink itself, even if completely empty.
/// This ensures no unnecessary allocations or deallocations occur. Emptying a
/// `SoAVec` and then filling it back up to the same [`len`] should incur no
/// calls to the allocator.
///
/// [`push`] will never (re)allocate if the reported capacity is sufficient.
/// [`push`] *will* (re)allocate if <code>[len] == [capacity]</code>. That is,
/// the reported capacity is completely accurate. The size of the allocation is
/// not guaranteed to be equal to <code>size_of::\<T>]\() * [capacity]</code>,
/// as padding may be required between field slices.
///
/// `SoAVec` does not guarantee any particular growth strategy when
/// reallocating when full, nor when [`reserve`] is called. The current
/// strategy is basic and it may prove desirable to use a non-constant growth
/// factor. Whatever strategy is used will of course guarantee *O*(1) amortized
/// [`push`].
///
/// It is guaranteed, in order to respect the intentions of the programmer,
/// that all of `soavec![e_1, e_2, ..., e_n]`, `soavec![x; n]`, and
/// [`SoAVec::with_capacity(n)`] produce a `SoAVec` that requests an allocation
/// of the exact size needed for precisely `n` elements from the allocator,
/// and no other size (such as, for example: a size rounded up to the nearest
/// power of 2). The allocator will return an allocation that is at least as
/// large as requested, but it may be larger.
///
/// It is guaranteed that the [`SoAVec::capacity`] method returns a value that
/// is at least the requested capacity and not more than the allocated
/// capacity.
///
/// `SoAVec` will not specifically overwrite any data that is removed from it,
/// but also won't specifically preserve it. Its uninitialized memory is
/// scratch space that it may use however it wants. It will generally just do
/// whatever is most efficient or otherwise easy to implement. Do not rely on
/// removed data to be erased for security purposes. Even if you drop a
/// `SoAVec`, its buffer may simply be reused by another allocation. Even if
/// you zero a `SoAVec`'s memory first, that might not actually happen because
/// the optimizer does not consider this a side-effect that must be preserved.
///
/// Currently, `SoAVec` does not guarantee the order in which elements are
/// dropped.
///
/// [`get`]: SoAVec::get
/// [`get_mut`]: SoAVec::get_mut
/// [capacity]: SoAVec::capacity
/// [`capacity`]: SoAVec::capacity
/// [`SoAVec::capacity`]: SoAVec::capacity
/// [size_of::\<T>]: size_of
/// [len]: SoAVec::len
/// [`len`]: SoAVec::len
/// [`push`]: SoAVec::push
/// [`as_slice`]: SoAVec::as_slice
/// [`as_mut_slice`]: SoAVec::as_mut_slice
/// [`reserve`]: SoAVec::reserve
/// [`Vec::with_capacity(n)`]: SoAVec::with_capacity
/// [`MaybeUninit`]: core::mem::MaybeUninit
#[repr(C)]
pub struct SoAVec<T: SoAble> {
    buf: RawSoAVec<T>,
}

impl<T: SoAble> SoAVec<T> {
    pub fn new() -> Self {
        SoAVec {
            // SAFETY: 0-capacity vector cannot create an invalid layout.
            buf: unsafe { RawSoAVec::with_capacity(0).unwrap_unchecked() },
        }
    }

    /// Constructs a new, empty `SoAVec<T>` with at least the specified
    /// capacity. Returns an error if an allocator error occurred.
    ///
    /// The Struct-of-Arrays vector will be able to hold at least `capacity`
    /// elements without reallocating. This method is allowed to allocate for
    /// more elements than `capacity`. If `capacity` is zero, the vector will
    /// not allocate.
    ///
    /// It is important to note that although the returned vector has the
    /// minimum *capacity* specified, the vector will have a zero *length*. For
    /// an explanation of the difference between length and capacity, see
    /// *[Capacity and reallocation]*.
    ///
    /// If it is important to know the exact allocated capacity of a `SoAVec`,
    /// always use the [`capacity`] method after construction.
    ///
    /// For `SoAVec<T>` where `T` is a zero-sized type, there will be no
    /// allocation and the capacity will always be `usize::MAX`.
    ///
    /// [Capacity and reallocation]: #capacity-and-reallocation
    /// [`capacity`]: Vec::capacity
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// use soavec::SoAVec;
    ///
    /// let mut vec = SoAVec::<(u32, u32)>::with_capacity(10).unwrap();
    ///
    /// // The vector contains no items, even though it has capacity for more
    /// assert_eq!(vec.len(), 0);
    /// assert!(vec.capacity() >= 10);
    ///
    /// // These are all done without reallocating...
    /// for i in 0..10 {
    ///     vec.push((i, i));
    /// }
    /// assert_eq!(vec.len(), 10);
    /// assert!(vec.capacity() >= 10);
    ///
    /// // ...but this may make the vector reallocate
    /// vec.push((11, 11));
    /// assert_eq!(vec.len(), 11);
    /// assert!(vec.capacity() >= 11);
    ///
    /// // A vector of a zero-sized type will always over-allocate, since no
    /// // allocation is necessary
    /// let vec_units = SoAVec::<((), ())>::with_capacity(10).unwrap();
    /// assert_eq!(vec_units.capacity(), u32::MAX);
    /// ```
    pub fn with_capacity(cap: u32) -> Result<Self, AllocError> {
        Ok(SoAVec {
            buf: RawSoAVec::with_capacity(cap)?,
        })
    }

    /// Returns the number of elements in the vector, also referred to
    /// as its 'length'.
    ///
    /// # Examples
    ///
    /// ```
    /// use soavec::soavec;
    ///
    /// let mut a = soavec![(0, 0); 3].unwrap();
    /// assert_eq!(a.len(), 3);
    /// ```
    #[inline]
    pub fn len(&self) -> u32 {
        self.buf.len()
    }

    /// Returns `true` if the vector contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use soavec::SoAVec;
    ///
    /// let mut v = SoAVec::new();
    /// assert!(v.is_empty());
    ///
    /// v.push((1, 1));
    /// assert!(!v.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.buf.is_empty()
    }

    /// Returns the total number of elements the vector can hold without
    /// reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use soavec::SoAVec;
    ///
    /// let mut vec: SoAVec<(u32, i32)> = SoAVec::with_capacity(10).unwrap();
    /// vec.push((42, 3));
    /// assert!(vec.capacity() >= 10);
    /// ```
    ///
    /// A vector with zero-sized elements will always have a capacity of usize::MAX:
    ///
    /// ```
    /// use soavec::SoAVec;
    ///
    /// assert_eq!(std::mem::size_of::<((), ())>(), 0);
    /// let v = SoAVec::<((), ())>::new();
    /// assert_eq!(v.capacity(), u32::MAX);
    /// ```
    #[inline]
    pub fn capacity(&self) -> u32 {
        self.buf.capacity()
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the given `Vec<T>`. The collection may reserve more space to
    /// speculatively avoid frequent reallocations. After calling `reserve`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    ///
    /// # Errors
    ///
    /// Returns an error if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// use soavec::soavec;
    ///
    /// let mut vec = soavec![(1u32, 1u32)].unwrap();
    /// vec.reserve(10).unwrap();
    /// assert!(vec.capacity() >= 11);
    /// ```
    pub fn reserve(&mut self, additional: u32) -> Result<(), AllocError> {
        self.buf.reserve(additional)
    }

    /// Appends an element to the back of a collection.
    ///
    /// # Errors
    ///
    /// Returns an error if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// use soavec::soavec;
    ///
    /// let mut vec = soavec![(1u32, 1u32), (2u32, 2u32)].unwrap();
    /// vec.push((3, 3)).unwrap();
    /// assert_eq!(vec.get(0), Some((&1, &1)));
    /// assert_eq!(vec.get(1), Some((&2, &2)));
    /// assert_eq!(vec.get(2), Some((&3, &3)));
    /// ```
    ///
    /// # Time complexity
    ///
    /// Takes amortized *O*(1) time. If the vector's length would exceed its
    /// capacity after the push, *O*(*capacity*) time is taken to copy the
    /// vector's elements to a larger allocation. This expensive operation is
    /// offset by the *capacity* *O*(1) insertions it allows.
    pub fn push(&mut self, value: T) -> Result<(), AllocError> {
        let len = self.len();
        if len == self.capacity() {
            self.buf.reserve(1)?;
        }

        // SAFETY: sure.
        unsafe {
            T::TupleRepr::write(
                self.buf.as_mut_ptr(),
                T::into_tuple(value),
                len,
                self.capacity(),
            )
        };
        // SAFETY: length cannot overflow due to reserve succeeding.
        unsafe { self.buf.set_len(self.len().unchecked_add(1)) };
        Ok(())
    }

    /// Removes the last element from a SoA vector and returns it, or [`None`]
    /// if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use soavec::soavec;
    ///
    /// let mut vec = soavec![(1, 1), (2, 2), (3, 3)].unwrap();
    /// assert_eq!(vec.pop(), Some((3, 3)));
    /// assert_eq!(vec.get(0), Some((&1, &1)));
    /// assert_eq!(vec.get(1), Some((&2, &2)));
    /// ```
    ///
    /// # Time complexity
    ///
    /// Takes *O*(1) time.
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        let len = self.len();
        if len == 0 {
            None
        } else {
            unsafe {
                self.buf.set_len(len - 1);
                core::hint::assert_unchecked(self.len() < self.capacity());
                Some(T::from_tuple(T::TupleRepr::read(
                    self.buf.as_ptr(),
                    self.len(),
                    self.capacity(),
                )))
            }
        }
    }

    /// Returns a reference to each field in T or `None` if out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use soavec::soavec;
    ///
    /// let v = soavec![(10, 10), (40, 40), (30, 30)].unwrap();
    /// assert_eq!(Some((&40, &40)), v.get(1));
    /// assert_eq!(None, v.get(3));
    /// ```
    #[inline]
    #[must_use]
    pub fn get(&self, index: u32) -> Option<T::Ref<'_>> {
        if self.len() <= index {
            // Over-indexing.
            return None;
        }
        let ptrs = unsafe { T::TupleRepr::get_pointers(self.buf.as_ptr(), index, self.capacity()) };
        Some(T::as_ref(PhantomData, ptrs))
    }

    /// Returns a mutable reference to each field in `T` or `None` if the index
    /// is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use soavec::soavec;
    ///
    /// let x = &mut soavec![(0, 0), (1, 1), (2, 2)].unwrap();
    ///
    /// if let Some((first, second)) = x.get_mut(1) {
    ///     *first = 42;
    ///     *second = 3;
    /// }
    /// assert_eq!(x.as_slice(), ([0, 42, 2].as_slice(), [0, 3, 2].as_slice()));
    /// ```
    #[inline]
    #[must_use]
    pub fn get_mut(&mut self, index: u32) -> Option<T::Mut<'_>> {
        if self.len() <= index {
            // Over-indexing.
            return None;
        }
        let ptrs =
            unsafe { T::TupleRepr::get_pointers(self.buf.as_mut_ptr(), index, self.capacity()) };
        Some(T::as_mut(PhantomData, ptrs))
    }

    /// Extracts a tuple of slices containing the entire vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use soavec::soavec;
    /// use std::io::{self, Write};
    ///
    /// let buffer = soavec![(1, 1), (2, 2), (3, 3), (5, 5), (8, 8)].unwrap();
    /// let (first, second) = buffer.as_slice();
    /// io::sink().write(first).unwrap();
    /// io::sink().write(second).unwrap();
    /// ```
    pub fn as_slice(&self) -> T::Slice<'_> {
        let ptrs = unsafe { T::TupleRepr::get_pointers(self.buf.as_ptr(), 0, self.capacity()) };
        let len = self.len();
        T::as_slice(PhantomData, ptrs, len)
    }

    /// Extracts a mutable slice of the entire vector.
    ///
    /// Equivalent to `&mut s[..]`.
    ///
    /// # Examples
    ///
    /// ```
    /// use soavec::soavec;
    /// use std::io::{self, Read};
    /// let mut buffer = soavec![(0, 0); 3].unwrap();
    /// let (first, second) = buffer.as_mut_slice();
    ///
    /// io::repeat(0b101).read_exact(first).unwrap();
    /// io::repeat(0b010).read_exact(second).unwrap();
    /// ```
    pub fn as_mut_slice(&mut self) -> T::SliceMut<'_> {
        let ptrs = unsafe { T::TupleRepr::get_pointers(self.buf.as_ptr(), 0, self.capacity()) };
        let len = self.len();
        T::as_mut_slice(PhantomData, ptrs, len)
    }

    /// Retains only the elements specified by the predicate, passing a mutable
    /// reference to it.
    ///
    /// In other words, remove all elements `e` such that `f(T::Mut)` returns
    /// `false`. This method operates in place, visiting each element exactly
    /// once in the original order, and preserves the order of the retained
    /// elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use soavec::soavec;
    /// let mut vec = soavec![(1, 1), (2, 2), (3, 3), (4, 4)].unwrap();
    /// vec.retain_mut(|x| if *x.0 <= 3 {
    ///     *x.1 += 1;
    ///     true
    /// } else {
    ///     false
    /// });
    /// assert_eq!(vec.len(), 3);
    /// assert_eq!(vec.get(0), Some((&1, &2)));
    /// assert_eq!(vec.get(1), Some((&2, &3)));
    /// assert_eq!(vec.get(2), Some((&3, &4)));
    /// ```
    pub fn retain_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(T::Mut<'_>) -> bool,
    {
        let original_len = self.len();

        if original_len == 0 {
            // Empty case: explicit return allows better optimization, vs letting compiler infer it
            return;
        }

        // Avoid double drop if the drop guard is not executed,
        // since we may make some holes during the process.
        unsafe { self.buf.set_len(0) };

        // Vec: [Kept, Kept, Hole, Hole, Hole, Hole, Unchecked, Unchecked]
        //      |<-              processed len   ->| ^- next to check
        //                  |<-  deleted cnt     ->|
        //      |<-              original_len                          ->|
        // Kept: Elements which predicate returns true on.
        // Hole: Moved or dropped element slot.
        // Unchecked: Unchecked valid elements.
        //
        // This drop guard will be invoked when predicate or `drop` of element panicked.
        // It shifts unchecked elements to cover holes and `set_len` to the correct length.
        // In cases when predicate and `drop` never panick, it will be optimized out.
        struct BackshiftOnDrop<'a, T: SoAble> {
            v: &'a mut SoAVec<T>,
            processed_len: u32,
            deleted_cnt: u32,
            original_len: u32,
        }

        impl<T: SoAble> Drop for BackshiftOnDrop<'_, T> {
            fn drop(&mut self) {
                if self.deleted_cnt > 0 {
                    let cap = self.v.buf.capacity();
                    // SAFETY: Trailing unchecked items must be valid since we never touch them.
                    unsafe {
                        T::TupleRepr::copy(
                            T::TupleRepr::get_pointers(
                                self.v.buf.as_ptr(),
                                self.processed_len,
                                cap,
                            ),
                            T::TupleRepr::get_pointers(
                                self.v.buf.as_mut_ptr(),
                                self.processed_len - self.deleted_cnt,
                                cap,
                            ),
                            self.original_len - self.processed_len,
                        );
                    }
                }
                // SAFETY: After filling holes, all items are in contiguous memory.
                unsafe {
                    self.v.buf.set_len(self.original_len - self.deleted_cnt);
                }
            }
        }

        let mut g = BackshiftOnDrop {
            v: self,
            processed_len: 0,
            deleted_cnt: 0,
            original_len,
        };

        fn process_loop<F, T: SoAble, const DELETED: bool>(
            original_len: u32,
            f: &mut F,
            g: &mut BackshiftOnDrop<'_, T>,
        ) where
            F: FnMut(T::Mut<'_>) -> bool,
        {
            while g.processed_len != original_len {
                // SAFETY: Unchecked element must be valid.
                let cur_ptrs = unsafe {
                    T::TupleRepr::get_pointers(
                        g.v.buf.as_mut_ptr(),
                        g.processed_len,
                        g.v.capacity(),
                    )
                };
                let cur = T::as_mut(PhantomData, cur_ptrs);
                if !f(cur) {
                    let cur_len = g.processed_len;
                    // Advance early to avoid double drop if `drop_in_place` panicked.
                    g.processed_len += 1;
                    g.deleted_cnt += 1;
                    // SAFETY: We never touch this element again after dropped.
                    if T::MUST_DROP_AS_SELF {
                        // T must be dropped as T; we have to read out each T from the
                        // SoAVec and drop them individually.
                        let ptr = g.v.buf.as_mut_ptr();
                        let cap = g.v.buf.capacity();
                        // SAFETY: cur was moved to f and its backing memory
                        // will never be accessed again.
                        let _ = T::from_tuple(unsafe { T::TupleRepr::read(ptr, cur_len, cap) });
                    } else if const { core::mem::needs_drop::<T::TupleRepr>() } {
                        // SAFETY: cur was moved to f and its backing memory
                        // will never be accessed again.
                        unsafe { T::TupleRepr::drop_in_place(cur_ptrs, 1) };
                    }
                    // We already advanced the counter.
                    if DELETED {
                        continue;
                    } else {
                        break;
                    }
                }
                if DELETED {
                    // SAFETY: `deleted_cnt` > 0, so the hole slot must not overlap with current element.
                    // We use copy for move, and never touch this element again.
                    unsafe {
                        let hole_slot = T::TupleRepr::get_pointers(
                            g.v.buf.as_mut_ptr(),
                            g.processed_len - g.deleted_cnt,
                            g.v.buf.capacity(),
                        );
                        T::TupleRepr::copy(cur_ptrs, hole_slot, 1);
                    }
                }
                g.processed_len += 1;
            }
        }

        // Stage 1: Nothing was deleted.
        process_loop::<F, T, false>(original_len, &mut f, &mut g);

        // Stage 2: Some elements were deleted.
        process_loop::<F, T, true>(original_len, &mut f, &mut g);

        // All item are processed. This can be optimized to `set_len` by LLVM.
        drop(g);
    }

    /// Removes and returns the element at position `index` within the vector,
    /// shifting all elements after it to the left.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use soavec::soavec;
    ///
    /// let mut v = soavec![('a', 'a'), ('b', 'b'), ('c', 'c')].unwrap();
    /// assert_eq!(v.remove(1), ('b', 'b'));
    /// assert_eq!(v.len(), 2);
    /// ```
    pub fn remove(&mut self, index: u32) -> T {
        let len = self.len();

        if index >= len {
            panic!("removal index (is {index}) should be < len (is {len})");
        }

        let cap = self.buf.capacity();
        let ptr = self.buf.as_ptr();

        unsafe {
            // Read the value out before we overwrite its memory.
            let result = T::from_tuple(T::TupleRepr::read(ptr, index, cap));
            // Shift down everything after it.
            if index < len - 1 {
                T::TupleRepr::copy(
                    T::TupleRepr::get_pointers(ptr, index + 1, cap),
                    T::TupleRepr::get_pointers(ptr, index, cap),
                    len - index - 1,
                );
            }
            // Update the length.
            self.buf.set_len(len - 1);

            result
        }
    }

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after it to the right.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// use soavec::soavec;
    ///
    /// let mut vec = soavec![('a', 'b'), ('c', 'd')].unwrap();
    /// vec.insert(1, ('x', 'y')).unwrap();
    /// assert_eq!(vec.len(), 3);
    /// ```
    pub fn insert(&mut self, index: u32, element: T) -> Result<(), AllocError> {
        let _ = self.insert_mut(index, element)?;

        Ok(())
    }

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after it to the right, and returning a reference to the new
    /// element.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// use soavec::soavec;
    ///
    /// let mut vec = soavec![(1, 1), (3, 3), (5, 5), (7, 7), (9, 9)].unwrap();
    /// let (mut x1, _) = vec.insert_mut(3, (6, 6)).unwrap();
    /// *x1 += 1;
    /// assert_eq!(vec.len(), 6);
    /// assert_eq!(vec.get(3), Some((&7, &6)));
    /// ```
    pub fn insert_mut(&mut self, index: u32, element: T) -> Result<T::Mut<'_>, AllocError> {
        let len = self.len();

        if index > len {
            panic!("insertion index (is {index}) should be <= len (is {len})");
        }

        if len == self.capacity() {
            // Make sure we have space to one more element.
            self.buf.reserve(1)?;
        }

        let ptr = self.buf.as_mut_ptr();
        let cap = self.capacity();

        unsafe {
            if index < len {
                // Shift elements to the right.
                let src = T::TupleRepr::get_pointers(ptr, index, cap);
                let dst = T::TupleRepr::get_pointers(ptr, (index) + 1, cap);
                T::TupleRepr::copy(src, dst, len - (index));
            }

            // Write the new element.
            let src = T::into_tuple(element);
            T::TupleRepr::write(ptr, src, index, cap);

            // Update length.
            self.buf.set_len(self.len().unchecked_add(1));

            let ptrs = T::TupleRepr::get_pointers(ptr, index, cap);
            Ok(T::as_mut(PhantomData, ptrs))
        }
    }

    /// Clears the vector, removing all values.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use soavec::soavec;
    ///
    /// let mut vec = soavec![(1, 1), (2, 2), (3, 3)].unwrap();
    /// vec.clear();
    /// assert_eq!(vec.len(), 0);
    /// ```
    pub fn clear(&mut self) {
        let len = self.len();
        if len == 0 {
            return;
        }

        let ptr = self.buf.as_mut_ptr();
        let cap = self.capacity();

        unsafe {
            self.buf.set_len(0);
        };
        self.drop_in_place(ptr, cap, len);
    }

    // Drops the items in place without deallocating the buffer.
    fn drop_in_place(&mut self, ptr: NonNull<u8>, cap: u32, len: u32) {
        if T::MUST_DROP_AS_SELF {
            for i in 0..len {
                // SAFETY: reads each value out without altering the backing
                // memory; using the backing memory may violate memory safety
                // after this but we are about to deallocate it afterwards.
                let _ = T::from_tuple(unsafe { T::TupleRepr::read(ptr, i, cap) });
            }
        } else if const { core::mem::needs_drop::<T::TupleRepr>() } {
            // SAFETY: buffer is still allocated to capacity, contains len
            // items.
            unsafe { T::TupleRepr::drop_in_place(T::TupleRepr::get_pointers(ptr, 0, cap), len) };
        }
    }
}

impl<T: SoAble> Drop for SoAVec<T> {
    fn drop(&mut self) {
        let len = self.len();
        let cap = self.capacity();
        let ptr = self.buf.as_mut_ptr();
        self.drop_in_place(ptr, cap, len);
        // RawSoAVec's Drop impl deallocates the buffer.
    }
}

impl<T: SoAble> core::default::Default for SoAVec<T> {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
}

impl<T: SoAble> core::fmt::Debug for SoAVec<T>
where
    for<'a> T::Slice<'a>: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Debug::fmt(&self.as_slice(), f)
    }
}

impl<T: SoAble> AsRef<SoAVec<T>> for SoAVec<T> {
    #[inline(always)]
    fn as_ref(&self) -> &SoAVec<T> {
        self
    }
}

impl<T: SoAble> AsMut<SoAVec<T>> for SoAVec<T> {
    #[inline(always)]
    fn as_mut(&mut self) -> &mut SoAVec<T> {
        self
    }
}

#[cfg(test)]
mod tests {
    use core::marker::PhantomData;

    use crate as soavec;
    use crate::{SoATuple, SoAVec, SoAble};

    #[test]
    fn basic_usage() {
        use soavec_derive::SoAble;

        #[repr(C)]
        #[derive(Debug, Clone, Copy, PartialEq, Eq, SoAble)]
        struct Foo {
            a: u64,
            b: u32,
        }

        /// Conceptually; this is what we're doing here.
        const _ARRAY: [Foo; 16] = [Foo { a: 0, b: 1 }; 16];
        const _SOA_ARRAY: ([u64; 16], [u32; 16]) = ([0; 16], [1; 16]);

        let mut foo = SoAVec::<Foo>::with_capacity(16).unwrap();
        foo.push(Foo { a: 0, b: 2 }).unwrap();
        let first = foo.get(0).unwrap();
        assert_eq!(first.a, &0);
        assert_eq!(first.b, &2);

        let first = foo.get_mut(0).unwrap();
        *first.a = 52;
        *first.b = 66;
        assert_eq!(first.a, &52);
        assert_eq!(first.b, &66);

        let first = foo.get(0).unwrap();
        assert_eq!(first.a, &52);
        assert_eq!(first.b, &66);

        foo.reserve(32).unwrap();
        let first = foo.get(0).unwrap();
        assert_eq!(first.a, &52);
        assert_eq!(first.b, &66);

        foo.push(Foo { a: 4, b: 8 }).unwrap();
        let FooSlice {
            a: a_slice,
            b: b_slice,
        } = foo.as_slice();
        assert_eq!(a_slice.len(), b_slice.len());
        assert_eq!(a_slice.len(), 2);
        assert_eq!(a_slice, &[52, 4]);
        assert_eq!(b_slice, &[66, 8]);
        assert_eq!(foo.pop(), Some(Foo { a: 4, b: 8 }));
    }

    #[test]
    fn basic_usage_with_lifetime() {
        use soavec_derive::SoAble;

        #[repr(C)]
        #[derive(Debug, Clone, Copy, SoAble)]
        struct Foo<'a> {
            a: &'a u64,
            b: &'a u32,
        }

        let mut foo = SoAVec::<Foo>::with_capacity(16).unwrap();
        foo.push(Foo { a: &0, b: &2 }).unwrap();
        let first = foo.get(0).unwrap();
        assert_eq!(first.a, &&0);
        assert_eq!(first.b, &&2);

        let first = foo.get_mut(0).unwrap();
        *first.a = &52;
        *first.b = &66;
        assert_eq!(first.a, &&52);
        assert_eq!(first.b, &&66);

        let first = foo.get(0).unwrap();
        assert_eq!(first.a, &&52);
        assert_eq!(first.b, &&66);

        foo.reserve(32).unwrap();
        let first = foo.get(0).unwrap();
        assert_eq!(first.a, &&52);
        assert_eq!(first.b, &&66);

        foo.push(Foo { a: &4, b: &8 }).unwrap();
        let FooSlice {
            a: a_slice,
            b: b_slice,
        } = foo.as_slice();
        assert_eq!(a_slice.len(), b_slice.len());
        assert_eq!(a_slice.len(), 2);
        assert_eq!(a_slice, &[&52, &4]);
        assert_eq!(b_slice, &[&66, &8]);
    }

    #[test]
    fn more_basic_usage() {
        use soavec_derive::SoAble;

        #[repr(C)]
        #[derive(Debug, Clone, Copy, SoAble)]
        struct Bar {
            a: u64,
            b: u32,
            c: u8,
        }

        let mut bar = SoAVec::<Bar>::with_capacity(16).unwrap();
        bar.reserve(32).unwrap();
        bar.push(Bar { a: 0, b: 2, c: 255 }).unwrap();
        let first = bar.get(0).unwrap();
        assert_eq!(first.a, &0);
        assert_eq!(first.b, &2);
        assert_eq!(first.c, &255);
    }

    #[test]
    fn clear_resets_len() {
        use soavec_derive::SoAble;

        #[repr(C)]
        #[derive(SoAble)]
        struct Foo {
            a: u32,
            b: u64,
        }

        let mut foo = SoAVec::<Foo>::with_capacity(5).unwrap();
        foo.push(Foo { a: 2, b: 0 }).unwrap();
        assert_eq!(foo.len(), 1);

        foo.clear();

        assert_eq!(foo.len(), 0);

        foo.push(Foo { a: 3, b: 0 }).unwrap();
        assert_eq!(foo.len(), 1);
    }

    #[test]
    fn clear_does_not_change_capacity() {
        use soavec_derive::SoAble;

        #[repr(C)]
        #[derive(SoAble)]
        struct Foo {
            a: u32,
            b: u64,
        }

        let mut foo = SoAVec::<Foo>::with_capacity(5).unwrap();
        let cap = foo.capacity();
        foo.push(Foo { a: 2, b: 0 }).unwrap();
        assert_eq!(foo.len(), 1);
        assert_eq!(foo.capacity(), cap);

        foo.clear();

        assert_eq!(foo.len(), 0);
        assert_eq!(foo.capacity(), cap);

        foo.push(Foo { a: 3, b: 0 }).unwrap();
        assert_eq!(foo.len(), 1);
        assert_eq!(foo.capacity(), cap);
    }

    #[test]
    fn clears_all_elements() {
        use soavec_derive::SoAble;
        use std::rc::Rc;

        #[repr(C)]
        #[derive(Debug, Clone, SoAble)]
        struct Foo {
            b: Rc<u32>,
            a: u64,
        }

        let rc1 = Rc::new(2u32);

        let mut foo = SoAVec::<Foo>::with_capacity(5).unwrap();
        foo.push(Foo {
            b: rc1.clone(),
            a: 0,
        })
        .unwrap();

        // `rc1` is referenced two times. Once in `rc1` and once in `foo`.
        assert_eq!(Rc::strong_count(&rc1), 2);

        foo.clear();

        assert_eq!(foo.len(), 0);
        // After clearing, `rc1` should only be referenced once in `rc1`.
        assert_eq!(Rc::strong_count(&rc1), 1);
    }

    #[test]
    fn clears_all_elements_with_droppable() {
        #[repr(C)]
        struct LoudDrop {
            a: (),
            b: (),
        }

        static mut DROP_COUNT: usize = 0;

        impl Drop for LoudDrop {
            fn drop(&mut self) {
                println!("LoudDrop");
                // SAFETY: test is entirely single-threaded.
                unsafe {
                    DROP_COUNT += 1;
                }
            }
        }

        // SAFETY: No internal invariants on fields.
        unsafe impl SoAble for LoudDrop {
            type TupleRepr = ((), ());

            const MUST_DROP_AS_SELF: bool = true;

            type Ref<'a>
                = (&'a (), &'a ())
            where
                Self: 'a;

            type Mut<'a>
                = (&'a mut (), &'a mut ())
            where
                Self: 'a;

            type Slice<'a>
                = (&'a [()], &'a [()])
            where
                Self: 'a;

            type SliceMut<'a>
                = (&'a mut [()], &'a mut [()])
            where
                Self: 'a;

            fn into_tuple(value: Self) -> Self::TupleRepr {
                core::mem::forget(value);
                ((), ())
            }

            fn from_tuple(_value: Self::TupleRepr) -> Self {
                Self { a: (), b: () }
            }

            fn as_ref<'a>(
                _: PhantomData<&'a Self>,
                value: <Self::TupleRepr as SoATuple>::Pointers,
            ) -> Self::Ref<'a> {
                unsafe { (value.0.as_ref(), value.1.as_ref()) }
            }

            fn as_mut<'a>(
                _: PhantomData<&'a mut Self>,
                mut value: <Self::TupleRepr as SoATuple>::Pointers,
            ) -> Self::Mut<'a> {
                unsafe { (value.0.as_mut(), value.1.as_mut()) }
            }

            fn as_slice<'a>(
                _: PhantomData<&'a Self>,
                value: <Self::TupleRepr as SoATuple>::Pointers,
                len: u32,
            ) -> Self::Slice<'a> {
                unsafe {
                    (
                        core::slice::from_raw_parts(value.0.as_ptr(), len as usize),
                        core::slice::from_raw_parts(value.1.as_ptr(), len as usize),
                    )
                }
            }

            fn as_mut_slice<'a>(
                _: PhantomData<&'a mut Self>,
                value: <Self::TupleRepr as SoATuple>::Pointers,
                len: u32,
            ) -> Self::SliceMut<'a> {
                unsafe {
                    (
                        core::slice::from_raw_parts_mut(value.0.as_ptr(), len as usize),
                        core::slice::from_raw_parts_mut(value.1.as_ptr(), len as usize),
                    )
                }
            }
        }

        let mut foo = SoAVec::<LoudDrop>::with_capacity(16).unwrap();
        foo.push(LoudDrop { a: (), b: () }).unwrap();
        foo.push(LoudDrop { a: (), b: () }).unwrap();

        assert_eq!(foo.len(), 2);

        foo.clear();

        assert_eq!(foo.len(), 0);
        assert_eq!(unsafe { DROP_COUNT }, 2);
    }

    #[test]
    fn basic_usage_with_bad_alignment() {
        use soavec_derive::SoAble;

        #[repr(C)]
        #[derive(Debug, Clone, Copy, SoAble)]
        struct Foo {
            b: u32,
            a: u64,
        }

        #[repr(C)]
        #[derive(Debug, Clone, Copy, SoAble)]
        struct Bar {
            c: u8,
            b: u32,
            a: u64,
        }

        let mut foo = SoAVec::<Foo>::with_capacity(5).unwrap();
        foo.reserve(9).unwrap();
        foo.push(Foo { b: 2, a: 0 }).unwrap();
        let first = foo.get(0).unwrap();
        assert_eq!(first.b, &2);
        assert_eq!(first.a, &0);
        // let a_0: &u64 = foo.get_a(0);
        // let a_0: &u32 = foo.get_b(0);
        // let a_n: &[u64] = foo.get_all_a();

        let mut bar = SoAVec::<Bar>::with_capacity(7).unwrap();
        bar.reserve(11).unwrap();
        bar.push(Bar { c: 255, b: 2, a: 0 }).unwrap();
        let first = bar.get(0).unwrap();
        assert_eq!(first.c, &255);
        assert_eq!(first.b, &2);
        assert_eq!(first.a, &0);
    }

    #[test]
    fn insert_and_insert_mut() {
        let mut vec = SoAVec::<(u32, u32)>::new();
        vec.push((1, 10)).unwrap();
        vec.push((3, 30)).unwrap();

        let (first, second) = vec.insert_mut(1, (2, 20)).unwrap();
        *first += 10;
        *second += 5;

        vec.insert(0, (0, 0)).unwrap();

        let slice = vec.as_slice();
        assert_eq!(slice.0, &[0, 1, 12, 3]);
        assert_eq!(slice.1, &[0, 10, 25, 30]);
    }

    #[test]
    fn insert_grows_capacity() {
        let mut vec = SoAVec::<(u32, u32)>::with_capacity(2).unwrap();
        assert_eq!(vec.capacity(), 2);

        vec.push((1, 10)).unwrap();
        vec.push((2, 20)).unwrap();
        assert_eq!(vec.capacity(), 2);

        // Should grow capacity.
        vec.insert(1, (3, 30)).unwrap();
        assert!(vec.capacity() >= 3);

        let slice = vec.as_slice();
        assert_eq!(slice.0, &[1, 3, 2]);
        assert_eq!(slice.1, &[10, 30, 20]);
    }

    #[test]
    fn basic_usage_with_zst() {
        use soavec_derive::SoAble;

        #[repr(C)]
        #[derive(Debug, Clone, Copy, SoAble)]
        struct Foo {
            b: (),
            a: u32,
        }

        #[repr(C)]
        #[derive(Debug, Clone, Copy, SoAble)]
        struct Bar {
            c: u8,
            b: (),
            a: u64,
        }

        #[repr(C)]
        #[derive(Debug, Clone, Copy, SoAble)]
        struct Baz {
            c: (),
            b: (),
            a: (),
        }

        let mut foo = SoAVec::<Foo>::with_capacity(5).unwrap();
        foo.reserve(9).unwrap();
        foo.push(Foo { a: 2, b: () }).unwrap();
        let first = foo.get(0).unwrap();
        assert_eq!(first.b, &());
        assert_eq!(first.a, &2);

        let mut bar = SoAVec::<Bar>::with_capacity(7).unwrap();
        bar.reserve(11).unwrap();
        bar.push(Bar {
            c: 255,
            b: (),
            a: 0,
        })
        .unwrap();
        let first = bar.get(0).unwrap();
        assert_eq!(first.c, &255);
        assert_eq!(first.b, &());
        assert_eq!(first.a, &0);

        let mut baz = SoAVec::<Baz>::with_capacity(7).unwrap();
        baz.reserve(11).unwrap();
        baz.push(Baz {
            a: (),
            b: (),
            c: (),
        })
        .unwrap();
        let first = baz.get(0).unwrap();
        assert_eq!(first.a, &());
        assert_eq!(first.b, &());
        assert_eq!(first.c, &());
    }

    #[test]
    fn droppable_types() {
        use soavec_derive::SoAble;

        #[repr(C)]
        #[derive(Debug, Clone, SoAble)]
        struct Foo {
            a: Vec<u64>,
            b: Box<u32>,
        }

        let mut foo = SoAVec::<Foo>::with_capacity(16).unwrap();
        foo.push(Foo {
            a: vec![0],
            b: Box::new(2),
        })
        .unwrap();
        let first = foo.get(0).unwrap();
        assert_eq!(first.a, &[0]);
        assert_eq!(**first.b, 2);

        let first = foo.get_mut(0).unwrap();
        first.a.push(52);
        *first.b = Box::new(66u32);
        assert_eq!(first.a, &[0, 52]);
        assert_eq!(**first.b, 66u32);

        let first = foo.get(0).unwrap();
        assert_eq!(first.a, &[0, 52]);
        assert_eq!(**first.b, 66u32);

        foo.reserve(32).unwrap();
        let first = foo.get(0).unwrap();
        assert_eq!(first.a, &[0, 52]);
        assert_eq!(**first.b, 66u32);

        foo.push(Foo {
            a: vec![4],
            b: Box::new(8),
        })
        .unwrap();
        let FooSlice {
            a: a_slice,
            b: b_slice,
        } = foo.as_slice();
        assert_eq!(a_slice.len(), b_slice.len());
        assert_eq!(a_slice.len(), 2);
        assert_eq!(a_slice, &[vec![0, 52], vec![4]]);
        assert_eq!(b_slice, &[Box::new(66), Box::new(8)]);
    }

    #[test]
    fn must_drop_as_self_type() {
        #[repr(C)]
        struct LoudDrop {
            a: (),
            b: (),
        }

        static mut DROP_COUNT: usize = 0;

        impl Drop for LoudDrop {
            fn drop(&mut self) {
                println!("LoudDrop");
                // SAFETY: test is entirely single-threaded.
                unsafe {
                    DROP_COUNT += 1;
                }
            }
        }

        // SAFETY: No internal invariants on fields.
        unsafe impl SoAble for LoudDrop {
            type TupleRepr = ((), ());

            const MUST_DROP_AS_SELF: bool = true;

            type Ref<'a>
                = (&'a (), &'a ())
            where
                Self: 'a;

            type Mut<'a>
                = (&'a mut (), &'a mut ())
            where
                Self: 'a;

            type Slice<'a>
                = (&'a [()], &'a [()])
            where
                Self: 'a;

            type SliceMut<'a>
                = (&'a mut [()], &'a mut [()])
            where
                Self: 'a;

            fn into_tuple(value: Self) -> Self::TupleRepr {
                core::mem::forget(value);
                ((), ())
            }

            fn from_tuple(_value: Self::TupleRepr) -> Self {
                Self { a: (), b: () }
            }

            fn as_ref<'a>(
                _: PhantomData<&'a Self>,
                value: <Self::TupleRepr as SoATuple>::Pointers,
            ) -> Self::Ref<'a> {
                unsafe { (value.0.as_ref(), value.1.as_ref()) }
            }

            fn as_mut<'a>(
                _: PhantomData<&'a mut Self>,
                mut value: <Self::TupleRepr as SoATuple>::Pointers,
            ) -> Self::Mut<'a> {
                unsafe { (value.0.as_mut(), value.1.as_mut()) }
            }

            fn as_slice<'a>(
                _: PhantomData<&'a Self>,
                value: <Self::TupleRepr as SoATuple>::Pointers,
                len: u32,
            ) -> Self::Slice<'a> {
                unsafe {
                    (
                        core::slice::from_raw_parts(value.0.as_ptr(), len as usize),
                        core::slice::from_raw_parts(value.1.as_ptr(), len as usize),
                    )
                }
            }

            fn as_mut_slice<'a>(
                _: PhantomData<&'a mut Self>,
                value: <Self::TupleRepr as SoATuple>::Pointers,
                len: u32,
            ) -> Self::SliceMut<'a> {
                unsafe {
                    (
                        core::slice::from_raw_parts_mut(value.0.as_ptr(), len as usize),
                        core::slice::from_raw_parts_mut(value.1.as_ptr(), len as usize),
                    )
                }
            }
        }

        let mut foo = SoAVec::<LoudDrop>::with_capacity(16).unwrap();
        foo.push(LoudDrop { a: (), b: () }).unwrap();
        let _first = foo.get(0).unwrap();
        drop(foo);
        assert_eq!(
            unsafe { DROP_COUNT },
            1,
            "should have dropped a single LoudDrop item"
        );
    }

    #[test]
    fn remove_at_index() {
        use soavec_derive::SoAble;

        #[repr(C)]
        #[derive(Debug, Clone, Copy, PartialEq, Eq, SoAble)]
        struct Foo {
            a: u64,
            b: u32,
        }

        let mut foo = SoAVec::<Foo>::with_capacity(16).unwrap();
        for i in 0..10 {
            foo.push(Foo { a: i, b: i as u32 }).unwrap()
        }

        assert_eq!(foo.len(), 10);

        let removed = foo.remove(4);
        assert_eq!(removed, Foo { a: 4, b: 4 });
        assert_eq!(foo.len(), 9);
    }
}
