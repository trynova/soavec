// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use core::{
    alloc::{Layout, LayoutError},
    marker::PhantomData,
    ptr::{NonNull, drop_in_place},
};

/// Used for defining the format and API of a type stored in `SoAVec` in a
/// Struct-of-Arrays format.
///
/// This trait defines a representation for the implementing type that the
/// `SoAVec` recognises and knows how to store, and the conversions to and from
/// said type. Additionally, the trait defines the necessary references types
/// for exposing the type's data when borrowed from the `SoAVec`.
///
/// For simple structs that are only a collection of individual fields, the
/// `soable!` macro can be used to easily map the fields into an equivalent
/// tuple representation. For more involved types such as structs with safety
/// invariants, unions, or enums the trait should be implemented manually with
/// all the necessary safety requirements considered.
///
/// # Safety
///
/// 1. The type must be safely droppable field-wise, **or** the
///    `MUST_DROP_AS_SELF` boolean must be set. If it is set, `SoAVec`
///    guarantees that each dropped entry in the Struct-of-Arrays is read out
///    onto the stack and dropped as `Self`.
/// 2. The type's internal invariants must be upheld by the `SoAble::Ref`,
///    `SoAble::Mut`, `SoAble::Slice`, and `SoAble::SliceMut` types.
///    Specifically, this means that if mutating a given field individually
///    could break invariants, then that field's (mutable) reference must not
///    be exposed by any of the SoAble reference types.
///
/// # When to manually implement `SoAble`
///
/// If your type is an enum, a union, or a struct with internal invariants then
/// a manual implementation of `SoAble` is required. A direct tuple
/// representation of any of these would allow internal invariants to be
/// broken through the SoAble reference types.
///
/// ## `SoAble` enums
///
/// For enums the Struct-of-Arrays format is likely to be
/// `(Discriminant, union Payload)`; the `Discimrinant` can be extracted
/// directly using `std::mem::discriminant` but the payload needs pattern
/// matching to extract and place inside the payload union. It is safe to
/// expose the payload union directly through the SoAble reference types
/// because accessing its data is unsafe (as a union); thus the implementation
/// of `SoAble` can be fairly straight-forward. Alternatively, a safe API
/// can be implemented to abstract over the discriminant-payload reference
/// pair.
///
/// ## `SoAble` unions
///
/// The representation is entirely up to and decidable by the implementor. If
/// you're thinking about this, then there's a good chance you should rather
/// move some shared data out of the union.
///
/// ## `SoAble` structs with internal invariants
///
/// A struct with internal invariants must manually implement `SoAble` such
/// that the exposed SoAble reference types cannot violate those internal
/// invariants.
///
/// ## Types with custom `Drop`
///
/// Any type that has a custom `Drop` needs to manually implement `SoAble`. The
/// conversion between `Self` and `Self::TupleRepr` should then move the `Self`
/// into `ManuallyDrop`, use exclusive references to the individual fields to
/// `std::ptr::read` the values out of `Self` and move the results into
/// `Self::TupleRepr`. Finally, let the `ManuallyDrop<Self>` to go out of scope
/// without dropping its contents.
///
/// Use `NEEDS_DROP` to indiciate if `Self` needs to be reconstructed for
/// dropping purposes.
///
/// # Fallibility
///
/// **This trait's methods should never unexpectedly fail**. Failure can be
/// extremely confusing. In the majority of uses it should be infallible,
/// though it may be acceptable to panic if the type or methods is misused
/// through programmer error, for example.
///
/// However, infallibility is not enforced and therefore not guaranteed.
/// As such, `unsafe` code should not rely on infallibility in general for
/// soundness.
///
/// # Examples
pub unsafe trait SoAble: Sized {
    /// Representation of the SoAble type in a Struct-of-Arrays friendly tuple
    /// form.
    ///
    /// The tuple does not need to strictly follow the field split or ordering
    /// of the original type, though that is generally a good starting point.
    ///
    /// The tuple form is identified by the SoATuple trait which is a sealed
    /// trait implemented by the crate for a select group of generic tuples.
    /// The form is thus required to match one of these presets.
    type TupleRepr: SoATuple;

    /// Set to true if the type must read out of the `SoAVec` and dropped as
    /// `Self` when deallocating.
    ///
    /// If the type's fields can be dropped directly in the Struct-of-Arrays
    /// format then this value should be false.
    ///
    /// # Examples
    ///
    /// A simple struct containing fields that required drop themselves but are
    /// not indvidually split up in the Struct-of-Arrays format can be dropped
    /// directly in the Struct-of-Arrays format.
    ///
    /// ```rust,ignore
    /// struct Simple {
    ///   a: Vec<u32>,
    ///   b: Box<u64>,
    /// }
    /// soable!(Simple { a: Vec<u32>, b: Box<u64> });
    /// ```
    ///
    /// A struct whose fields are not individually droppable must be read out
    /// of the `SoAVec` and dropped as `Self`.
    ///
    /// ```rust,ignore
    /// struct Complex {
    ///   ptr: NonNull<u32>,
    ///   len: u32,
    ///   cap: u32,
    /// }
    ///
    /// impl Drop for Complex {
    ///   fn drop(&mut self) {
    ///     // Note: deallocation requires access to ptr and cap.
    ///     core::mem::deallocate(self.ptr, array_layout(self.cap, Layout::new::<u32>()));
    ///   }
    /// }
    ///
    /// impl Soable for Complex {
    ///   const MUST_DROP_AS_SELF: bool = true;
    /// }
    /// ```
    ///
    /// f.ex. a field containing a `Vec` can be dropped in the Struct-of-Arrays
    /// format while a `Vec` split into two or three arrays would need to be
    /// read out and dropped as `Vec`.
    const MUST_DROP_AS_SELF: bool = false;

    /// Representation of the SoAble type as a group of references borrowed
    /// from the Struct-of-Arrays.
    ///
    /// Generally this will be a tuple of references matching the TupleRepr but
    /// in cases of types that split apart fields that have interconnected
    /// safety requirements that could be violated using shared references to
    /// individual fields, this type may be chosen to expose a safe interface
    /// over the group of field references.
    ///
    /// # Examples
    ///
    /// If a hypothetical `AtomicVec` was placed inside a `SoAVec` and shared
    /// references to its fields were exposed, then the `SoAVec` API would
    /// allow direct access to the `len` and `cap` fields that could be then
    /// used to mutate those without corresponding changes to `ptr`.
    ///
    /// In this case, the `AtomicVec` should use a different `Ref` type that
    /// does not allow such mutations to occur.
    ///
    /// ```rust,ignore
    /// struct AtomicVecSoaRef<'a, T> {
    ///   ptr: &'a AtomicPtr<T>,
    ///   cap: &'a AtomicUsize,
    ///   len: &'a AtomicUsize,
    /// }
    ///
    /// impl<T> SoAble for AtomicVec<T> {
    ///   type Ref<'a> = AtomicVecSoARef<'a, T> where Self: 'a;
    /// }
    /// ```
    type Ref<'a>: Copy
    where
        Self: 'a;

    /// Representation of the SoAble type as a group of exclusive references
    /// borrowed from the Struct-of-Arrays.
    ///
    /// Generally this will be a tuple of exclusive references matching the
    /// TupleRepr but in cases of types that split apart fields that have
    /// interconnected safety requirements that could be violated using
    /// exclusive references to individual fields, this type may be chosen to
    /// expose a safe interface over the group of exclusive field references.
    ///
    /// # Examples
    ///
    /// If a `Vec` was placed inside a `SoAVec` and exclusive references to its
    /// fields were exposed, then the `SoAVec` API would allow direct access to
    /// the `len` and `cap` fields that could be then used to mutate those
    /// without corresponding changes to `ptr`.
    ///
    /// In this case, the `Vec` should use a different `Mut` type that does not
    /// allow such mutations to occur.
    ///
    /// ```rust,ignore
    /// struct VecSoaRef<'a, T> {
    ///   ptr: &'a *mut T,
    ///   cap: &'a usize,
    ///   len: &'a usize,
    /// }
    ///
    /// impl<T> SoAble for AtomicVec<T> {
    ///   type Ref<'a> = VecSoARef<'a, T> where Self: 'a;
    /// }
    /// ```
    type Mut<'a>
    where
        Self: 'a;

    /// Representation of a group of the SoAble types as a group of slices
    /// borrowed from the Struct-of-Arrays.
    ///
    /// Generally this will be a tuple of slices matching the TupleRepr but
    /// in cases of types that split apart fields that have interconnected
    /// safety requirements that could be violated using shared references to
    /// individual fields, this type may be chosen to expose a safe interface
    /// over the group of field slices.
    type Slice<'a>: Copy
    where
        Self: 'a;

    /// Representation of a group of the SoAble types as a group of slices
    /// borrowed from the Struct-of-Arrays.
    ///
    /// Generally this will be a tuple of slices matching the TupleRepr but
    /// in cases of types that split apart fields that have interconnected
    /// safety requirements that could be violated using shared references to
    /// individual fields, this type may be chosen to expose a safe interface
    /// over the group of field slices.
    type SliceMut<'a>
    where
        Self: 'a;

    /// Take ownership of Self and convert to a tuple representation. The
    /// result will immediately be pushed into the SoAVec, which has already
    /// been checked to have space for the new item.
    ///
    /// ## Safety
    ///
    /// This method should never fail. The SoAVec guarantees that once the
    /// tuple has been received, it will always be successfully moved into the
    /// SoAVec and if dropping the value requires reconsituting a Self, then
    /// that will always be done on Drop.
    ///
    /// If the tuple representation gives unprivileged access to internal
    /// fields of the Self type that have safety invariants on them, then any
    /// of the Ref, Mut, Slice, and SliceMut types that enable violating those
    /// invariants should be manually defined.
    fn into_tuple(value: Self) -> Self::TupleRepr;
    /// Take ownership of Self's tuple representation and convert to Self. The
    /// result will immediately be given to the caller or dropped.
    fn from_tuple(value: Self::TupleRepr) -> Self;
    /// Convert the Self's pointer tuple representation into Ref.
    ///
    /// Note: this method should only perform the conversion and nothing else;
    /// the resulting code generation should effectively be a no-op.
    ///
    /// ### Safety
    ///
    /// The Ref type should not allow violating any safety invariants of Self.
    /// This is relevant for Ref types that expose internal mutation APIs.
    fn as_ref<'a>(
        _: PhantomData<&'a Self>,
        value: <Self::TupleRepr as SoATuple>::Pointers,
    ) -> Self::Ref<'a>;
    /// Convert the Self's pointer tuple representation into Mut.
    ///
    /// Note: this method should only perform the conversion and nothing else;
    /// the resulting code generation should effectively be a no-op.
    ///
    /// ### Safety
    ///
    /// The Mut type should not allow violating any safety invariants of Self.
    fn as_mut<'a>(
        _: PhantomData<&'a mut Self>,
        value: <Self::TupleRepr as SoATuple>::Pointers,
    ) -> Self::Mut<'a>;
    /// Convert the Self's pointer tuple representation with length into Slice.
    ///
    /// Note: this method should only perform the conversion and nothing else.
    ///
    /// ### Safety
    ///
    /// The Slice type should not allow violating any safety invariants of
    /// Self. This is relevant for Slice types that expose internal mutation
    /// APIs.
    fn as_slice<'a>(
        _: PhantomData<&'a Self>,
        value: <Self::TupleRepr as SoATuple>::Pointers,
        len: u32,
    ) -> Self::Slice<'a>;
    /// Convert the Self's pointer tuple representation with length into
    /// SliceMut.
    ///
    /// Note: this method should only perform the conversion and nothing else.
    ///
    /// ### Safety
    ///
    /// The SliceMut type should not allow violating any safety invariants of
    /// Self.
    fn as_mut_slice<'a>(
        _: PhantomData<&'a mut Self>,
        value: <Self::TupleRepr as SoATuple>::Pointers,
        len: u32,
    ) -> Self::SliceMut<'a>;
}

/// A trait for working with Struct-of-Arrays tuples. This enables working with
/// Struct-of-Arrays allocations in a way similar to normal vector allocations.
pub trait SoATuple {
    /// A collection of N-1 field pointers where N is the cardinality of the
    /// Self tuple. The first field is always at offset 0 and is thus omitted
    /// from this collection.
    type Offsets: Copy;
    /// A collection of N field pointers where N is the cardinality of the Self
    /// tuple.
    type Pointers: Copy;

    /// Calculate the layout of a Struct-of-Arrays allocation of the Self tuple
    /// with `capacity`.
    fn layout(capacity: u32) -> Result<Layout, LayoutError>;

    /// Calculate the offsets into fields beyond the first.
    fn get_offsets(capacity: u32) -> Self::Offsets;

    /// Move `len` items in the Struct-of-Arrays allocation pointer to by
    /// `base` which previously was had a capacity of `old_capacity` but has
    /// been reallocated to contain `new_capacity`.
    ///
    /// ## Safety
    ///
    /// The base pointer must point to a valid Struct-of-Arrays allocation
    /// containing items in the layout given by `old_capacity`, but with memory
    /// capacity for the layout given by `new_capacity`. The allocation must
    /// contain exactly `len` initialised items. `old_capacity` must be less
    /// than `new_capacity`.
    // Development notes: this could probably be implemented in terms of `copy`
    // and `get_pointers` done at the call-site. Note that when growing the
    // last fields must be copied first (as fields move "up" in the allocation,
    // earlier fields might overwrite later ones) but when shrinking the first
    // fields must be copied first (as fields move "down" in the allocation,
    // earlier fields might be overwritten by later ones).
    unsafe fn grow(base: NonNull<u8>, new_capacity: u32, old_capacity: u32, len: u32);

    /// Read a Self tuple from the `base` Struct-of-Arrays allocation. This
    /// leaves the memory in `base` unchanged.
    ///
    /// ## Safety
    ///
    /// The base pointer must point to a valid Struct-of-Arrays allocation of
    /// the given `capacity`, containing at least `index` initialised items.
    ///
    /// ## Ownership of the Returned Value
    ///
    /// `read` creates a bitwise copy of `Self`, regardless of whether `Self`
    /// is `Copy`. If `Self` is not `Copy`, using both the returned value and
    /// the value in the Struct-of-Arrays allocation can violate memory safety.
    /// Note that assigning into a slice counts as a use because it will
    /// attempt to drop the previous value in the slice. [`write`] can be used
    /// to overwrite data without causing it to be dropped.
    #[must_use]
    unsafe fn read(base: NonNull<u8>, index: u32, capacity: u32) -> Self;

    /// Overwrites an index in the Struct-of-Arrays allocation with the given
    /// value without reading or dropping the old value.
    ///
    /// `write` does not drop the contents of the Struct-of-Arrays at `index`.
    /// This is safe, but it could leak allocations or resources, so care
    /// should be taken not to overwrite an object that should be dropped.
    ///
    /// Additionally, it does not drop `src`. Semantically, `src` is moved into the
    /// location pointed to by `base`, `index`, and `capacity`.
    ///
    /// This is appropriate for initializing uninitialized memory, or overwriting
    /// memory that has previously been [`read`] from.
    ///
    /// ## Safety
    ///
    /// The base pointer must point to a valid Struct-of-Arrays allocation of
    /// the given `capacity`.
    unsafe fn write(base: NonNull<u8>, src: Self, index: u32, capacity: u32);

    /// Copies `count * size_of::<T>()` bytes from `src` to `dst`. The source
    /// and destination may overlap.
    ///
    /// ## Safety
    ///
    /// The pointer collections must be valid, pointing to readable memory for
    /// `src` and readable and writeable memory for `dst`, and the pointers
    /// must be properly aligned. There must be at least `count` valid items to
    /// read from in `src` and equivalently many places to write to in `dst`.
    unsafe fn copy(src: Self::Pointers, dst: Self::Pointers, count: u32);

    /// Drop `len` items in place at the pointed-to places.
    ///
    /// ## Safety
    ///
    /// The pointer collections must be valid, pointing to readable memory
    /// containing at least `len` initialised items. The items pointed to by
    /// `ptrs` must not be used afterwards.
    unsafe fn drop_in_place(ptrs: Self::Pointers, len: u32);

    /// Get the field pointers of a Struct-of-Arrays tuple referring to the
    /// given index.
    ///
    /// ## Safety
    ///
    /// The base pointer must point to a valid Struct-of-Arrays allocation of
    /// the given `capacity`, containing at least `index` initialised items.
    unsafe fn get_pointers(base: NonNull<u8>, index: u32, capacity: u32) -> Self::Pointers;
}

impl<T, U> SoATuple for (T, U) {
    type Offsets = (usize,);
    type Pointers = (NonNull<T>, NonNull<U>);

    fn layout(capacity: u32) -> Result<Layout, LayoutError> {
        Ok(layout_array::<T>(capacity)?
            .extend(layout_array::<U>(capacity)?)?
            .0
            .pad_to_align())
    }

    fn get_offsets(capacity: u32) -> (usize,) {
        // SAFETY: method is guaranteed to call with checked capacities.
        unsafe {
            let layout = layout_array::<T>(capacity).unwrap_unchecked();
            let (_, u_offset) = extend_layout_array::<U>(layout, capacity).unwrap_unchecked();
            (u_offset,)
        }
    }

    unsafe fn grow(base: NonNull<u8>, new_capacity: u32, old_capacity: u32, len: u32) {
        if size_of::<Self>() == 0 || len == 0 {
            return;
        }
        debug_assert!(base.cast::<Self>().is_aligned());
        debug_assert!(old_capacity < new_capacity);

        // SAFETY: Caller guarantee
        unsafe {
            let (_, old_u_ptr) = Self::get_pointers(base, 0, old_capacity);
            // SAFETY: Caller guarantee
            let (_, new_u_ptr) = Self::get_pointers(base, 0, new_capacity);

            // Copy old data to new allocation area.
            core::ptr::copy(old_u_ptr.as_ptr(), new_u_ptr.as_ptr(), len as usize);
        };
    }

    unsafe fn read(ptr: NonNull<u8>, index: u32, capacity: u32) -> Self {
        // SAFETY: Caller guarantee.
        unsafe {
            let ptr = Self::get_pointers(ptr, index, capacity);
            (ptr.0.read(), ptr.1.read())
        }
    }

    unsafe fn write(base: NonNull<u8>, data: Self, index: u32, capacity: u32) {
        debug_assert!(base.cast::<Self>().is_aligned());
        // SAFETY: Caller guarantee.
        unsafe {
            let (t_ptr, u_ptr) = Self::get_pointers(base, index, capacity);

            t_ptr.write(data.0);
            u_ptr.write(data.1);
        }
    }

    unsafe fn copy(src: Self::Pointers, dst: Self::Pointers, len: u32) {
        if size_of::<Self>() == 0 || len == 0 {
            return;
        }
        // SAFETY: old allocation; the layout has been checked.
        let (src_t_ptr, src_u_ptr) = src;
        let (dst_t_ptr, dst_u_ptr) = dst;

        // SAFETY: old data is located at src_*_ptr and its length is len
        unsafe {
            // Copy old data to new allocation area.
            core::ptr::copy(src_u_ptr.as_ptr(), dst_u_ptr.as_ptr(), len as usize);
            // Copy old data to new allocation area.
            core::ptr::copy(src_t_ptr.as_ptr(), dst_t_ptr.as_ptr(), len as usize);
        };
    }

    unsafe fn drop_in_place(ptrs: Self::Pointers, len: u32) {
        assert!(core::mem::needs_drop::<Self>());
        let (t_ptr, u_ptr) = ptrs;
        if core::mem::needs_drop::<T>() {
            // SAFETY: caller guarantee
            unsafe {
                drop_in_place(core::ptr::slice_from_raw_parts_mut(
                    t_ptr.as_ptr(),
                    len as usize,
                ));
            }
        }
        if core::mem::needs_drop::<U>() {
            // SAFETY: caller guarantee
            unsafe {
                drop_in_place(core::ptr::slice_from_raw_parts_mut(
                    u_ptr.as_ptr(),
                    len as usize,
                ));
            }
        }
    }

    unsafe fn get_pointers(ptr: NonNull<u8>, index: u32, capacity: u32) -> Self::Pointers {
        debug_assert!(ptr.cast::<Self>().is_aligned());
        let (u_offset,) = Self::get_offsets(capacity);

        // SAFETY: Caller guarantee.
        unsafe {
            let t_ptr = ptr.cast::<T>().add(index as usize);
            debug_assert!(t_ptr.is_aligned());
            let u_ptr = ptr.byte_add(u_offset).cast::<U>().add(index as usize);
            debug_assert!(u_ptr.is_aligned());
            (t_ptr, u_ptr)
        }
    }
}

impl<T, U, V> SoATuple for (T, U, V) {
    type Offsets = (usize, usize);
    type Pointers = (NonNull<T>, NonNull<U>, NonNull<V>);

    fn layout(capacity: u32) -> Result<Layout, LayoutError> {
        Ok(layout_array::<T>(capacity)?
            .extend(layout_array::<U>(capacity)?)?
            .0
            .extend(layout_array::<V>(capacity)?)?
            .0
            .pad_to_align())
    }

    fn get_offsets(capacity: u32) -> Self::Offsets {
        // SAFETY: method is guaranteed to call with checked capacities.
        unsafe {
            let layout = layout_array::<T>(capacity).unwrap_unchecked();
            let (layout, u_offset) = extend_layout_array::<U>(layout, capacity).unwrap_unchecked();
            let (_, v_offset) = extend_layout_array::<V>(layout, capacity).unwrap_unchecked();
            (u_offset, v_offset)
        }
    }

    unsafe fn read(ptr: NonNull<u8>, index: u32, capacity: u32) -> Self {
        // SAFETY: Caller guarantee.
        unsafe {
            let ptr = Self::get_pointers(ptr, index, capacity);
            (ptr.0.read(), ptr.1.read(), ptr.2.read())
        }
    }

    unsafe fn grow(base: NonNull<u8>, new_capacity: u32, old_capacity: u32, len: u32) {
        if size_of::<Self>() == 0 || len == 0 {
            return;
        }
        debug_assert!(base.cast::<Self>().is_aligned());
        debug_assert!(old_capacity < new_capacity);

        // SAFETY: Caller guarantee
        unsafe {
            let (_, old_u_ptr, old_v_ptr) = Self::get_pointers(base, 0, old_capacity);
            // SAFETY: Caller guarantee
            let (_, new_u_ptr, new_v_ptr) = Self::get_pointers(base, 0, new_capacity);

            // Copy old data to new allocation area.
            core::ptr::copy(old_v_ptr.as_ptr(), new_v_ptr.as_ptr(), len as usize);
            // Copy old data to new allocation area.
            core::ptr::copy(old_u_ptr.as_ptr(), new_u_ptr.as_ptr(), len as usize);
        };
    }

    unsafe fn write(base: NonNull<u8>, data: Self, index: u32, capacity: u32) {
        debug_assert!(base.cast::<Self>().is_aligned());
        // SAFETY: Caller guarantee.
        unsafe {
            let (t_ptr, u_ptr, v_ptr) = Self::get_pointers(base, index, capacity);

            t_ptr.write(data.0);
            u_ptr.write(data.1);
            v_ptr.write(data.2);
        }
    }

    unsafe fn copy(src: Self::Pointers, dst: Self::Pointers, len: u32) {
        if size_of::<Self>() == 0 || len == 0 {
            return;
        }
        // SAFETY: old allocation; the layout has been checked.
        let (src_t_ptr, src_u_ptr, src_v_ptr) = src;
        let (dst_t_ptr, dst_u_ptr, dst_v_ptr) = dst;

        // SAFETY: old data is located at src_*_ptr and its length is len
        unsafe {
            // Copy old data to new allocation area.
            core::ptr::copy(src_v_ptr.as_ptr(), dst_v_ptr.as_ptr(), len as usize);
            // Copy old data to new allocation area.
            core::ptr::copy(src_u_ptr.as_ptr(), dst_u_ptr.as_ptr(), len as usize);
            // Copy old data to new allocation area.
            core::ptr::copy(src_t_ptr.as_ptr(), dst_t_ptr.as_ptr(), len as usize);
        };
    }

    unsafe fn drop_in_place(ptrs: Self::Pointers, len: u32) {
        assert!(core::mem::needs_drop::<Self>());
        let (t_ptr, u_ptr, v_ptr) = ptrs;
        if core::mem::needs_drop::<T>() {
            // SAFETY: caller guarantee
            unsafe {
                drop_in_place(core::ptr::slice_from_raw_parts_mut(
                    t_ptr.as_ptr(),
                    len as usize,
                ));
            }
        }
        if core::mem::needs_drop::<U>() {
            // SAFETY: caller guarantee
            unsafe {
                drop_in_place(core::ptr::slice_from_raw_parts_mut(
                    u_ptr.as_ptr(),
                    len as usize,
                ));
            }
        }
        if core::mem::needs_drop::<V>() {
            // SAFETY: caller guarantee
            unsafe {
                drop_in_place(core::ptr::slice_from_raw_parts_mut(
                    v_ptr.as_ptr(),
                    len as usize,
                ));
            }
        }
    }

    unsafe fn get_pointers(ptr: NonNull<u8>, index: u32, capacity: u32) -> Self::Pointers {
        debug_assert!(ptr.cast::<Self>().is_aligned());
        let (u_offset, v_offset) = Self::get_offsets(capacity);

        // SAFETY: Caller guarantee.
        unsafe {
            let t_ptr = ptr.cast::<T>().add(index as usize);
            debug_assert!(t_ptr.is_aligned());
            let u_ptr = ptr.byte_add(u_offset).cast::<U>().add(index as usize);
            debug_assert!(u_ptr.is_aligned());
            let v_ptr = ptr.byte_add(v_offset).cast::<V>().add(index as usize);
            debug_assert!(v_ptr.is_aligned());
            (t_ptr, u_ptr, v_ptr)
        }
    }
}

impl<T, U, V, W> SoATuple for (T, U, V, W) {
    type Offsets = (usize, usize, usize);
    type Pointers = (NonNull<T>, NonNull<U>, NonNull<V>, NonNull<W>);

    fn layout(capacity: u32) -> Result<Layout, LayoutError> {
        Ok(layout_array::<T>(capacity)?
            .extend(layout_array::<U>(capacity)?)?
            .0
            .extend(layout_array::<V>(capacity)?)?
            .0
            .extend(layout_array::<W>(capacity)?)?
            .0
            .pad_to_align())
    }

    fn get_offsets(capacity: u32) -> Self::Offsets {
        // SAFETY: method is guaranteed to call with checked capacities.
        unsafe {
            let layout = layout_array::<T>(capacity).unwrap_unchecked();
            let (layout, u_offset) = extend_layout_array::<U>(layout, capacity).unwrap_unchecked();
            let (layout, v_offset) = extend_layout_array::<V>(layout, capacity).unwrap_unchecked();
            let (_, w_offset) = extend_layout_array::<W>(layout, capacity).unwrap_unchecked();
            (u_offset, v_offset, w_offset)
        }
    }

    unsafe fn read(ptr: NonNull<u8>, index: u32, capacity: u32) -> Self {
        // SAFETY: Caller guarantee.
        unsafe {
            let ptr = Self::get_pointers(ptr, index, capacity);
            (ptr.0.read(), ptr.1.read(), ptr.2.read(), ptr.3.read())
        }
    }

    unsafe fn grow(base: NonNull<u8>, new_capacity: u32, old_capacity: u32, len: u32) {
        if size_of::<Self>() == 0 || len == 0 {
            return;
        }
        debug_assert!(base.cast::<Self>().is_aligned());
        debug_assert!(old_capacity < new_capacity);

        // SAFETY: Caller guarantee
        unsafe {
            let (_, old_u_ptr, old_v_ptr, old_w_ptr) = Self::get_pointers(base, 0, old_capacity);
            // SAFETY: Caller guarantee
            let (_, new_u_ptr, new_v_ptr, new_w_ptr) = Self::get_pointers(base, 0, new_capacity);

            // Copy old data to new allocation area.
            core::ptr::copy(old_w_ptr.as_ptr(), new_w_ptr.as_ptr(), len as usize);
            // Copy old data to new allocation area.
            core::ptr::copy(old_v_ptr.as_ptr(), new_v_ptr.as_ptr(), len as usize);
            // Copy old data to new allocation area.
            core::ptr::copy(old_u_ptr.as_ptr(), new_u_ptr.as_ptr(), len as usize);
        };
    }

    unsafe fn write(base: NonNull<u8>, data: Self, index: u32, capacity: u32) {
        debug_assert!(base.cast::<Self>().is_aligned());
        // SAFETY: Caller guarantee.
        unsafe {
            let (t_ptr, u_ptr, v_ptr, w_ptr) = Self::get_pointers(base, index, capacity);

            t_ptr.write(data.0);
            u_ptr.write(data.1);
            v_ptr.write(data.2);
            w_ptr.write(data.3);
        }
    }

    unsafe fn drop_in_place(ptrs: Self::Pointers, len: u32) {
        assert!(core::mem::needs_drop::<Self>());
        let (t_ptr, u_ptr, v_ptr, w_ptr) = ptrs;
        if core::mem::needs_drop::<T>() {
            // SAFETY: caller guarantee
            unsafe {
                drop_in_place(core::ptr::slice_from_raw_parts_mut(
                    t_ptr.as_ptr(),
                    len as usize,
                ));
            }
        }
        if core::mem::needs_drop::<U>() {
            // SAFETY: caller guarantee
            unsafe {
                drop_in_place(core::ptr::slice_from_raw_parts_mut(
                    u_ptr.as_ptr(),
                    len as usize,
                ));
            }
        }
        if core::mem::needs_drop::<V>() {
            // SAFETY: caller guarantee
            unsafe {
                drop_in_place(core::ptr::slice_from_raw_parts_mut(
                    v_ptr.as_ptr(),
                    len as usize,
                ));
            }
        }
        if core::mem::needs_drop::<W>() {
            // SAFETY: caller guarantee
            unsafe {
                drop_in_place(core::ptr::slice_from_raw_parts_mut(
                    w_ptr.as_ptr(),
                    len as usize,
                ));
            }
        }
    }

    unsafe fn copy(src: Self::Pointers, dst: Self::Pointers, len: u32) {
        if size_of::<Self>() == 0 || len == 0 {
            return;
        }
        // SAFETY: old allocation; the layout has been checked.
        let (src_t_ptr, src_u_ptr, src_v_ptr, src_w_ptr) = src;
        let (dst_t_ptr, dst_u_ptr, dst_v_ptr, dst_w_ptr) = dst;

        // SAFETY: old data is located at src_*_ptr and its length is len
        unsafe {
            // Copy old data to new allocation area.
            core::ptr::copy(src_w_ptr.as_ptr(), dst_w_ptr.as_ptr(), len as usize);
            // Copy old data to new allocation area.
            core::ptr::copy(src_v_ptr.as_ptr(), dst_v_ptr.as_ptr(), len as usize);
            // Copy old data to new allocation area.
            core::ptr::copy(src_u_ptr.as_ptr(), dst_u_ptr.as_ptr(), len as usize);
            // Copy old data to new allocation area.
            core::ptr::copy(src_t_ptr.as_ptr(), dst_t_ptr.as_ptr(), len as usize);
        };
    }

    unsafe fn get_pointers(ptr: NonNull<u8>, index: u32, capacity: u32) -> Self::Pointers {
        debug_assert!(ptr.cast::<Self>().is_aligned());
        let (u_offset, v_offset, w_offset) = Self::get_offsets(capacity);

        // SAFETY: Caller guarantee.
        unsafe {
            let t_ptr = ptr.cast::<T>().add(index as usize);
            debug_assert!(t_ptr.is_aligned());
            let u_ptr = ptr.byte_add(u_offset).cast::<U>().add(index as usize);
            debug_assert!(u_ptr.is_aligned());
            let v_ptr = ptr.byte_add(v_offset).cast::<V>().add(index as usize);
            debug_assert!(v_ptr.is_aligned());
            let w_ptr = ptr.byte_add(w_offset).cast::<W>().add(index as usize);
            debug_assert!(w_ptr.is_aligned());
            (t_ptr, u_ptr, v_ptr, w_ptr)
        }
    }
}

impl<T, U, V, W, X> SoATuple for (T, U, V, W, X) {
    type Offsets = (usize, usize, usize, usize);
    type Pointers = (NonNull<T>, NonNull<U>, NonNull<V>, NonNull<W>, NonNull<X>);

    fn layout(capacity: u32) -> Result<Layout, LayoutError> {
        Ok(layout_array::<T>(capacity)?
            .extend(layout_array::<U>(capacity)?)?
            .0
            .extend(layout_array::<V>(capacity)?)?
            .0
            .extend(layout_array::<W>(capacity)?)?
            .0
            .extend(layout_array::<X>(capacity)?)?
            .0
            .pad_to_align())
    }

    fn get_offsets(capacity: u32) -> Self::Offsets {
        // SAFETY: method is guaranteed to call with checked capacities.
        unsafe {
            let layout = layout_array::<T>(capacity).unwrap_unchecked();
            let (layout, u_offset) = extend_layout_array::<U>(layout, capacity).unwrap_unchecked();
            let (layout, v_offset) = extend_layout_array::<V>(layout, capacity).unwrap_unchecked();
            let (layout, w_offset) = extend_layout_array::<W>(layout, capacity).unwrap_unchecked();
            let (_, x_offset) = extend_layout_array::<X>(layout, capacity).unwrap_unchecked();
            (u_offset, v_offset, w_offset, x_offset)
        }
    }

    unsafe fn read(ptr: NonNull<u8>, index: u32, capacity: u32) -> Self {
        // SAFETY: Caller guarantee.
        unsafe {
            let ptr = Self::get_pointers(ptr, index, capacity);
            (
                ptr.0.read(),
                ptr.1.read(),
                ptr.2.read(),
                ptr.3.read(),
                ptr.4.read(),
            )
        }
    }

    unsafe fn grow(base: NonNull<u8>, new_capacity: u32, old_capacity: u32, len: u32) {
        if size_of::<Self>() == 0 || len == 0 {
            return;
        }
        debug_assert!(base.cast::<Self>().is_aligned());
        debug_assert!(old_capacity < new_capacity);

        // SAFETY: Caller guarantee
        unsafe {
            let (_, old_u_ptr, old_v_ptr, old_w_ptr, old_x_ptr) =
                Self::get_pointers(base, 0, old_capacity);
            // SAFETY: Caller guarantee
            let (_, new_u_ptr, new_v_ptr, new_w_ptr, new_x_ptr) =
                Self::get_pointers(base, 0, new_capacity);

            // Copy old data to new allocation area.
            core::ptr::copy(old_x_ptr.as_ptr(), new_x_ptr.as_ptr(), len as usize);
            // Copy old data to new allocation area.
            core::ptr::copy(old_w_ptr.as_ptr(), new_w_ptr.as_ptr(), len as usize);
            // Copy old data to new allocation area.
            core::ptr::copy(old_v_ptr.as_ptr(), new_v_ptr.as_ptr(), len as usize);
            // Copy old data to new allocation area.
            core::ptr::copy(old_u_ptr.as_ptr(), new_u_ptr.as_ptr(), len as usize);
        };
    }

    unsafe fn write(base: NonNull<u8>, data: Self, index: u32, capacity: u32) {
        debug_assert!(base.cast::<Self>().is_aligned());

        // SAFETY: Caller guarantees that base points to allocation of capacity
        // and index can be written to.
        let (t_ptr, u_ptr, v_ptr, w_ptr, x_ptr) =
            unsafe { Self::get_pointers(base, index, capacity) };

        // SAFETY: Caller guarantees that index can be written to.
        unsafe {
            t_ptr.write(data.0);
            u_ptr.write(data.1);
            v_ptr.write(data.2);
            w_ptr.write(data.3);
            x_ptr.write(data.4);
        }
    }

    unsafe fn copy(src: Self::Pointers, dst: Self::Pointers, len: u32) {
        if size_of::<Self>() == 0 || len == 0 {
            return;
        }
        // SAFETY: old allocation; the layout has been checked.
        let (src_t_ptr, src_u_ptr, src_v_ptr, src_w_ptr, src_x_ptr) = src;
        let (dst_t_ptr, dst_u_ptr, dst_v_ptr, dst_w_ptr, dst_x_ptr) = dst;

        // SAFETY: old data is located at src_*_ptr and its length is len
        unsafe {
            core::ptr::copy(src_t_ptr.as_ptr(), dst_t_ptr.as_ptr(), len as usize);
            // Copy old data to new allocation area.
            core::ptr::copy(src_x_ptr.as_ptr(), dst_x_ptr.as_ptr(), len as usize);
            // Copy old data to new allocation area.
            core::ptr::copy(src_w_ptr.as_ptr(), dst_w_ptr.as_ptr(), len as usize);
            // Copy old data to new allocation area.
            core::ptr::copy(src_v_ptr.as_ptr(), dst_v_ptr.as_ptr(), len as usize);
            // Copy old data to new allocation area.
            core::ptr::copy(src_u_ptr.as_ptr(), dst_u_ptr.as_ptr(), len as usize);
        };
    }

    unsafe fn drop_in_place(ptrs: Self::Pointers, len: u32) {
        assert!(core::mem::needs_drop::<Self>());
        let (t_ptr, u_ptr, v_ptr, w_ptr, x_ptr) = ptrs;
        if core::mem::needs_drop::<T>() {
            // SAFETY: caller guarantee
            unsafe {
                drop_in_place(core::ptr::slice_from_raw_parts_mut(
                    t_ptr.as_ptr(),
                    len as usize,
                ));
            }
        }
        if core::mem::needs_drop::<U>() {
            // SAFETY: caller guarantee
            unsafe {
                drop_in_place(core::ptr::slice_from_raw_parts_mut(
                    u_ptr.as_ptr(),
                    len as usize,
                ));
            }
        }
        if core::mem::needs_drop::<V>() {
            // SAFETY: caller guarantee
            unsafe {
                drop_in_place(core::ptr::slice_from_raw_parts_mut(
                    v_ptr.as_ptr(),
                    len as usize,
                ));
            }
        }
        if core::mem::needs_drop::<W>() {
            // SAFETY: caller guarantee
            unsafe {
                drop_in_place(core::ptr::slice_from_raw_parts_mut(
                    w_ptr.as_ptr(),
                    len as usize,
                ));
            }
        }
        if core::mem::needs_drop::<X>() {
            // SAFETY: caller guarantee
            unsafe {
                drop_in_place(core::ptr::slice_from_raw_parts_mut(
                    x_ptr.as_ptr(),
                    len as usize,
                ));
            }
        }
    }

    unsafe fn get_pointers(base: NonNull<u8>, index: u32, capacity: u32) -> Self::Pointers {
        debug_assert!(base.cast::<Self>().is_aligned());
        let (u_offset, v_offset, w_offset, x_offset) = Self::get_offsets(capacity);

        // SAFETY: caller guarantees that base points to a valid SoA of
        // capacity and index is within it.
        unsafe {
            let t_ptr = base.cast::<T>().add(index as usize);
            debug_assert!(t_ptr.is_aligned());
            let u_ptr = base.byte_add(u_offset).cast::<U>().add(index as usize);
            debug_assert!(u_ptr.is_aligned());
            let v_ptr = base.byte_add(v_offset).cast::<V>().add(index as usize);
            debug_assert!(v_ptr.is_aligned());
            let w_ptr = base.byte_add(w_offset).cast::<W>().add(index as usize);
            debug_assert!(w_ptr.is_aligned());
            let x_ptr = base.byte_add(x_offset).cast::<X>().add(index as usize);
            debug_assert!(x_ptr.is_aligned());
            (t_ptr, u_ptr, v_ptr, w_ptr, x_ptr)
        }
    }
}

#[inline]
fn extend_layout_array<T>(layout: Layout, cap: u32) -> Result<(Layout, usize), LayoutError> {
    layout.extend(layout_array::<T>(cap)?)
}

#[inline]
fn layout_array<T>(cap: u32) -> Result<Layout, LayoutError> {
    let elem_layout = Layout::new::<T>();
    Layout::from_size_align(elem_layout.size() * cap as usize, elem_layout.align())
}

unsafe impl<T, U> SoAble for (T, U) {
    type TupleRepr = Self;

    type Ref<'a>
        = (&'a T, &'a U)
    where
        Self: 'a;

    type Mut<'a>
        = (&'a mut T, &'a mut U)
    where
        Self: 'a;

    type Slice<'a>
        = (&'a [T], &'a [U])
    where
        Self: 'a;

    type SliceMut<'a>
        = (&'a mut [T], &'a mut [U])
    where
        Self: 'a;

    fn into_tuple(value: Self) -> Self::TupleRepr {
        value
    }

    fn from_tuple(value: Self::TupleRepr) -> Self {
        value
    }

    fn as_ref<'a>(
        _: PhantomData<&'a Self>,
        value: <Self::TupleRepr as SoATuple>::Pointers,
    ) -> Self::Ref<'a> {
        let (a, b) = value;
        unsafe { (a.as_ref(), b.as_ref()) }
    }

    fn as_mut<'a>(
        _: PhantomData<&'a mut Self>,
        value: <Self::TupleRepr as SoATuple>::Pointers,
    ) -> Self::Mut<'a> {
        let (mut a, mut b) = value;
        unsafe { (a.as_mut(), b.as_mut()) }
    }

    fn as_slice<'a>(
        _: PhantomData<&'a Self>,
        value: <Self::TupleRepr as SoATuple>::Pointers,
        len: u32,
    ) -> Self::Slice<'a> {
        let len = len as usize;
        let (a, b) = value;
        unsafe {
            (
                core::slice::from_raw_parts(a.as_ptr(), len),
                core::slice::from_raw_parts(b.as_ptr(), len),
            )
        }
    }

    fn as_mut_slice<'a>(
        _: PhantomData<&'a mut Self>,
        value: <Self::TupleRepr as SoATuple>::Pointers,
        len: u32,
    ) -> Self::SliceMut<'a> {
        let len = len as usize;
        let (a, b) = value;
        unsafe {
            (
                core::slice::from_raw_parts_mut(a.as_ptr(), len),
                core::slice::from_raw_parts_mut(b.as_ptr(), len),
            )
        }
    }
}

unsafe impl<T, U, V> SoAble for (T, U, V) {
    type TupleRepr = Self;

    type Ref<'a>
        = (&'a T, &'a U, &'a V)
    where
        Self: 'a;

    type Mut<'a>
        = (&'a mut T, &'a mut U, &'a mut V)
    where
        Self: 'a;

    type Slice<'a>
        = (&'a [T], &'a [U], &'a [V])
    where
        Self: 'a;

    type SliceMut<'a>
        = (&'a mut [T], &'a mut [U], &'a mut [V])
    where
        Self: 'a;

    fn into_tuple(value: Self) -> Self::TupleRepr {
        value
    }

    fn from_tuple(value: Self::TupleRepr) -> Self {
        value
    }

    fn as_ref<'a>(
        _: PhantomData<&'a Self>,
        value: <Self::TupleRepr as SoATuple>::Pointers,
    ) -> Self::Ref<'a> {
        let (a, b, c) = value;
        unsafe { (a.as_ref(), b.as_ref(), c.as_ref()) }
    }

    fn as_mut<'a>(
        _: PhantomData<&'a mut Self>,
        value: <Self::TupleRepr as SoATuple>::Pointers,
    ) -> Self::Mut<'a> {
        let (mut a, mut b, mut c) = value;
        unsafe { (a.as_mut(), b.as_mut(), c.as_mut()) }
    }

    fn as_slice<'a>(
        _: PhantomData<&'a Self>,
        value: <Self::TupleRepr as SoATuple>::Pointers,
        len: u32,
    ) -> Self::Slice<'a> {
        let len = len as usize;
        let (a, b, c) = value;
        unsafe {
            (
                core::slice::from_raw_parts(a.as_ptr(), len),
                core::slice::from_raw_parts(b.as_ptr(), len),
                core::slice::from_raw_parts(c.as_ptr(), len),
            )
        }
    }

    fn as_mut_slice<'a>(
        _: PhantomData<&'a mut Self>,
        value: <Self::TupleRepr as SoATuple>::Pointers,
        len: u32,
    ) -> Self::SliceMut<'a> {
        let len = len as usize;
        let (a, b, c) = value;
        unsafe {
            (
                core::slice::from_raw_parts_mut(a.as_ptr(), len),
                core::slice::from_raw_parts_mut(b.as_ptr(), len),
                core::slice::from_raw_parts_mut(c.as_ptr(), len),
            )
        }
    }
}

unsafe impl<T, U, V, W> SoAble for (T, U, V, W) {
    type TupleRepr = Self;

    type Ref<'a>
        = (&'a T, &'a U, &'a V, &'a W)
    where
        Self: 'a;

    type Mut<'a>
        = (&'a mut T, &'a mut U, &'a mut V, &'a mut W)
    where
        Self: 'a;

    type Slice<'a>
        = (&'a [T], &'a [U], &'a [V], &'a [W])
    where
        Self: 'a;

    type SliceMut<'a>
        = (&'a mut [T], &'a mut [U], &'a mut [V], &'a mut [W])
    where
        Self: 'a;

    fn into_tuple(value: Self) -> Self::TupleRepr {
        value
    }

    fn from_tuple(value: Self::TupleRepr) -> Self {
        value
    }

    fn as_ref<'a>(
        _: PhantomData<&'a Self>,
        value: <Self::TupleRepr as SoATuple>::Pointers,
    ) -> Self::Ref<'a> {
        let (a, b, c, d) = value;
        unsafe { (a.as_ref(), b.as_ref(), c.as_ref(), d.as_ref()) }
    }

    fn as_mut<'a>(
        _: PhantomData<&'a mut Self>,
        value: <Self::TupleRepr as SoATuple>::Pointers,
    ) -> Self::Mut<'a> {
        let (mut a, mut b, mut c, mut d) = value;
        unsafe { (a.as_mut(), b.as_mut(), c.as_mut(), d.as_mut()) }
    }

    fn as_slice<'a>(
        _: PhantomData<&'a Self>,
        value: <Self::TupleRepr as SoATuple>::Pointers,
        len: u32,
    ) -> Self::Slice<'a> {
        let len = len as usize;
        let (a, b, c, d) = value;
        unsafe {
            (
                core::slice::from_raw_parts(a.as_ptr(), len),
                core::slice::from_raw_parts(b.as_ptr(), len),
                core::slice::from_raw_parts(c.as_ptr(), len),
                core::slice::from_raw_parts(d.as_ptr(), len),
            )
        }
    }

    fn as_mut_slice<'a>(
        _: PhantomData<&'a mut Self>,
        value: <Self::TupleRepr as SoATuple>::Pointers,
        len: u32,
    ) -> Self::SliceMut<'a> {
        let len = len as usize;
        let (a, b, c, d) = value;
        unsafe {
            (
                core::slice::from_raw_parts_mut(a.as_ptr(), len),
                core::slice::from_raw_parts_mut(b.as_ptr(), len),
                core::slice::from_raw_parts_mut(c.as_ptr(), len),
                core::slice::from_raw_parts_mut(d.as_ptr(), len),
            )
        }
    }
}

unsafe impl<T, U, V, W, X> SoAble for (T, U, V, W, X) {
    type TupleRepr = Self;

    type Ref<'a>
        = (&'a T, &'a U, &'a V, &'a W, &'a X)
    where
        Self: 'a;

    type Mut<'a>
        = (&'a mut T, &'a mut U, &'a mut V, &'a mut W, &'a mut X)
    where
        Self: 'a;

    type Slice<'a>
        = (&'a [T], &'a [U], &'a [V], &'a [W], &'a [X])
    where
        Self: 'a;

    type SliceMut<'a>
        = (
        &'a mut [T],
        &'a mut [U],
        &'a mut [V],
        &'a mut [W],
        &'a mut [X],
    )
    where
        Self: 'a;

    fn into_tuple(value: Self) -> Self::TupleRepr {
        value
    }

    fn from_tuple(value: Self::TupleRepr) -> Self {
        value
    }

    fn as_ref<'a>(
        _: PhantomData<&'a Self>,
        value: <Self::TupleRepr as SoATuple>::Pointers,
    ) -> Self::Ref<'a> {
        let (a, b, c, d, e) = value;
        unsafe { (a.as_ref(), b.as_ref(), c.as_ref(), d.as_ref(), e.as_ref()) }
    }

    fn as_mut<'a>(
        _: PhantomData<&'a mut Self>,
        value: <Self::TupleRepr as SoATuple>::Pointers,
    ) -> Self::Mut<'a> {
        let (mut a, mut b, mut c, mut d, mut e) = value;
        unsafe { (a.as_mut(), b.as_mut(), c.as_mut(), d.as_mut(), e.as_mut()) }
    }

    fn as_slice<'a>(
        _: PhantomData<&'a Self>,
        value: <Self::TupleRepr as SoATuple>::Pointers,
        len: u32,
    ) -> Self::Slice<'a> {
        let len = len as usize;
        let (a, b, c, d, e) = value;
        unsafe {
            (
                core::slice::from_raw_parts(a.as_ptr(), len),
                core::slice::from_raw_parts(b.as_ptr(), len),
                core::slice::from_raw_parts(c.as_ptr(), len),
                core::slice::from_raw_parts(d.as_ptr(), len),
                core::slice::from_raw_parts(e.as_ptr(), len),
            )
        }
    }

    fn as_mut_slice<'a>(
        _: PhantomData<&'a mut Self>,
        value: <Self::TupleRepr as SoATuple>::Pointers,
        len: u32,
    ) -> Self::SliceMut<'a> {
        let len = len as usize;
        let (a, b, c, d, e) = value;
        unsafe {
            (
                core::slice::from_raw_parts_mut(a.as_ptr(), len),
                core::slice::from_raw_parts_mut(b.as_ptr(), len),
                core::slice::from_raw_parts_mut(c.as_ptr(), len),
                core::slice::from_raw_parts_mut(d.as_ptr(), len),
                core::slice::from_raw_parts_mut(e.as_ptr(), len),
            )
        }
    }
}
