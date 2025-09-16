#![no_main]
use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use soavec::{SoAVec, SoAble};
use soavec_derive::SoAble as SoAbleDerive;
use std::hint::black_box;

#[derive(SoAbleDerive, Debug, Clone, PartialEq, Arbitrary)]
struct PlainStruct {
    x: i32,
    y: u64,
    z: i16,
}

#[derive(SoAbleDerive, Debug, Clone, PartialEq, Arbitrary)]
struct CustomDropStruct {
    counter: u32,
    flag: bool,
    value: i64,
}

impl Drop for CustomDropStruct {
    fn drop(&mut self) {
        self.counter = 0;
        self.flag = false;
        self.value = -1;
    }
}

#[derive(SoAbleDerive, Debug, Clone, PartialEq, Arbitrary)]
struct MixedStruct {
    id: u32,
    name: String,
    values: Vec<i32>,
    count: u16,
}

#[derive(SoAbleDerive, Debug, Clone, PartialEq, Arbitrary)]
struct HeapOnlyStruct {
    text: String,
    data: Vec<u8>,
    more_data: Vec<String>,
}

struct SoableVec {
    ptr: *mut u32,
    length: usize,
    capacity: usize,
}

impl From<Vec<u32>> for SoableVec {
    fn from(mut value: Vec<u32>) -> Self {
        let ptr = value.as_mut_ptr();
        let length = value.len();
        let capacity = value.capacity();

        core::mem::forget(value);

        SoableVec {
            ptr,
            length,
            capacity,
        }
    }
}

impl From<SoableVec> for Vec<u32> {
    fn from(value: SoableVec) -> Self {
        let ptr = value.ptr;
        let length = value.length;
        let capacity = value.capacity;

        core::mem::forget(value);

        unsafe { Vec::from_raw_parts(ptr, length, capacity) }
    }
}

impl Drop for SoableVec {
    fn drop(&mut self) {
        let ptr = self.ptr;
        let length = self.length;
        let capacity = self.capacity;

        let _ = unsafe { Vec::from_raw_parts(ptr, length, capacity) };
    }
}

// Recursive expansion of SoAble macro
// ====================================

#[allow(dead_code)]
struct SoableVecRef<'soa> {
    pub ptr: &'soa *mut u32,
    pub length: &'soa usize,
    pub capacity: &'soa usize,
}
impl<'soa> Copy for SoableVecRef<'soa> {}

impl<'soa> Clone for SoableVecRef<'soa> {
    fn clone(&self) -> Self {
        *self
    }
}
#[allow(dead_code)]
struct SoableVecMut<'soa> {
    pub ptr: &'soa mut *mut u32,
    pub length: &'soa mut usize,
    pub capacity: &'soa mut usize,
}
#[allow(dead_code)]
struct SoableVecSlice<'soa> {
    pub ptr: &'soa [*mut u32],
    pub length: &'soa [usize],
    pub capacity: &'soa [usize],
}
impl<'soa> Copy for SoableVecSlice<'soa> {}

impl<'soa> Clone for SoableVecSlice<'soa> {
    fn clone(&self) -> Self {
        *self
    }
}
#[allow(dead_code)]
struct SoableVecSliceMut<'soa> {
    pub ptr: &'soa mut [*mut u32],
    pub length: &'soa mut [usize],
    pub capacity: &'soa mut [usize],
}
unsafe impl soavec::SoAble for SoableVec {
    const MUST_DROP_AS_SELF: bool = true;
    type TupleRepr = (*mut u32, usize, usize);
    type Ref<'soa>
        = SoableVecRef<'soa>
    where
        Self: 'soa;
    type Mut<'soa>
        = SoableVecMut<'soa>
    where
        Self: 'soa;
    type Slice<'soa>
        = SoableVecSlice<'soa>
    where
        Self: 'soa;
    type SliceMut<'soa>
        = SoableVecSliceMut<'soa>
    where
        Self: 'soa;
    fn into_tuple(value: Self) -> Self::TupleRepr {
        let Self {
            ptr,
            length,
            capacity,
        } = value;
        core::mem::forget(value);
        (ptr, length, capacity)
    }
    fn from_tuple(value: Self::TupleRepr) -> Self {
        let (ptr, length, capacity) = value;
        Self {
            ptr,
            length,
            capacity,
        }
    }
    fn as_ref<'soa>(
        _: std::marker::PhantomData<&'soa Self>,
        value: <Self::TupleRepr as soavec::SoATuple>::Pointers,
    ) -> Self::Ref<'soa> {
        let (ptr, length, capacity) = value;
        unsafe {
            SoableVecRef {
                ptr: ptr.as_ref(),
                length: length.as_ref(),
                capacity: capacity.as_ref(),
            }
        }
    }
    fn as_mut<'soa>(
        _: std::marker::PhantomData<&'soa mut Self>,
        value: <Self::TupleRepr as soavec::SoATuple>::Pointers,
    ) -> Self::Mut<'soa> {
        let (mut ptr, mut length, mut capacity) = value;
        unsafe {
            SoableVecMut {
                ptr: ptr.as_mut(),
                length: length.as_mut(),
                capacity: capacity.as_mut(),
            }
        }
    }
    fn as_slice<'soa>(
        _: std::marker::PhantomData<&'soa Self>,
        value: <Self::TupleRepr as soavec::SoATuple>::Pointers,
        len: u32,
    ) -> Self::Slice<'soa> {
        let len = len as usize;
        let (ptr, length, capacity) = value;
        unsafe {
            SoableVecSlice {
                ptr: core::slice::from_raw_parts(ptr.as_ptr(), len),
                length: core::slice::from_raw_parts(length.as_ptr(), len),
                capacity: core::slice::from_raw_parts(capacity.as_ptr(), len),
            }
        }
    }
    fn as_mut_slice<'soa>(
        _: std::marker::PhantomData<&'soa mut Self>,
        value: <Self::TupleRepr as soavec::SoATuple>::Pointers,
        len: u32,
    ) -> Self::SliceMut<'soa> {
        let len = len as usize;
        let (ptr, length, capacity) = value;
        unsafe {
            SoableVecSliceMut {
                ptr: core::slice::from_raw_parts_mut(ptr.as_ptr(), len),
                length: core::slice::from_raw_parts_mut(length.as_ptr(), len),
                capacity: core::slice::from_raw_parts_mut(capacity.as_ptr(), len),
            }
        }
    }
}

#[derive(Arbitrary, Debug)]
enum SoAVecOp<T> {
    Push(T),
    Pop,
    Reserve { additional: u32 },
    Get { index: u32 },
    GetMut { index: u32 },
}

#[derive(Arbitrary, Debug)]
struct SoAVecFuzzInput {
    plain_ops: Vec<SoAVecOp<PlainStruct>>,
    mixed_ops: Vec<SoAVecOp<MixedStruct>>,
    heap_only_ops: Vec<SoAVecOp<HeapOnlyStruct>>,
    custom_drop_ops: Vec<SoAVecOp<CustomDropStruct>>,
    normal_vec_ops: Vec<SoAVecOp<Vec<u32>>>,
}

fn execute_ops<T: SoAble, U: Into<T> + Clone>(vec: &mut SoAVec<T>, ops: &[SoAVecOp<U>]) {
    for op in ops {
        match op {
            SoAVecOp::Push(item) => {
                let _ = vec.push(item.clone().into());
            }
            SoAVecOp::Pop => {
                let _ = vec.pop();
            }
            SoAVecOp::Reserve { additional } => {
                let safe_additional = (*additional).min(1_000_000);
                let _ = vec.reserve(safe_additional);
            }
            SoAVecOp::Get { index } => {
                black_box(vec.get(*index));
            }
            SoAVecOp::GetMut { index } => {
                if let Some(mut item_ref) = vec.get_mut(*index) {
                    black_box(&item_ref);
                    black_box(&mut item_ref);
                }
            }
        }

        assert!(
            vec.len() <= vec.capacity(),
            "Length should not exceed capacity"
        );
    }
}

fuzz_target!(|input: SoAVecFuzzInput| {
    let mut plain_vec: SoAVec<PlainStruct> = SoAVec::new();
    execute_ops(&mut plain_vec, &input.plain_ops);

    let mut mixed_vec: SoAVec<MixedStruct> = SoAVec::new();
    execute_ops(&mut mixed_vec, &input.mixed_ops);

    let mut heap_only_vec: SoAVec<HeapOnlyStruct> = SoAVec::new();
    execute_ops(&mut heap_only_vec, &input.heap_only_ops);

    let mut custom_drop_vec: SoAVec<CustomDropStruct> = SoAVec::new();
    execute_ops(&mut custom_drop_vec, &input.custom_drop_ops);

    let mut normal_vec: SoAVec<SoableVec> = SoAVec::new();
    execute_ops(&mut normal_vec, &input.normal_vec_ops);
});
