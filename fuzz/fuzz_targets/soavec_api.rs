#![no_main]
use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use soavec::{SoAVec, SoAble};
use soavec_derive::SoAble;
use std::hint::black_box;

#[derive(SoAble, Debug, Clone, PartialEq, Arbitrary)]
struct PlainStruct {
    x: i32,
    y: u64,
    z: i16,
}

#[derive(SoAble, Debug, Clone, PartialEq, Arbitrary)]
struct MixedStruct {
    id: u32,
    name: String,
    values: Vec<i32>,
    count: u16,
}

#[derive(SoAble, Debug, Clone, PartialEq, Arbitrary)]
struct HeapOnlyStruct {
    text: String,
    data: Vec<u8>,
    more_data: Vec<String>,
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
}

fn execute_ops<T: Clone + SoAble>(vec: &mut SoAVec<T>, ops: &[SoAVecOp<T>]) {
    for op in ops {
        match op {
            SoAVecOp::Push(item) => {
                let _ = vec.push(item.clone());
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
});
