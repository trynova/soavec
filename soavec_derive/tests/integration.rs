#![allow(dead_code)]
use soavec_derive::SoAble;

#[derive(SoAble)]
struct TestStruct {
    a: u32,
    b: u64,
}

#[derive(SoAble)]
struct TestStructThreeFields {
    x: i32,
    y: f64,
    z: bool,
}

#[derive(SoAble)]
struct GenericStruct<T, U> {
    first: T,
    second: U,
}

#[derive(SoAble)]
struct TupleStruct(u32, f64, String);

#[derive(SoAble)]
struct StructWithLen {
    a: usize,
    // `len` should not overwrite in the macro
    len: usize,
}

#[derive(SoAble)]
pub enum Value {
    Undefined(()),
    Null(()),
    Boolean(bool),
    Number(f64),
}

// Test enum with unnamed fields for safety analysis
#[derive(SoAble)]
#[repr(u8)]
pub enum TestEnum {
    VariantA(u32, u64),
    VariantB(f32, bool),
    VariantC(f64, i32),
}

// Test enum with named fields
#[derive(SoAble)]
#[repr(u8)]
pub enum NamedFieldEnum {
    Point { x: f32, y: f32 },
    Vector { x: f32, y: f32, z: f32 },
    Origin,
}

// Test enum with private visibility
#[derive(SoAble)]
enum PrivateEnum {
    A(u32),
    B(f32),
}

// Test with pub(crate) visibility
#[derive(SoAble)]
pub(crate) enum CrateVisibleEnum {
    X(i32, i32),
    Y(bool, u8),
}

#[test]
fn test_derive_compiles() {
    // If this compiles, the derive macro worked
    let _s = TestStruct { a: 1, b: 2 };
    let _s3 = TestStructThreeFields {
        x: 1,
        y: 2.0,
        z: true,
    };
}

#[test]
fn test_soable_trait_implemented() {
    use soavec::SoAble;

    // Test that the SoAble trait is properly implemented
    let test_struct = TestStruct { a: 42, b: 100 };
    let tuple = SoAble::into_tuple(test_struct);
    assert_eq!(tuple, (42, 100));

    let back = TestStruct::from_tuple((99, 200));
    assert_eq!(back.a, 99);
    assert_eq!(back.b, 200);
}

#[test]
fn test_generic_struct() {
    use soavec::SoAble;

    let generic = GenericStruct {
        first: "hello",
        second: 3.21,
    };
    let tuple = SoAble::into_tuple(generic);
    assert_eq!(tuple, ("hello", 3.21));

    let back = GenericStruct::from_tuple(("world", 2.71));
    assert_eq!(back.first, "world");
    assert_eq!(back.second, 2.71);
}

#[test]
fn test_tuple_struct() {
    use soavec::SoAble;

    let tuple_struct = TupleStruct(7, 3.41, "test".to_string());
    let tuple = SoAble::into_tuple(tuple_struct);
    assert_eq!(tuple, (7, 3.41, "test".to_string()));

    let back = TupleStruct::from_tuple((42, 2.71, "hello".to_string()));
    assert_eq!(back.0, 42);
    assert_eq!(back.1, 2.71);
    assert_eq!(back.2, "hello".to_string());
}

#[test]
fn test_struct_with_len_field() {
    use soavec::SoAble;

    let value = StructWithLen { a: 5, len: 8 };
    let tuple = SoAble::into_tuple(value);
    assert_eq!(tuple, (5, 8));

    let back = StructWithLen::from_tuple((9, 12));
    assert_eq!(back.a, 9);
    assert_eq!(back.len, 12);
}

#[test]
fn test_enum() {
    use soavec::SoAble;

    let val = Value::Boolean(true);
    let tuple = SoAble::into_tuple(val);

    let back = Value::from_tuple(tuple);
    match back {
        Value::Boolean(b) => assert!(b),
        _ => panic!("Expected Value::Boolean"),
    }
}

#[test]
fn test_discriminant_access_ref() {
    use soavec::SoAVec;

    let mut vec = SoAVec::<TestEnum>::new();
    let _ = vec.push(TestEnum::VariantA(10, 20));
    let _ = vec.push(TestEnum::VariantB(3.5, true));
    let _ = vec.push(TestEnum::VariantC(2.5, -5));

    let item_ref = vec.get(0).unwrap();
    let disc = item_ref.get_discriminant();
    assert_eq!(*disc, TestEnumDiscriminant::VariantA);

    let item_ref = vec.get(1).unwrap();
    let disc = item_ref.get_discriminant();
    assert_eq!(*disc, TestEnumDiscriminant::VariantB);

    let slice = vec.as_slice();
    let discs = slice.get_discriminant();
    assert_eq!(discs.len(), 3);
    assert_eq!(discs[0], TestEnumDiscriminant::VariantA);
    assert_eq!(discs[1], TestEnumDiscriminant::VariantB);
    assert_eq!(discs[2], TestEnumDiscriminant::VariantC);
}

#[test]
fn test_discriminant_access_mut() {
    use soavec::SoAVec;

    let mut vec = SoAVec::<TestEnum>::new();
    let _ = vec.push(TestEnum::VariantA(100, 200));

    let item_mut = vec.get_mut(0).unwrap();
    let disc = item_mut.get_discriminant();
    assert_eq!(*disc, TestEnumDiscriminant::VariantA);

    let slice_mut = vec.as_mut_slice();
    let discs = slice_mut.get_discriminant();
    assert_eq!(discs[0], TestEnumDiscriminant::VariantA);
}

#[test]
fn test_discriminant_unsafe_mutation() {
    use soavec::SoAVec;

    let mut vec = SoAVec::<TestEnum>::new();
    let _ = vec.push(TestEnum::VariantA(42, 84));

    let mut item_mut = vec.get_mut(0).unwrap();

    assert_eq!(*item_mut.get_discriminant(), TestEnumDiscriminant::VariantA);

    unsafe {
        let disc_mut = item_mut.get_discriminant_mut();
        *disc_mut = TestEnumDiscriminant::VariantB;
    }

    assert_eq!(*item_mut.get_discriminant(), TestEnumDiscriminant::VariantB);

    // NOTE: Do NOT attempt to read the union fields now - they contain
    // invalid data for VariantB!
}

#[test]
fn test_named_field_enum() {
    use soavec::{SoAVec, SoAble};

    let mut vec = SoAVec::<NamedFieldEnum>::new();
    let _ = vec.push(NamedFieldEnum::Point { x: 1.0, y: 2.0 });
    let _ = vec.push(NamedFieldEnum::Vector {
        x: 3.0,
        y: 4.0,
        z: 5.0,
    });
    let _ = vec.push(NamedFieldEnum::Origin);

    let point = NamedFieldEnum::Point { x: 10.0, y: 20.0 };
    let tuple = SoAble::into_tuple(point);
    let back = NamedFieldEnum::from_tuple(tuple);
    match back {
        NamedFieldEnum::Point { x, y } => {
            assert_eq!(x, 10.0);
            assert_eq!(y, 20.0);
        }
        _ => panic!("Expected Point variant"),
    }

    assert_eq!(
        *vec.get(0).unwrap().get_discriminant(),
        NamedFieldEnumDiscriminant::Point
    );
    assert_eq!(
        *vec.get(1).unwrap().get_discriminant(),
        NamedFieldEnumDiscriminant::Vector
    );
    assert_eq!(
        *vec.get(2).unwrap().get_discriminant(),
        NamedFieldEnumDiscriminant::Origin
    );
}
