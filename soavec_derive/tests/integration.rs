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

    let tuple_struct = TupleStruct(7, 3.14, "test".to_string());
    let tuple = SoAble::into_tuple(tuple_struct);
    assert_eq!(tuple, (7, 3.14, "test".to_string()));

    let back = TupleStruct::from_tuple((42, 2.71, "hello".to_string()));
    assert_eq!(back.0, 42);
    assert_eq!(back.1, 2.71);
    assert_eq!(back.2, "hello".to_string());
}
