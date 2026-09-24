//! Instantiates the crate's generic functions from an integration test.

#[test]
fn instantiates_from_outside() {
    known::must_assert_generic(&[1u16]);
    assert_eq!(known::must_generic_size_divide::<u64>(16), 2);
}
