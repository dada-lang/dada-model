use crate::{core::grammar as core, dada_lang, surface};

#[test]
fn generated_permissions_follow_explicit_generics_receiver_first() {
    let source = r#"
        struct Container[ty T, perm P] where T is struct {
            value: P T;
            fn method[ty U, perm Q](!self, x: any T, y: !U, z: Q U) -> P T
                where Q is owned { self.share.other[P, Q](x^, y^, z^); }
        }
    "#;
    let expected: core::Program = dada_lang::term(
        r#"
        struct Container[ty T, perm P] where T is struct {
            value: P T;
            fn method[ty U, perm Q, perm R, perm S, perm V](R self, x: S T, y: V U, z: Q U) -> P T
                where Q is owned, R is mut, V is mut { self.share.other[P, Q](x^, y^, z^); }
        }
    "#,
    );
    assert_eq!(*surface::parse_program(source).unwrap(), expected);
}

#[test]
fn explicit_sugar_introduces_one_outer_permission_only() {
    let source = r#"
        struct Data {
            fn method(any self, x: any Array[Int], y: !Array[Int]) -> Array[Int] ...;
        }
    "#;
    let expected: core::Program = dada_lang::term(
        r#"
        struct Data {
            fn method[perm R, perm P, perm Q](R self, x: P Array[Int], y: Q Array[Int]) -> Array[Int]
                where Q is mut ...;
        }
    "#,
    );
    assert_eq!(*surface::parse_program(source).unwrap(), expected);
}

#[test]
fn sugar_is_not_accepted_in_fields_returns_or_nested_types() {
    for source in [
        "struct Data { x: any Int; }",
        "struct Data { x: !Int; }",
        "struct Data { fn method(^ self) -> any Int ...; }",
        "struct Data { fn method(^ self) -> !Int ...; }",
        "struct Data { fn method(^ self, x: Array[any Int]) ...; }",
        "struct Data { fn method(^ self, x: Array[!Int]) ...; }",
    ] {
        assert!(surface::parse_program(source).is_err(), "{source}");
    }
}

#[test]
fn permission_arguments_are_preserved_without_inference() {
    let source = r#"
        struct Data {
            fn method[ty T](any self, x: any T) { x^; }
            fn caller(^ self) { self.share.method[Int, shared[self], ^](1); }
        }
    "#;
    let expected: core::Program = dada_lang::term(
        r#"
        struct Data {
            fn method[ty T, perm R, perm P](R self, x: P T) { x^; }
            fn caller(^ self) { self.share.method[Int, shared[self], ^](1); }
        }
    "#,
    );
    assert_eq!(*surface::parse_program(source).unwrap(), expected);
}
