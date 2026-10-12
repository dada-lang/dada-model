//! Tests that permissions on copy types are no-ops.
//!
//! Copy types include `Int`, `()`, shared structs, and generic shared structs
//! whose type parameters are all copy. Applying any permission to a copy type
//! should produce an equivalent type — `shared[p] Int` is just `Int`, etc.

use formality_core::test;

// -------------------------------------------------------------------
// Int: permissions are identity
// -------------------------------------------------------------------

#[test]
fn ref_int_to_int() {
    // shared[self] Int <: Int — borrow of a copy type is just the type
    crate::assert_ok!(
        r#"
        struct Main {
            fn test(given self) → Int {
                let x: shared[self] Int = 0;
                x→;
            }
        }
    "#
    );
}

#[test]
fn int_to_ref_int() {
    // Int <: shared[self] Int
    crate::assert_ok!(
        r#"
        struct Main {
            fn test(given self) → Int {
                let x: Int = 0;
                let y: shared[self] Int = x→;
                y→;
            }
        }
    "#
    );
}

#[test]
fn shared_int_to_int() {
    // shared Int <: Int
    crate::assert_ok!(
        r#"
        struct Main {
            fn test(given self) → Int {
                let x: shared Int = 0;
                x→;
            }
        }
    "#
    );
}

#[test]
fn int_to_shared_int() {
    // Int <: shared Int
    crate::assert_ok!(
        r#"
        struct Main {
            fn test(given self) → Int {
                let x: Int = 0;
                let y: shared Int = x→;
                y→;
            }
        }
    "#
    );
}

#[test]
fn given_int_to_int() {
    // given Int <: Int (given is identity, but let's be explicit)
    crate::assert_ok!(
        r#"
        struct Main {
            fn test(given self) → Int {
                let x: given Int = 0;
                x→;
            }
        }
    "#
    );
}

#[test]
fn given_from_int_to_int() {
    // given[self] Int <: Int
    crate::assert_ok!(
        r#"
        struct Main {
            fn test(given self) → Int {
                let x: given[self] Int = 0;
                x→;
            }
        }
    "#
    );
}

// -------------------------------------------------------------------
// Struct class (always copy): permissions are identity
// -------------------------------------------------------------------

#[test]
fn ref_struct_to_struct() {
    crate::assert_ok!(
        r#"
        shared struct Point { x: Int; y: Int; }
        struct Main {
            fn test(given self) → Point {
                let p: shared[self] Point = new Point(1, 2);
                p→;
            }
        }
    "#
    );
}

#[test]
fn struct_to_ref_struct() {
    crate::assert_ok!(
        r#"
        shared struct Point { x: Int; y: Int; }
        struct Main {
            fn test(given self) → Point {
                let p: Point = new Point(1, 2);
                let q: shared[self] Point = p→;
                q→;
            }
        }
    "#
    );
}

#[test]
fn shared_struct_to_struct() {
    crate::assert_ok!(
        r#"
        shared struct Point { x: Int; y: Int; }
        struct Main {
            fn test(given self) → Point {
                let p: shared Point = new Point(1, 2);
                p→;
            }
        }
    "#
    );
}

// -------------------------------------------------------------------
// Generic shared struct: copy iff type parameter is shared
// -------------------------------------------------------------------

#[test]
fn ref_generic_struct_copy_param_to_bare() {
    // Box[Int] is shared, so shared[self] Box[Int] <: Box[Int]
    crate::assert_ok!(
        r#"
        shared struct Box[type T] { value: T; }
        struct Main {
            fn test(given self) → Box[Int] {
                let b: shared[self] Box[Int] = new Box[Int](42);
                b→;
            }
        }
    "#
    );
}

#[test]
fn ref_generic_struct_noncopy_param_fails() {
    // Box[Data] is NOT copy (Data is a regular class), so shared[self] Box[Data] </: Box[Data]
    crate::assert_err!(r#"
        shared struct Box[type T] { value: T; }
        struct Data { }
        struct Main {
            fn test(given self, d: given Data) → Box[Data] {
                let b: shared[d] Box[Data] = new Box[Data](new Data());
                b→;
            }
        }
    "#, expect_test::expect!["judgment had no applicable rules: `check_program { program: shared struct Box [type] { value : ^type0_0 ; } struct Data { } struct Main { fn test (given self d : given Data) → Box[Data] { let b : shared [d] Box[Data] = new Box [Data] (new Data ()) ; b → ; } } }`"]);
}

#[test]
fn shared_generic_struct_noncopy_param_fails() {
    // shared Box[Data] </: Box[Data]
    crate::assert_err!(r#"
        shared struct Box[type T] { value: T; }
        struct Data { }
        struct Main {
            fn test(given self) → Box[Data] {
                let b: shared Box[Data] = new Box[Data](new Data()).share;
                b→;
            }
        }
    "#, expect_test::expect!["judgment had no applicable rules: `check_program { program: shared struct Box [type] { value : ^type0_0 ; } struct Data { } struct Main { fn test (given self) → Box[Data] { let b : shared Box[Data] = new Box [Data] (new Data ()) . share ; b → ; } } }`"]);
}
