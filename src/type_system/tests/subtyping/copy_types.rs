//! Tests that permissions on copy types are no-ops.
//!
//! Copy types include `Int`, `()`, shared classes, and generic shared classes
//! whose type parameters are all copy. Applying any permission to a copy type
//! should produce an equivalent type — `ref[p] Int` is just `Int`, etc.

use formality_core::test;

// -------------------------------------------------------------------
// Int: permissions are identity
// -------------------------------------------------------------------

#[test]
fn ref_int_to_int() {
    // ref[self] Int <: Int — borrow of a copy type is just the type
    crate::assert_ok!({
        class Main {
            fn test(given self) -> Int {
                let x: ref[self] Int = 0;
                x.give;
            }
        }
    });
}

#[test]
fn int_to_ref_int() {
    // Int <: ref[self] Int
    crate::assert_ok!({
        class Main {
            fn test(given self) -> Int {
                let x: Int = 0;
                let y: ref[self] Int = x.give;
                y.give;
            }
        }
    });
}

#[test]
fn shared_int_to_int() {
    // shared Int <: Int
    crate::assert_ok!({
        class Main {
            fn test(given self) -> Int {
                let x: shared Int = 0;
                x.give;
            }
        }
    });
}

#[test]
fn int_to_shared_int() {
    // Int <: shared Int
    crate::assert_ok!({
        class Main {
            fn test(given self) -> Int {
                let x: Int = 0;
                let y: shared Int = x.give;
                y.give;
            }
        }
    });
}

#[test]
fn given_int_to_int() {
    // given Int <: Int (given is identity, but let's be explicit)
    crate::assert_ok!({
        class Main {
            fn test(given self) -> Int {
                let x: given Int = 0;
                x.give;
            }
        }
    });
}

#[test]
fn given_from_int_to_int() {
    // given_from[self] Int <: Int
    crate::assert_ok!({
        class Main {
            fn test(given self) -> Int {
                let x: given_from[self] Int = 0;
                x.give;
            }
        }
    });
}

// -------------------------------------------------------------------
// Struct class (always copy): permissions are identity
// -------------------------------------------------------------------

#[test]
fn ref_struct_to_struct() {
    crate::assert_ok!({
        shared class Point { x: Int; y: Int; }
        class Main {
            fn test(given self) -> Point {
                let p: ref[self] Point = new Point(1, 2);
                p.give;
            }
        }
    });
}

#[test]
fn struct_to_ref_struct() {
    crate::assert_ok!({
        shared class Point { x: Int; y: Int; }
        class Main {
            fn test(given self) -> Point {
                let p: Point = new Point(1, 2);
                let q: ref[self] Point = p.give;
                q.give;
            }
        }
    });
}

#[test]
fn shared_struct_to_struct() {
    crate::assert_ok!({
        shared class Point { x: Int; y: Int; }
        class Main {
            fn test(given self) -> Point {
                let p: shared Point = new Point(1, 2);
                p.give;
            }
        }
    });
}

// -------------------------------------------------------------------
// Generic shared class: copy iff type parameter is copy
// -------------------------------------------------------------------

#[test]
fn ref_generic_struct_copy_param_to_bare() {
    // Box[Int] is copy, so ref[self] Box[Int] <: Box[Int]
    crate::assert_ok!({
        shared class Box[ty T] { value: T; }
        class Main {
            fn test(given self) -> Box[Int] {
                let b: ref[self] Box[Int] = new Box[Int](42);
                b.give;
            }
        }
    });
}

#[test]
fn ref_generic_struct_noncopy_param_fails() {
    // Box[Data] is NOT copy (Data is a regular class), so ref[self] Box[Data] </: Box[Data]
    crate::assert_err!({
        shared class Box[ty T] { value: T; }
        class Data { }
        class Main {
            fn test(given self, d: given Data) -> Box[Data] {
                let b: ref[d] Box[Data] = new Box[Data](new Data());
                b.give;
            }
        }
    }, expect_test::expect![[r#"
        the rule "parameter" at (predicates.rs) failed because
          pattern `true` did not match value `false`

        the rule "parameter" at (predicates.rs) failed because
          pattern `true` did not match value `false`

        the rule "parameter" at (predicates.rs) failed because
          pattern `true` did not match value `false`

        the rule "parameter" at (predicates.rs) failed because
          pattern `true` did not match value `false`"#]]);
}

#[test]
fn shared_generic_struct_noncopy_param_fails() {
    // shared Box[Data] </: Box[Data]
    crate::assert_err!({
        shared class Box[ty T] { value: T; }
        class Data { }
        class Main {
            fn test(given self) -> Box[Data] {
                let b: shared Box[Data] = new Box[Data](new Data()).share;
                b.give;
            }
        }
    }, expect_test::expect![[r#"
        the rule "parameter" at (predicates.rs) failed because
          pattern `true` did not match value `false`

        the rule "parameter" at (predicates.rs) failed because
          pattern `true` did not match value `false`"#]]);
}
