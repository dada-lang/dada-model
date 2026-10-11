//! # Explicit ownership preserves a generic type
//!
//! `^` is the identity permission. Making it explicit on a generic input does
//! not require a relative bound on that type. This allows parameter migration
//! from the old owned default without adding constraints. A nonidentity shared
//! permission still requires the relative bound; the paired declarations test
//! that distinction through the surface pipeline.

#[test]
fn explicit_ownership_needs_no_relative_bound() {
    crate::assert_ok!({
        struct Channel[ty T] {
            fn send(^self, value: ^T) { (); }
        }
    });
}

#[test]
fn sharing_still_requires_a_relative_bound() {
    crate::assert_err!({
        struct Channel[ty T] {
            fn send(^self, value: shared T) { (); }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Channel [ty] { fn send (^ self value : shared ^ty1_0) -> () { () ; } } }`"]);
}
