//! # Only classes have destructors
//!
//! A class may define a nonempty `drop` body. A struct or shared struct may not:
//! independent sharing requires data without a destructor. Empty `drop {}` is
//! represented identically to an absent body and is accepted for every category.
//! These paired programs use the same body and differ only in declaration kind.

#[test]
fn class_destructor_is_allowed() {
    crate::assert_ok!(r#" class Resource { drop { print(42); } } "#);
}

#[test]
fn struct_destructor_is_rejected() {
    crate::assert_err!(
        r#" struct Resource { drop { print(42); } } "#,
        expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Resource { drop { print(42) ; } } }`"]
    );
}

#[test]
fn shared_struct_destructor_is_rejected() {
    crate::assert_err!(
        r#" shared struct Resource { drop { print(42); } } "#,
        expect_test::expect!["judgment had no applicable rules: `check_program { program: shared struct Resource { drop { print(42) ; } } }`"]
    );
}
