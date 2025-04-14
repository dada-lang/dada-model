use crate::dada_lang::term;
use formality_core::{test, test_util::ResultTestExt};

use super::check_program;

mod assignment;
mod cancellation;
mod class_defn_wf;
mod fn_calls;
mod lock_guard;
mod move_check;
mod move_tracking;
mod new_with_self_references;
mod permission_check;
mod subpermission;
mod subtyping;
mod type_check;
mod value_type_permissions;
mod value_type_subtyping;
mod variance_subtyping;

/// Check what happens when we encounter a bad class name in a function parameter.
#[test]
fn bad_class_name_in_fn_parameter() {
    check_program(&term(
        "
        class OtherClass {
            fn no_such_class(
                my self,
                c: my TypeName,
            ) -> () {}
        }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class OtherClass { fn no_such_class (my self c : my TypeName) -> () { } }`

        Caused by:
            0: check class named `OtherClass`
            1: check method named `no_such_class`
            2: check type `my TypeName`
            3: check type `TypeName`
            4: check class name `TypeName`
            5: no class named `TypeName`"#]]);
}

/// Check what happens when we encounter a bad class name in a function parameter.
#[test]
fn ok_field_name_in_fn_parameter() {
    check_program(&term(
        "
        class Point { 
            x: our Int;
            y: our Int;

            fn no_such_class(
                my self,
                c: my Point, 
                x: ref[c.x] Int,
                y: ref[c.y] Int,
            ) -> () {

            }
        }  
    ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

/// Check what happens when we encounter a bad class name in a function parameter.
#[test]
fn bad_field_name_in_fn_parameter() {
    check_program(&term(
        "
        class Point {
            x: our Int;
            y: our Int;

            fn no_such_class(
                my self,
                c: my Point, 
                x: ref[c.z] Int,
            ) -> () {}
        }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Point { x : our Int ; y : our Int ; fn no_such_class (my self c : my Point, x : ref [c . z] Int) -> () { } }`

        Caused by:
            0: check class named `Point`
            1: check method named `no_such_class`
            2: check type `ref [c . z] Int`
            3: check_perm(ref [c . z]
            4: check place `c . z`
            5: field `z` not found in type `my Point` (found: [x, y])"#]]);
}
