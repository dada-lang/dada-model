use crate::dada_lang::term;
use formality_core::{test, test_util::ResultTestExt};

use super::check_program;

mod assignment;
mod cancellation;
mod class_defn_wf;
mod fn_calls;
mod move_check;
mod move_tracking;
mod new_with_self_references;
mod permission_check;
mod subtyping;
mod type_check;
mod value_types;
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
            x: shared Int;
            y: shared Int;

            fn no_such_class(
                my self,
                c: my Point, 
                x: shared{c.x} Int, 
                y: shared{c.y} Int,
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
            x: shared Int;
            y: shared Int;

            fn no_such_class(
                my self,
                c: my Point, 
                x: shared{c.z} Int,
            ) -> () {}
        }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Point { x : shared Int ; y : shared Int ; fn no_such_class (my self c : my Point, x : shared {c . z} Int) -> () { } }`

        Caused by:
            0: check class named `Point`
            1: check method named `no_such_class`
            2: check type `shared {c . z} Int`
            3: check_perm(shared {c . z}
            4: check place `c . z`
            5: judgment `place_ty { place: c . z, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Point, c: my Point, x: shared {c . z} Int}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                 the rule "place" failed at step #1 (src/file.rs:LL:CC) because
                   judgment `type_projections { base_place: c, base_ty: my Point, projections: [. z], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Point, c: my Point, x: shared {c . z} Int}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                     the rule "field" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `field_ty { base_ty: my Point, field: z, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Point, c: my Point, x: shared {c . z} Int}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "field" failed at step #2 (src/file.rs:LL:CC) because
                           condition evaluted to false: `field.name == field_name`"#]]);
}
