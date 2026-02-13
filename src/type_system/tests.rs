use formality_core::test;

mod assignment;
mod cancellation;
mod class_defn_wf;
mod fn_calls;
mod guard_classes;
mod move_check;
mod move_tracking;
mod new_with_self_references;
mod shared_classes_permissions;
mod shared_classes_subtyping;
mod permission_check;
mod subpermission;
mod subtyping;
mod type_check;
mod variance_subtyping;

/// Check what happens when we encounter a bad class name in a function parameter.
#[test]
fn bad_class_name_in_fn_parameter() {
    crate::assert_err!(
        "
        class OtherClass {
            fn no_such_class(
                given self,
                c: given TypeName,
            ) -> () {}
        }
    ",
        expect_test::expect![[r#"
            the rule "named" at (types.rs) failed because
              check class name `TypeName`"#]]
    );
}

/// Check what happens when we encounter a bad class name in a function parameter.
#[test]
fn ok_field_name_in_fn_parameter() {
    crate::assert_ok!(
        "
        class Point {
            x: shared Int;
            y: shared Int;

            fn no_such_class(
                given self,
                c: given Point,
                x: ref[c.x] Int,
                y: ref[c.y] Int,
            ) -> () {

            }
        }
    "
    );
}

/// Check what happens when we encounter a bad class name in a function parameter.
#[test]
fn bad_field_name_in_fn_parameter() {
    crate::assert_err!(
        "
        class Point {
            x: shared Int;
            y: shared Int;

            fn no_such_class(
                given self,
                c: given Point,
                x: ref[c.z] Int,
            ) -> () {}
        }
    ",
        expect_test::expect![[r#"
            the rule "check_place" at (types.rs) failed because
              field `z` not found in type `given Point` (found: [x, y])"#]]
    );
}
