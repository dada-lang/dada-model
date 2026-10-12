use formality_core::test;

mod array_ops;
mod assignment;
mod cancellation;
mod class_defn_wf;
mod drop_body;
mod fn_calls;
mod given_classes;
mod mdbook;
mod move_check;
mod new_with_self_references;
mod or_perm;
mod permission_check;
mod predicate_quantifiers;
mod shared_classes_permissions;
mod shared_classes_subtyping;
mod subpermission;
mod subtyping;
mod type_check;
mod variance_subtyping;
mod vector;

/// Check what happens when we encounter a bad class name in a function parameter.
#[test]
fn bad_class_name_in_fn_parameter() {
    crate::assert_err!(
        "
        struct OtherClass {
            fn no_such_class(
                given self,
                c: given TypeName,
            ) -> () {}
        }
    ",
        expect_test::expect![[r#"
            the rule "apply_perm" at (types.rs) failed because
              condition evaluted to false: `*perm != Perm::Given`

            the rule "named" at (types.rs) failed because
              check class name `TypeName`"#]]
    );
}

/// Check what happens when we encounter a bad class name in a function parameter.
#[test]
fn ok_field_name_in_fn_parameter() {
    crate::assert_ok!(
        "
        struct Point {
            x: shared Int;
            y: shared Int;

            fn no_such_class(
                given self,
                c: given Point,
                x: shared[c.x] Int,
                y: shared[c.y] Int,
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
        struct Point {
            x: shared Int;
            y: shared Int;

            fn no_such_class(
                given self,
                c: given Point,
                x: shared[c.z] Int,
            ) -> () {}
        }
    ",
        expect_test::expect![[r#"
            the rule "check_place" at (types.rs) failed because
              field `z` not found in type `given Point` (found: [x, y])"#]]
    );
}
