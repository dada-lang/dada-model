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
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn no_such_class (given self c : given TypeName) -> () { }, class_ty: OtherClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_type { ty: given TypeName, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given OtherClass, c: given TypeName}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "apply_perm" at (types.rs) failed because
                      judgment `check_type { ty: TypeName, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given OtherClass, c: given TypeName}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
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
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn no_such_class (given self c : given Point, x : ref [c . z] Int) -> () { }, class_ty: Point, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `"flat_map"` failed at the following rule(s):
                    failed at (quantifiers.rs) because
                      judgment `check_type { ty: ref [c . z] Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Point, c: given Point, x: ref [c . z] Int}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                        the rule "apply_perm" at (types.rs) failed because
                          judgment `check_perm { perm: ref [c . z], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Point, c: given Point, x: ref [c . z] Int}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                            the rule "ref" at (types.rs) failed because
                              judgment `check_place { place: c . z, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Point, c: given Point, x: ref [c . z] Int}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                the rule "check_place" at (types.rs) failed because
                                  field `z` not found in type `given Point` (found: [x, y])"#]]
    );
}
