use formality_core::test;

/// Check we are able to type check an empty method.
#[test]
fn empty_method() {
    crate::assert_ok!("
        class TheClass {
            fn empty_method(my self) {}
        }
        ");
}

/// Check that empty blocks return unit (and that is not assignable to Int)
#[test]
fn bad_int_return_value() {
    crate::assert_err!("
            class TheClass {
                fn empty_method(my self) -> Int {}
            }
        ", expect_test::expect![[r#"judgment had no applicable rules: `can_type_expr_as { expr: { }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }`"#]])
}

/// Check that empty blocks return unit (and that is not assignable to Int)
#[test]
fn bad_int_ascription() {
    crate::assert_err!("
            class TheClass {
                fn empty_method(my self) {
                    let x: Int = ();
                }
            }
        ", expect_test::expect![[r#"judgment had no applicable rules: `can_type_expr_as { expr: { let x : Int = () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }`"#]])
}

/// Check returning an integer with return type of Int.
#[test]
fn good_int_return_value() {
    crate::assert_ok!("
        class TheClass {
            fn empty_method(my self) -> Int {
                22;
            }
        }
    ");
}

/// Check returning an instance of a class.
#[test]
#[allow(non_snake_case)]
fn return_instance_of_Foo() {
    crate::assert_ok!("
        class Foo { }

        class TheClass {
            fn empty_method(my self) -> Foo {
                new Foo();
            }
        }
    ");
}

/// Check returning an instance of a class.
#[test]
#[allow(non_snake_case)]
fn return_from_variable() {
    crate::assert_ok!("
        class Foo { }

        class TheClass {
            fn empty_method(my self) -> Foo {
                let foo = new Foo();
                foo.move;
            }
        }
    ");
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn return_shared_not_give() {
    crate::assert_err!("
            class Foo { }
    
            class TheClass {
                fn empty_method(my self) -> Foo {
                    let foo = new Foo();
                    foo.ref;
                }
            }
        ", expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]])
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn return_int_field_from_class_with_int_field() {
    crate::assert_ok!("
        class Foo {
            i: Int;
        }

        class TheClass {
            fn empty_method(my self) -> Int {
                let foo = new Foo(22);
                foo.i.move;
            }
        }
    ");
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn return_modified_int_field_from_class_with_int_field() {
    crate::assert_ok!("
        class Foo {
            i: Int;
        }

        class TheClass {
            fn empty_method(my self) -> Int {
                let foo = new Foo(22);
                foo.i = foo.i.move + 1;
                foo.i.move;
            }
        }
    ");
}
