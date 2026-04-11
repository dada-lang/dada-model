use formality_core::test;

/// Check we are able to type check an empty method.
#[test]
fn empty_method() {
    crate::assert_ok!({
        class TheClass {
            fn empty_method(given self) {}
        }
        });
}

/// Check that empty blocks return unit (and that is not assignable to Int)
#[test]
fn bad_int_return_value() {
    crate::assert_err!({
            class TheClass {
                fn empty_method(given self) -> Int {}
            }
        }, expect_test::expect![[r#"src/type_system/subtypes.rs:38:1: no applicable rules for sub { a: (), b: Int, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 } }"#]])
}

/// Check that empty blocks return unit (and that is not assignable to Int)
#[test]
fn bad_int_ascription() {
    crate::assert_err!({
            class TheClass {
                fn empty_method(given self) {
                    let x: Int = ();
                }
            }
        }, expect_test::expect![[r#"src/type_system/subtypes.rs:38:1: no applicable rules for sub { a: (), b: Int, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 } }"#]])
}

/// Check returning an integer with return type of Int.
#[test]
fn good_int_return_value() {
    crate::assert_ok!({
        class TheClass {
            fn empty_method(given self) -> Int {
                22;
            }
        }
    });
}

/// Check returning an instance of a class.
#[test]
#[allow(non_snake_case)]
fn return_instance_of_Foo() {
    crate::assert_ok!({
        class Foo { }

        class TheClass {
            fn empty_method(given self) -> Foo {
                new Foo();
            }
        }
    });
}

/// Check returning an instance of a class.
#[test]
#[allow(non_snake_case)]
fn return_from_variable() {
    crate::assert_ok!({
        class Foo { }

        class TheClass {
            fn empty_method(given self) -> Foo {
                let foo = new Foo();
                foo.give;
            }
        }
    });
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn return_shared_not_give() {
    crate::assert_err!({
            class Foo { }
    
            class TheClass {
                fn empty_method(given self) -> Foo {
                    let foo = new Foo();
                    foo.ref;
                }
            }
        }, expect_test::expect![[r#"
            the rule "keep non-popped link" at (pop_normalize.rs) failed because
              condition evaluated to false: `!link_references_popped(&link, &popped_vars)`
                &link = Rfd(foo)
                &popped_vars = [foo]

            src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, foo: Foo}, assumptions: {}, fresh: 0 } }

            src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, foo: Foo}, assumptions: {}, fresh: 0 } }"#]])
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn return_int_field_from_class_with_int_field() {
    crate::assert_ok!({
        class Foo {
            i: Int;
        }

        class TheClass {
            fn empty_method(given self) -> Int {
                let foo = new Foo(22);
                foo.i.give;
            }
        }
    });
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn return_modified_int_field_from_class_with_int_field() {
    crate::assert_ok!({
        class Foo {
            i: Int;
        }

        class TheClass {
            fn empty_method(given self) -> Int {
                let foo = new Foo(22);
                foo.i = foo.i.give + 1;
                foo.i.give;
            }
        }
    });
}
