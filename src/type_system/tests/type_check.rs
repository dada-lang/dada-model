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
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn empty_method (given self) -> Int { }, class_ty: TheClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { }, output: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment had no applicable rules: `sub { a: (), b: Int, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 } }`"#]])
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
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn empty_method (given self) -> () { let x : Int = () ; }, class_ty: TheClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let x : Int = () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let x : Int = () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let x : Int = () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let x : Int = () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let x : Int = () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let x : Int = () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statement { statement: let x : Int = () ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "let" at (statements.rs) failed because
                                              judgment `type_expr_as { expr: (), as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "type_expr_as" at (expressions.rs) failed because
                                                  judgment had no applicable rules: `sub { a: (), b: Int, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 } }`"#]])
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
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn empty_method (given self) -> Foo { let foo = new Foo () ; foo . ref ; }, class_ty: TheClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let foo = new Foo () ; foo . ref ; }, output: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let foo = new Foo () ; foo . ref ; }, as_ty: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let foo = new Foo () ; foo . ref ; }, as_ty: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: ref [foo] Foo, b: Foo, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_perms { perm_a: ref [foo], perm_b: given, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                      judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Rfd(foo)] }, red_perm_b: RedPerm { chains: {RedChain { links: [] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                          judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Rfd(foo)] }, red_chain_b: RedChain { links: [] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "(ref-dead::P) vs Q ~~> (shared::P) vs Q" at (redperms.rs) failed because
                                              judgment `prove_is_mut { a: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "is-mut" at (predicates.rs) failed because
                                                  judgment `prove_predicate { predicate: mut(given), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "parameter" at (predicates.rs) failed because
                                                      pattern `true` did not match value `false`"#]])
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
