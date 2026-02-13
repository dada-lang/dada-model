use formality_core::test;

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn give_same_field_twice() {
    crate::assert_err!({
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn main(given self) -> Int {
                let foo = new Foo(new Data());
                foo.i.give;
                foo.i.give;
            }
        }
    }, expect_test::expect![[r#"
        the rule "check_class" at (classes.rs) failed because
          judgment `check_method { decl: fn main (given self) -> Int { let foo = new Foo (new Data ()) ; foo . i . give ; foo . i . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
            the rule "check_method" at (methods.rs) failed because
              judgment `check_body { body: { let foo = new Foo (new Data ()) ; foo . i . give ; foo . i . give ; }, output: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "block" at (methods.rs) failed because
                  judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; foo . i . give ; foo . i . give ; }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                    the rule "can_type_expr_as" at (expressions.rs) failed because
                      judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; foo . i . give ; foo . i . give ; }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; foo . i . give ; foo . i . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "block" at (expressions.rs) failed because
                              judgment `type_block { block: { let foo = new Foo (new Data ()) ; foo . i . give ; foo . i . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "place" at (blocks.rs) failed because
                                  judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, foo . i . give ;, foo . i . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "cons" at (statements.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [foo . i . give ;, foo . i . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statement { statement: foo . i . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo . i}, traversed: {} } }` failed at the following rule(s):
                                            the rule "expr" at (statements.rs) failed because
                                              judgment `type_expr { expr: foo . i . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo . i}, traversed: {} } }` failed at the following rule(s):
                                                the rule "give place" at (expressions.rs) failed because
                                                  judgment `move_place { place: foo . i, ty: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo . i}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "copy" at (expressions.rs) failed because
                                                      judgment `prove_is_copy { a: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "is" at (predicates.rs) failed because
                                                          judgment `prove_predicate { predicate: copy(Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "parameter" at (predicates.rs) failed because
                                                              pattern `true` did not match value `false`
                                                    the rule "give" at (expressions.rs) failed because
                                                      condition evaluted to false: `!live_after.is_live(&place)`
                                                        live_after = LivePlaces { accessed: {foo . i}, traversed: {} }
                                                        &place = foo . i"#]])
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn give_field_of_moved_variable() {
    crate::assert_err!({
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn main(given self) -> Int {
                    let foo = new Foo(new Data());
                    foo.give;
                    foo.i.give;
                }
            }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn main (given self) -> Int { let foo = new Foo (new Data ()) ; foo . give ; foo . i . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let foo = new Foo (new Data ()) ; foo . give ; foo . i . give ; }, output: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; foo . give ; foo . i . give ; }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; foo . give ; foo . i . give ; }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; foo . give ; foo . i . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let foo = new Foo (new Data ()) ; foo . give ; foo . i . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, foo . give ;, foo . i . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [foo . give ;, foo . i . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statement { statement: foo . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo . i}, traversed: {} } }` failed at the following rule(s):
                                                the rule "expr" at (statements.rs) failed because
                                                  judgment `type_expr { expr: foo . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo . i}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "give place" at (expressions.rs) failed because
                                                      judgment `move_place { place: foo, ty: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo . i}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "copy" at (expressions.rs) failed because
                                                          judgment `prove_is_copy { a: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "is" at (predicates.rs) failed because
                                                              judgment `prove_predicate { predicate: copy(Foo), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "parameter" at (predicates.rs) failed because
                                                                  pattern `true` did not match value `false`
                                                        the rule "give" at (expressions.rs) failed because
                                                          condition evaluted to false: `!live_after.is_live(&place)`
                                                            live_after = LivePlaces { accessed: {foo . i}, traversed: {} }
                                                            &place = foo"#]])
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn give_variable_with_moved_field() {
    crate::assert_err!({
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn main(given self) -> Int {
                    let foo = new Foo(new Data());
                    foo.i.give;
                    foo.give;
                }
            }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn main (given self) -> Int { let foo = new Foo (new Data ()) ; foo . i . give ; foo . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let foo = new Foo (new Data ()) ; foo . i . give ; foo . give ; }, output: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; foo . i . give ; foo . give ; }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; foo . i . give ; foo . give ; }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; foo . i . give ; foo . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let foo = new Foo (new Data ()) ; foo . i . give ; foo . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, foo . i . give ;, foo . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [foo . i . give ;, foo . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statement { statement: foo . i . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo}, traversed: {} } }` failed at the following rule(s):
                                                the rule "expr" at (statements.rs) failed because
                                                  judgment `type_expr { expr: foo . i . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "give place" at (expressions.rs) failed because
                                                      judgment `move_place { place: foo . i, ty: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "copy" at (expressions.rs) failed because
                                                          judgment `prove_is_copy { a: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "is" at (predicates.rs) failed because
                                                              judgment `prove_predicate { predicate: copy(Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "parameter" at (predicates.rs) failed because
                                                                  pattern `true` did not match value `false`
                                                        the rule "give" at (expressions.rs) failed because
                                                          condition evaluted to false: `!live_after.is_live(&place)`
                                                            live_after = LivePlaces { accessed: {foo}, traversed: {} }
                                                            &place = foo . i"#]])
}

/// Check giving a shared value twice (giving a shared value doesn't consume it).
#[test]
#[allow(non_snake_case)]
fn give_shared_value() {
    crate::assert_ok!({
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn main(given self) {
                let foo = new Foo(new Data());
                let bar = foo.ref;
                bar.give;
                bar.give;
                ();
            }
        }
    })
}

/// Check giving a leased value twice errors.
#[test]
#[allow(non_snake_case)]
fn give_leased_value() {
    crate::assert_err!({
              class Data { }

              class Foo {
                  i: Data;
              }

              class Main {
                  fn main(given self) {
                      let foo = new Foo(new Data());
                      let bar = foo.mut;
                      bar.give;
                      bar.give;
                      ();
                  }
              }
          }, expect_test::expect![[r#"
              the rule "check_class" at (classes.rs) failed because
                judgment `check_method { decl: fn main (given self) -> () { let foo = new Foo (new Data ()) ; let bar = foo . mut ; bar . give ; bar . give ; () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                  the rule "check_method" at (methods.rs) failed because
                    judgment `check_body { body: { let foo = new Foo (new Data ()) ; let bar = foo . mut ; bar . give ; bar . give ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                      the rule "block" at (methods.rs) failed because
                        judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . mut ; bar . give ; bar . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                          the rule "can_type_expr_as" at (expressions.rs) failed because
                            judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . mut ; bar . give ; bar . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                              the rule "type_expr_as" at (expressions.rs) failed because
                                judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; let bar = foo . mut ; bar . give ; bar . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                  the rule "block" at (expressions.rs) failed because
                                    judgment `type_block { block: { let foo = new Foo (new Data ()) ; let bar = foo . mut ; bar . give ; bar . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                      the rule "place" at (blocks.rs) failed because
                                        judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, let bar = foo . mut ;, bar . give ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                          the rule "cons" at (statements.rs) failed because
                                            judgment `type_statements_with_final_ty { statements: [let bar = foo . mut ;, bar . give ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                              the rule "cons" at (statements.rs) failed because
                                                judgment `type_statements_with_final_ty { statements: [bar . give ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: mut [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                  the rule "cons" at (statements.rs) failed because
                                                    judgment `type_statement { statement: bar . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: mut [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                      the rule "expr" at (statements.rs) failed because
                                                        judgment `type_expr { expr: bar . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: mut [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                          the rule "give place" at (expressions.rs) failed because
                                                            judgment `move_place { place: bar, ty: mut [foo] Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: mut [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                              the rule "copy" at (expressions.rs) failed because
                                                                judgment `prove_is_copy { a: mut [foo] Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: mut [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                  the rule "is" at (predicates.rs) failed because
                                                                    judgment `prove_predicate { predicate: copy(mut [foo] Foo), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: mut [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                      the rule "parameter" at (predicates.rs) failed because
                                                                        pattern `true` did not match value `false`
                                                              the rule "give" at (expressions.rs) failed because
                                                                condition evaluted to false: `!live_after.is_live(&place)`
                                                                  live_after = LivePlaces { accessed: {bar}, traversed: {} }
                                                                  &place = bar"#]])
}
