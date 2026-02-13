use formality_core::test;

/// Check that we can give something which is shared and then go on
/// using the shared thing.
#[test]
fn give_while_shared_then_use() {
    crate::assert_ok!({
        class Data {}

        class Foo {
            i: Data;
        }

        class Main {
            fn main(given self) -> () {
                let foo = new Foo(new Data());
                let s = foo.i.ref;
                let bar = foo.give; // rewrites type of `s` to `shared(bar) Foo`
                bar.i.ref;
                s.give;
                ();
            }
        }
    })
}

/// Check that we can give something which is shared and then go on
/// using the shared thing.
#[test]
fn give_while_shared_then_drop() {
    crate::assert_ok!({
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn main(given self) -> () {
                let foo = new Foo(new Data());
                let s = foo.i.ref;
                let bar = foo.give; // rewrites type of `s` to `shared(bar) Foo`
                bar.i.give;
                ();
            }
        }
    })
}

/// Check that if we give while shared we can't then move out of the new name.
#[test]
fn give_while_shared_then_move_while_shared() {
    crate::assert_err!({
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn main(given self) -> () {
                let foo = new Foo(new Data());
                let s = foo.i.ref;

                // rewrites type of `s` to `shared(bar.i) Int`
                let bar = foo.give;

                // now we get an error here..
                bar.i.give;

                // ...because `s` is used again
                s.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "check_class" at (classes.rs) failed because
          judgment `check_method { decl: fn main (given self) -> () { let foo = new Foo (new Data ()) ; let s = foo . i . ref ; let bar = foo . give ; bar . i . give ; s . give ; () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
            the rule "check_method" at (methods.rs) failed because
              judgment `check_body { body: { let foo = new Foo (new Data ()) ; let s = foo . i . ref ; let bar = foo . give ; bar . i . give ; s . give ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "block" at (methods.rs) failed because
                  judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; let s = foo . i . ref ; let bar = foo . give ; bar . i . give ; s . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                    the rule "can_type_expr_as" at (expressions.rs) failed because
                      judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; let s = foo . i . ref ; let bar = foo . give ; bar . i . give ; s . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; let s = foo . i . ref ; let bar = foo . give ; bar . i . give ; s . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "block" at (expressions.rs) failed because
                              judgment `type_block { block: { let foo = new Foo (new Data ()) ; let s = foo . i . ref ; let bar = foo . give ; bar . i . give ; s . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "place" at (blocks.rs) failed because
                                  judgment `type_statements { statements: [let foo = new Foo (new Data ()) ;, let s = foo . i . ref ;, let bar = foo . give ;, bar . i . give ;, s . give ;, () ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "type_statements" at (statements.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, let s = foo . i . ref ;, let bar = foo . give ;, bar . i . give ;, s . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let s = foo . i . ref ;, let bar = foo . give ;, bar . i . give ;, s . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let bar = foo . give ;, bar . i . give ;, s . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo, s: ref [foo . i] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statements_with_final_ty { statements: [bar . i . give ;, s . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: Foo, foo: Foo, s: ref [bar . i] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "cons" at (statements.rs) failed because
                                                      judgment `type_statement { statement: bar . i . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: Foo, foo: Foo, s: ref [bar . i] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {s}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "expr" at (statements.rs) failed because
                                                          judgment `env_permits_access { access: drop, place: @ fresh(0), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Data, bar: Foo, foo: Foo, s: ref [@ fresh(0)] Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {s}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "env_permits_access" at (accesses.rs) failed because
                                                              judgment `parameters_permit_access { parameters: [ref [@ fresh(0)] Data], access: drop, place: @ fresh(0), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Data, bar: Foo, foo: Foo, s: ref [@ fresh(0)] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                the rule "cons" at (accesses.rs) failed because
                                                                  judgment `parameter_permits_access { parameter: ref [@ fresh(0)] Data, access: drop, place: @ fresh(0), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Data, bar: Foo, foo: Foo, s: ref [@ fresh(0)] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                    the rule "parameter" at (accesses.rs) failed because
                                                                      judgment `lien_permit_access { lien: rf(@ fresh(0)), access: drop, accessed_place: @ fresh(0), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Data, bar: Foo, foo: Foo, s: ref [@ fresh(0)] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                        the rule "ref'd" at (accesses.rs) failed because
                                                                          judgment `ref_place_permits_access { shared_place: @ fresh(0), access: drop, accessed_place: @ fresh(0) }` failed at the following rule(s):
                                                                            the rule "share-mutation" at (accesses.rs) failed because
                                                                              condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                                                                                &accessed_place = @ fresh(0)
                                                                                &shared_place = @ fresh(0)"#]])
}

/// Check that if we give while shared we can't then move out of the new name.
#[test]
fn give_while_shared_then_assign_while_shared() {
    crate::assert_ok!({
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn main(given self) -> () {
                let foo = new Foo(new Data());
                let s = foo.i.ref;

                // rewrites type of `s` to `shared(bar.i) Int`
                let bar = foo.give;

                // we can still assign `bar.i` to `d`...
                let d = new Data();
                d = bar.i.give;

                // ...even though `s` is used again;
                // the type of `s` becomes `shared(d)`
                s.give;
                ();
            }
        }
    })
}

/// Check that if we give while shared we can't then move out of the new name.
#[test]
fn give_while_shared_then_assign_while_shared_then_mutate_new_place() {
    crate::assert_err!({
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn main(given self) -> () {
                let foo = new Foo(new Data());
                let s = foo.i.ref;

                // rewrites type of `s` to `shared(bar.i) Int`
                let bar = foo.give;

                // we can still assign `bar.i` to `d`...
                let d = new Data();
                d = bar.i.give;

                // ...even though `s` is used again;
                // the type of `s` becomes `shared(d)`
                s.give;

                // but now we can't reassign `d`
                d = new Data();

                // when `s` is used again
                s.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "check_class" at (classes.rs) failed because
          judgment `check_method { decl: fn main (given self) -> () { let foo = new Foo (new Data ()) ; let s = foo . i . ref ; let bar = foo . give ; let d = new Data () ; d = bar . i . give ; s . give ; d = new Data () ; s . give ; () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
            the rule "check_method" at (methods.rs) failed because
              judgment `check_body { body: { let foo = new Foo (new Data ()) ; let s = foo . i . ref ; let bar = foo . give ; let d = new Data () ; d = bar . i . give ; s . give ; d = new Data () ; s . give ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "block" at (methods.rs) failed because
                  judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; let s = foo . i . ref ; let bar = foo . give ; let d = new Data () ; d = bar . i . give ; s . give ; d = new Data () ; s . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                    the rule "can_type_expr_as" at (expressions.rs) failed because
                      judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; let s = foo . i . ref ; let bar = foo . give ; let d = new Data () ; d = bar . i . give ; s . give ; d = new Data () ; s . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; let s = foo . i . ref ; let bar = foo . give ; let d = new Data () ; d = bar . i . give ; s . give ; d = new Data () ; s . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "block" at (expressions.rs) failed because
                              judgment `type_block { block: { let foo = new Foo (new Data ()) ; let s = foo . i . ref ; let bar = foo . give ; let d = new Data () ; d = bar . i . give ; s . give ; d = new Data () ; s . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "place" at (blocks.rs) failed because
                                  judgment `type_statements { statements: [let foo = new Foo (new Data ()) ;, let s = foo . i . ref ;, let bar = foo . give ;, let d = new Data () ;, d = bar . i . give ;, s . give ;, d = new Data () ;, s . give ;, () ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "type_statements" at (statements.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, let s = foo . i . ref ;, let bar = foo . give ;, let d = new Data () ;, d = bar . i . give ;, s . give ;, d = new Data () ;, s . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let s = foo . i . ref ;, let bar = foo . give ;, let d = new Data () ;, d = bar . i . give ;, s . give ;, d = new Data () ;, s . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let bar = foo . give ;, let d = new Data () ;, d = bar . i . give ;, s . give ;, d = new Data () ;, s . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo, s: ref [foo . i] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statements_with_final_ty { statements: [let d = new Data () ;, d = bar . i . give ;, s . give ;, d = new Data () ;, s . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: Foo, foo: Foo, s: ref [bar . i] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "cons" at (statements.rs) failed because
                                                      judgment `type_statements_with_final_ty { statements: [d = bar . i . give ;, s . give ;, d = new Data () ;, s . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: Foo, d: Data, foo: Foo, s: ref [bar . i] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "cons" at (statements.rs) failed because
                                                          judgment `type_statements_with_final_ty { statements: [s . give ;, d = new Data () ;, s . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: Foo, d: Data, foo: Foo, s: ref [d] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "cons" at (statements.rs) failed because
                                                              judgment `type_statements_with_final_ty { statements: [d = new Data () ;, s . give ;, () ;], ty: ref [d] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: Foo, d: Data, foo: Foo, s: ref [d] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                the rule "cons" at (statements.rs) failed because
                                                                  judgment `type_statement { statement: d = new Data () ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: Foo, d: Data, foo: Foo, s: ref [d] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {s}, traversed: {} } }` failed at the following rule(s):
                                                                    the rule "reassign" at (statements.rs) failed because
                                                                      judgment `env_permits_access { access: mut, place: d, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Data, bar: Foo, d: Data, foo: Foo, s: ref [d] Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {s}, traversed: {} } }` failed at the following rule(s):
                                                                        the rule "env_permits_access" at (accesses.rs) failed because
                                                                          judgment `parameters_permit_access { parameters: [ref [d] Data], access: mut, place: d, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Data, bar: Foo, d: Data, foo: Foo, s: ref [d] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                            the rule "cons" at (accesses.rs) failed because
                                                                              judgment `parameter_permits_access { parameter: ref [d] Data, access: mut, place: d, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Data, bar: Foo, d: Data, foo: Foo, s: ref [d] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                the rule "parameter" at (accesses.rs) failed because
                                                                                  judgment `lien_permit_access { lien: rf(d), access: mut, accessed_place: d, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Data, bar: Foo, d: Data, foo: Foo, s: ref [d] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                    the rule "ref'd" at (accesses.rs) failed because
                                                                                      judgment `ref_place_permits_access { shared_place: d, access: mut, accessed_place: d }` failed at the following rule(s):
                                                                                        the rule "share-mutation" at (accesses.rs) failed because
                                                                                          condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                                                                                            &accessed_place = d
                                                                                            &shared_place = d"#]])
}
