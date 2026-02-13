use formality_core::test;

mod borrowck_loan_kills;

/// Check sharing a field from a leased value errs.
#[test]
#[allow(non_snake_case)]
fn share_field_of_leased_value() {
    crate::assert_err!({
                class Data { }

                class Foo {
                    i: Data;
                }

                class Main {
                    fn main(given self) {
                        let foo = new Foo(new Data());
                        let bar = foo.mut;
                        let i = foo.i.ref;
                        bar.give;
                        ();
                    }
                }
            }, expect_test::expect![[r#"
                the rule "check_class" at (classes.rs) failed because
                  judgment `check_method { decl: fn main (given self) -> () { let foo = new Foo (new Data ()) ; let bar = foo . mut ; let i = foo . i . ref ; bar . give ; () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "check_method" at (methods.rs) failed because
                      judgment `check_body { body: { let foo = new Foo (new Data ()) ; let bar = foo . mut ; let i = foo . i . ref ; bar . give ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                        the rule "block" at (methods.rs) failed because
                          judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . mut ; let i = foo . i . ref ; bar . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "can_type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . mut ; let i = foo . i . ref ; bar . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "type_expr_as" at (expressions.rs) failed because
                                  judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; let bar = foo . mut ; let i = foo . i . ref ; bar . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "block" at (expressions.rs) failed because
                                      judgment `type_block { block: { let foo = new Foo (new Data ()) ; let bar = foo . mut ; let i = foo . i . ref ; bar . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "place" at (blocks.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, let bar = foo . mut ;, let i = foo . i . ref ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let bar = foo . mut ;, let i = foo . i . ref ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statements_with_final_ty { statements: [let i = foo . i . ref ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: mut [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "cons" at (statements.rs) failed because
                                                      judgment `type_statement { statement: let i = foo . i . ref ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: mut [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "let" at (statements.rs) failed because
                                                          judgment `type_expr { expr: foo . i . ref, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: mut [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "ref|mut place" at (expressions.rs) failed because
                                                              judgment `access_permitted { access: ref, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: mut [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                                the rule "access_permitted" at (accesses.rs) failed because
                                                                  judgment `env_permits_access { access: ref, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: mut [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                                    the rule "env_permits_access" at (accesses.rs) failed because
                                                                      judgment `parameters_permit_access { parameters: [mut [foo] Foo], access: ref, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: mut [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "cons" at (accesses.rs) failed because
                                                                          judgment `parameter_permits_access { parameter: mut [foo] Foo, access: ref, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: mut [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "parameter" at (accesses.rs) failed because
                                                                              judgment `lien_permit_access { lien: mt(foo), access: ref, accessed_place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: mut [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "mut'd" at (accesses.rs) failed because
                                                                                  judgment `mut_place_permits_access { leased_place: foo, access: ref, accessed_place: foo . i }` failed at the following rule(s):
                                                                                    the rule "lease-mutation" at (accesses.rs) failed because
                                                                                      condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                                                                                        &accessed_place = foo . i
                                                                                        &leased_place = foo"#]])
}

/// Check sharing a field from a shared value is ok.
#[test]
#[allow(non_snake_case)]
fn share_field_of_shared_value() {
    crate::assert_ok!({
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn main(given self) {
                    let foo = new Foo(new Data());
                    let bar = foo.ref;
                    let i = foo.i.ref;
                    bar.give;
                    ();
                }
            }
        })
}

/// Check leasing a field from a shared value is not ok.
#[test]
#[allow(non_snake_case)]
fn lease_field_of_shared_value() {
    crate::assert_err!({
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn main(given self) {
                    let foo = new Foo(new Data());
                    let bar = foo.ref;
                    let i = foo.i.mut;
                    bar.give;
                    ();
                }
            }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn main (given self) -> () { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = foo . i . mut ; bar . give ; () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = foo . i . mut ; bar . give ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = foo . i . mut ; bar . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = foo . i . mut ; bar . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = foo . i . mut ; bar . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = foo . i . mut ; bar . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, let bar = foo . ref ;, let i = foo . i . mut ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let bar = foo . ref ;, let i = foo . i . mut ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let i = foo . i . mut ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statement { statement: let i = foo . i . mut ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "let" at (statements.rs) failed because
                                                      judgment `type_expr { expr: foo . i . mut, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "ref|mut place" at (expressions.rs) failed because
                                                          judgment `access_permitted { access: mut, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "access_permitted" at (accesses.rs) failed because
                                                              judgment `env_permits_access { access: mut, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                                the rule "env_permits_access" at (accesses.rs) failed because
                                                                  judgment `parameters_permit_access { parameters: [ref [foo] Foo], access: mut, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "cons" at (accesses.rs) failed because
                                                                      judgment `parameter_permits_access { parameter: ref [foo] Foo, access: mut, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "parameter" at (accesses.rs) failed because
                                                                          judgment `lien_permit_access { lien: rf(foo), access: mut, accessed_place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "ref'd" at (accesses.rs) failed because
                                                                              judgment `ref_place_permits_access { shared_place: foo, access: mut, accessed_place: foo . i }` failed at the following rule(s):
                                                                                the rule "share-mutation" at (accesses.rs) failed because
                                                                                  condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                                                                                    &accessed_place = foo . i
                                                                                    &shared_place = foo"#]])
}

/// Check giving a field from a shared value is not ok.
#[test]
#[allow(non_snake_case)]
fn give_field_of_shared_value() {
    crate::assert_err!({
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn main(given self) {
                    let foo = new Foo(new Data());
                    let bar = foo.ref;
                    let i = foo.i.give;
                    bar.give;
                    ();
                }
            }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn main (given self) -> () { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = foo . i . give ; bar . give ; () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = foo . i . give ; bar . give ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = foo . i . give ; bar . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = foo . i . give ; bar . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = foo . i . give ; bar . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = foo . i . give ; bar . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, let bar = foo . ref ;, let i = foo . i . give ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let bar = foo . ref ;, let i = foo . i . give ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let i = foo . i . give ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statement { statement: let i = foo . i . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "let" at (statements.rs) failed because
                                                      judgment `type_expr { expr: foo . i . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "give place" at (expressions.rs) failed because
                                                          judgment `access_permitted { access: give, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "access_permitted" at (accesses.rs) failed because
                                                              judgment `env_permits_access { access: give, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                                the rule "env_permits_access" at (accesses.rs) failed because
                                                                  judgment `parameters_permit_access { parameters: [ref [foo] Foo], access: give, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "cons" at (accesses.rs) failed because
                                                                      judgment `parameter_permits_access { parameter: ref [foo] Foo, access: give, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "parameter" at (accesses.rs) failed because
                                                                          judgment `lien_permit_access { lien: rf(foo), access: give, accessed_place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "ref'd" at (accesses.rs) failed because
                                                                              judgment `ref_place_permits_access { shared_place: foo, access: give, accessed_place: foo . i }` failed at the following rule(s):
                                                                                the rule "share-give" at (accesses.rs) failed because
                                                                                  condition evaluted to false: `place_disjoint_from_or_prefix_of(&accessed_place, &shared_place)`
                                                                                    &accessed_place = foo . i
                                                                                    &shared_place = foo"#]])
}

/// Check sharing a field from a leased value errs.
#[test]
#[allow(non_snake_case)]
fn share_field_of_leased_value_after_explicit_give() {
    crate::assert_ok!({
                class Data { }

                class Foo {
                    i: Data;
                }

                class Main {
                    fn main(given self) {
                        let foo = new Foo(new Data());
                        let bar = foo.mut;
                        bar.give;
                        let i = foo.i.ref;
                        ();
                    }
                }
            })
}

/// Check that we can permit accessing `foo.i` even though
/// it was leased since `bar` is dead.
#[test]
#[allow(non_snake_case)]
fn share_field_of_leased_value_without_explicit_give() {
    crate::assert_ok!({
                class Data { }

                class Foo {
                    i: Data;
                }

                class Main {
                    fn main(given self) {
                        let foo = new Foo(new Data());
                        let bar = foo.mut;
                        let i = foo.i.ref;
                        ();
                    }
                }
            })
}

#[test]
fn share_field_of_leased_value_but_lease_variable_is_dead() {
    // Here, the variable `q` is dead, but its restrictions must
    // still be enforced because `r` is live.
    crate::assert_err!({
                class Data { }

                class Foo {
                    i: Data;
                }

                class Main {
                    fn main(given self) {
                        let p = new Foo(new Data());
                        let q = p.mut;
                        let r = q.ref;
                        let i = p.i.ref;
                        r.give;
                        ();
                    }
                }
            }, expect_test::expect![[r#"
                the rule "check_class" at (classes.rs) failed because
                  judgment `check_method { decl: fn main (given self) -> () { let p = new Foo (new Data ()) ; let q = p . mut ; let r = q . ref ; let i = p . i . ref ; r . give ; () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "check_method" at (methods.rs) failed because
                      judgment `check_body { body: { let p = new Foo (new Data ()) ; let q = p . mut ; let r = q . ref ; let i = p . i . ref ; r . give ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                        the rule "block" at (methods.rs) failed because
                          judgment `can_type_expr_as { expr: { let p = new Foo (new Data ()) ; let q = p . mut ; let r = q . ref ; let i = p . i . ref ; r . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "can_type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr_as { expr: { let p = new Foo (new Data ()) ; let q = p . mut ; let r = q . ref ; let i = p . i . ref ; r . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "type_expr_as" at (expressions.rs) failed because
                                  judgment `type_expr { expr: { let p = new Foo (new Data ()) ; let q = p . mut ; let r = q . ref ; let i = p . i . ref ; r . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "block" at (expressions.rs) failed because
                                      judgment `type_block { block: { let p = new Foo (new Data ()) ; let q = p . mut ; let r = q . ref ; let i = p . i . ref ; r . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "place" at (blocks.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let p = new Foo (new Data ()) ;, let q = p . mut ;, let r = q . ref ;, let i = p . i . ref ;, r . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let q = p . mut ;, let r = q . ref ;, let i = p . i . ref ;, r . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statements_with_final_ty { statements: [let r = q . ref ;, let i = p . i . ref ;, r . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: Foo, q: mut [p] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "cons" at (statements.rs) failed because
                                                      judgment `type_statements_with_final_ty { statements: [let i = p . i . ref ;, r . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "cons" at (statements.rs) failed because
                                                          judgment `type_statement { statement: let i = p . i . ref ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "let" at (statements.rs) failed because
                                                              judgment `type_expr { expr: p . i . ref, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                                the rule "ref|mut place" at (expressions.rs) failed because
                                                                  judgment `access_permitted { access: ref, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                                    the rule "access_permitted" at (accesses.rs) failed because
                                                                      judgment `env_permits_access { access: ref, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                                        the rule "env_permits_access" at (accesses.rs) failed because
                                                                          judgment `parameters_permit_access { parameters: [ref [q] Foo], access: ref, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "cons" at (accesses.rs) failed because
                                                                              judgment `parameter_permits_access { parameter: ref [q] Foo, access: ref, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "parameter" at (accesses.rs) failed because
                                                                                  judgment `"flat_map"` failed at the following rule(s):
                                                                                    failed at (quantifiers.rs) because
                                                                                      judgment `lien_permit_access { lien: mt(p), access: ref, accessed_place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "mut'd" at (accesses.rs) failed because
                                                                                          judgment `mut_place_permits_access { leased_place: p, access: ref, accessed_place: p . i }` failed at the following rule(s):
                                                                                            the rule "lease-mutation" at (accesses.rs) failed because
                                                                                              condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                                                                                                &accessed_place = p . i
                                                                                                &leased_place = p"#]])
}

#[test]
fn share_field_of_leased_value_but_lease_variable_is_dead_explicit_ty() {
    // Here, the variable `q` is dead, but its restrictions must
    // still be enforced because `r` is live.
    crate::assert_err!({
                class Data { }

                class Foo {
                    i: Data;
                }

                class Main {
                    fn main(given self) {
                        let p: given Foo = new Foo(new Data());
                        let q: mut[p] Foo = p.mut;
                        let r: ref[q] Foo = q.ref;
                        let i: ref[p.i] Data = p.i.ref;
                        r.give;
                        ();
                    }
                }
            }, expect_test::expect![[r#"
                the rule "check_class" at (classes.rs) failed because
                  judgment `check_method { decl: fn main (given self) -> () { let p : given Foo = new Foo (new Data ()) ; let q : mut [p] Foo = p . mut ; let r : ref [q] Foo = q . ref ; let i : ref [p . i] Data = p . i . ref ; r . give ; () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "check_method" at (methods.rs) failed because
                      judgment `check_body { body: { let p : given Foo = new Foo (new Data ()) ; let q : mut [p] Foo = p . mut ; let r : ref [q] Foo = q . ref ; let i : ref [p . i] Data = p . i . ref ; r . give ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                        the rule "block" at (methods.rs) failed because
                          judgment `can_type_expr_as { expr: { let p : given Foo = new Foo (new Data ()) ; let q : mut [p] Foo = p . mut ; let r : ref [q] Foo = q . ref ; let i : ref [p . i] Data = p . i . ref ; r . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "can_type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr_as { expr: { let p : given Foo = new Foo (new Data ()) ; let q : mut [p] Foo = p . mut ; let r : ref [q] Foo = q . ref ; let i : ref [p . i] Data = p . i . ref ; r . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "type_expr_as" at (expressions.rs) failed because
                                  judgment `type_expr { expr: { let p : given Foo = new Foo (new Data ()) ; let q : mut [p] Foo = p . mut ; let r : ref [q] Foo = q . ref ; let i : ref [p . i] Data = p . i . ref ; r . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "block" at (expressions.rs) failed because
                                      judgment `type_block { block: { let p : given Foo = new Foo (new Data ()) ; let q : mut [p] Foo = p . mut ; let r : ref [q] Foo = q . ref ; let i : ref [p . i] Data = p . i . ref ; r . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "place" at (blocks.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let p : given Foo = new Foo (new Data ()) ;, let q : mut [p] Foo = p . mut ;, let r : ref [q] Foo = q . ref ;, let i : ref [p . i] Data = p . i . ref ;, r . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let q : mut [p] Foo = p . mut ;, let r : ref [q] Foo = q . ref ;, let i : ref [p . i] Data = p . i . ref ;, r . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: given Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statements_with_final_ty { statements: [let r : ref [q] Foo = q . ref ;, let i : ref [p . i] Data = p . i . ref ;, r . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: given Foo, q: mut [p] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "cons" at (statements.rs) failed because
                                                      judgment `type_statements_with_final_ty { statements: [let i : ref [p . i] Data = p . i . ref ;, r . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: given Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "cons" at (statements.rs) failed because
                                                          judgment `type_statement { statement: let i : ref [p . i] Data = p . i . ref ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: given Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "let" at (statements.rs) failed because
                                                              judgment `type_expr_as { expr: p . i . ref, as_ty: ref [p . i] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: given Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                                the rule "type_expr_as" at (expressions.rs) failed because
                                                                  judgment `type_expr { expr: p . i . ref, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: given Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                                    the rule "ref|mut place" at (expressions.rs) failed because
                                                                      judgment `access_permitted { access: ref, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: given Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                                        the rule "access_permitted" at (accesses.rs) failed because
                                                                          judgment `env_permits_access { access: ref, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: given Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                                            the rule "env_permits_access" at (accesses.rs) failed because
                                                                              judgment `parameters_permit_access { parameters: [ref [q] Foo], access: ref, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: given Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "cons" at (accesses.rs) failed because
                                                                                  judgment `parameter_permits_access { parameter: ref [q] Foo, access: ref, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: given Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "parameter" at (accesses.rs) failed because
                                                                                      judgment `"flat_map"` failed at the following rule(s):
                                                                                        failed at (quantifiers.rs) because
                                                                                          judgment `lien_permit_access { lien: mt(p), access: ref, accessed_place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: given Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "mut'd" at (accesses.rs) failed because
                                                                                              judgment `mut_place_permits_access { leased_place: p, access: ref, accessed_place: p . i }` failed at the following rule(s):
                                                                                                the rule "lease-mutation" at (accesses.rs) failed because
                                                                                                  condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                                                                                                    &accessed_place = p . i
                                                                                                    &leased_place = p"#]])
}

/// Test where we expect data leased from self and then try to use self.
/// Error.
#[test]
#[allow(non_snake_case)]
fn pair_method__leased_self__use_self() {
    crate::assert_err!({
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, data: mut[self] Data) {
                  self.a.mut;
                  data.give;
                  ();
                }
            }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn method (given self data : mut [self] Data) -> () { self . a . mut ; data . give ; () ; }, class_ty: Pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { self . a . mut ; data . give ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { self . a . mut ; data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { self . a . mut ; data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { self . a . mut ; data . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { self . a . mut ; data . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [self . a . mut ;, data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statement { statement: self . a . mut ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                            the rule "expr" at (statements.rs) failed because
                                              judgment `type_expr { expr: self . a . mut, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                the rule "ref|mut place" at (expressions.rs) failed because
                                                  judgment `access_permitted { access: mut, place: self . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "access_permitted" at (accesses.rs) failed because
                                                      judgment `env_permits_access { access: mut, place: self . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "env_permits_access" at (accesses.rs) failed because
                                                          judgment `parameters_permit_access { parameters: [mut [self] Data], access: mut, place: self . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "cons" at (accesses.rs) failed because
                                                              judgment `parameter_permits_access { parameter: mut [self] Data, access: mut, place: self . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "parameter" at (accesses.rs) failed because
                                                                  judgment `lien_permit_access { lien: mt(self), access: mut, accessed_place: self . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "mut'd" at (accesses.rs) failed because
                                                                      judgment `mut_place_permits_access { leased_place: self, access: mut, accessed_place: self . a }` failed at the following rule(s):
                                                                        the rule "lease-mutation" at (accesses.rs) failed because
                                                                          condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                                                                            &accessed_place = self . a
                                                                            &leased_place = self"#]])
}

/// Test that we cannot mutate fields of a shared class.
#[test]
#[allow(non_snake_case)]
fn mutate_field_of_shared_pair() {
    crate::assert_err!({
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, data: given Data) {
                  let me = self.ref;
                  me.a = data.give;
                  ();
                }
            }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn method (given self data : given Data) -> () { let me = self . ref ; me . a = data . give ; () ; }, class_ty: Pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let me = self . ref ; me . a = data . give ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let me = self . ref ; me . a = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let me = self . ref ; me . a = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let me = self . ref ; me . a = data . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let me = self . ref ; me . a = data . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let me = self . ref ;, me . a = data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [me . a = data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: given Data, me: ref [self] Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statement { statement: me . a = data . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: given Data, me: ref [self] Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "reassign" at (statements.rs) failed because
                                                  judgment `prove_is_move { a: ref [self] Pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, @ fresh(0): Data, data: given Data, me: ref [self] Pair}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                    the rule "is-moved" at (predicates.rs) failed because
                                                      judgment `prove_predicate { predicate: move(ref [self] Pair), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, @ fresh(0): Data, data: given Data, me: ref [self] Pair}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                        the rule "mut => move" at (predicates.rs) failed because
                                                          judgment `prove_is_mut { a: ref [self] Pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, @ fresh(0): Data, data: given Data, me: ref [self] Pair}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                            the rule "is-mut" at (predicates.rs) failed because
                                                              judgment `prove_predicate { predicate: mut(ref [self] Pair), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, @ fresh(0): Data, data: given Data, me: ref [self] Pair}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                the rule "parameter" at (predicates.rs) failed because
                                                                  pattern `true` did not match value `false`
                                                        the rule "parameter" at (predicates.rs) failed because
                                                          pattern `true` did not match value `false`"#]])
}

/// Test that we cannot mutate fields of a shared class.
#[test]
#[allow(non_snake_case)]
fn mutate_field_of_our_pair() {
    crate::assert_err!({
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, pair: shared Pair, data: given Data) {
                  pair.a = data.give;
                  ();
                }
            }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn method (given self pair : shared Pair, data : given Data) -> () { pair . a = data . give ; () ; }, class_ty: Pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { pair . a = data . give ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: given Data, pair: shared Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { pair . a = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: given Data, pair: shared Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { pair . a = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: given Data, pair: shared Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { pair . a = data . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: given Data, pair: shared Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { pair . a = data . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: given Data, pair: shared Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [pair . a = data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: given Data, pair: shared Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statement { statement: pair . a = data . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: given Data, pair: shared Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "reassign" at (statements.rs) failed because
                                              judgment `prove_is_move { a: shared Pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, @ fresh(0): Data, data: given Data, pair: shared Pair}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                the rule "is-moved" at (predicates.rs) failed because
                                                  judgment `prove_predicate { predicate: move(shared Pair), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, @ fresh(0): Data, data: given Data, pair: shared Pair}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                    the rule "mut => move" at (predicates.rs) failed because
                                                      judgment `prove_is_mut { a: shared Pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, @ fresh(0): Data, data: given Data, pair: shared Pair}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                        the rule "is-mut" at (predicates.rs) failed because
                                                          judgment `prove_predicate { predicate: mut(shared Pair), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, @ fresh(0): Data, data: given Data, pair: shared Pair}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                            the rule "parameter" at (predicates.rs) failed because
                                                              pattern `true` did not match value `false`
                                                    the rule "parameter" at (predicates.rs) failed because
                                                      pattern `true` did not match value `false`"#]])
}

/// Test that we can mutate fields of a leased class.
#[test]
#[allow(non_snake_case)]
fn mutate_field_of_leased_pair() {
    crate::assert_ok!({
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, data: given Data) {
                  let me = self.mut;
                  me.a = data.give;
                  ();
                }
            }
        })
}

// Test that we can give from `shared` and go on using it
#[test]
#[allow(non_snake_case)]
fn give_our_then_use_later_and_return() {
    crate::assert_ok!({
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, data: shared Data) -> shared Data {
                  let d: shared Data = data.give;
                  let e: shared Data = data.give;
                  let f: shared Data = data.give;
                  d.give;
                }
            }
        })
}

// Test that we can give from `shared` and go on using it
#[test]
#[allow(non_snake_case)]
fn give_shared_then_use_later_and_return() {
    crate::assert_ok!({
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, owner: given Data, data: ref[owner] Data) -> ref[owner] Data {
                  let d: ref[owner] Data = data.give;
                  let e: ref[owner] Data = data.give;
                  let f: ref[owner] Data = data.give;
                  d.give;
                }
            }
        })
}

// Test that we can give from `shared` and go on using it
#[test]
#[allow(non_snake_case)]
fn take_given_and_shared_move_given_then_return_shared() {
    crate::assert_err!({
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, owner: given Data, data: ref[owner] Data) -> ref[owner] Data {
                  let d: ref[owner] Data = data.give;
                  let owner1: given Data = owner.give;
                  d.give;
                }
            }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn method (given self owner : given Data, data : ref [owner] Data) -> ref [owner] Data { let d : ref [owner] Data = data . give ; let owner1 : given Data = owner . give ; d . give ; }, class_ty: Pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let d : ref [owner] Data = data . give ; let owner1 : given Data = owner . give ; d . give ; }, output: ref [owner] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: ref [owner] Data, owner: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let d : ref [owner] Data = data . give ; let owner1 : given Data = owner . give ; d . give ; }, as_ty: ref [owner] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: ref [owner] Data, owner: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let d : ref [owner] Data = data . give ; let owner1 : given Data = owner . give ; d . give ; }, as_ty: ref [owner] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, data: ref [owner] Data, owner: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: ref [owner1] Data, b: ref [owner] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: given Data, owner1: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_perms { perm_a: ref [owner1], perm_b: ref [owner], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: given Data, owner1: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                      judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Rfd(owner1)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Rfd(owner)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: given Data, owner1: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                          judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Rfd(owner1)] }, red_chain_b: RedChain { links: [Rfd(owner)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: given Data, owner1: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "(ref-dead::P) vs Q ~~> (shared::P) vs Q" at (redperms.rs) failed because
                                              judgment `prove_is_mut { a: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: given Data, owner1: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "is-mut" at (predicates.rs) failed because
                                                  judgment `prove_predicate { predicate: mut(given), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: given Data, owner1: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "parameter" at (predicates.rs) failed because
                                                      pattern `true` did not match value `false`
                                            the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
                                              condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                                place_b = owner
                                                &place_a = owner1
                                            the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                              judgment `prove_is_copy_owned { a: ref [owner1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: given Data, owner1: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "prove" at (predicates.rs) failed because
                                                  judgment `prove_is_owned { a: ref [owner1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: given Data, owner1: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "is-owned" at (predicates.rs) failed because
                                                      judgment `prove_predicate { predicate: owned(ref [owner1]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: given Data, owner1: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "parameter" at (predicates.rs) failed because
                                                          pattern `true` did not match value `false`"#]])
}

/// Interesting example from [conversation with Isaac][r]. In this example,
/// when `bar` calls `foo`, it takes a *locally leased* copy of `y` -- but since
/// `y` is stored into `x.value`, it escapes, and hence is no longer usable.
///
/// In Dada this is accepted because `mut(y) B R[Int]` can be converted to `B R[Int]`
/// so long as `y` is dead (as long as B is shared/leased).
///
/// [r]: https://gitlab.inf.ethz.ch/public-plf/borrowck-examples/-/blob/db0ece7ab20404935e4cf381471f425b41e6c009/tests/passing/reborrowing-escape-function.md
#[test]
fn escapes_ok() {
    crate::assert_ok!({
          class R[ty T] {
            value: T;
          }

          class Main {
            fn foo[perm A, perm B](given self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              mut(A),
              mut(B),
            {
              ();
            }

            fn bar[perm A, perm B](given self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              mut(A),
              mut(B),
            {
              self.give.foo[A, B](x.give, y.mut);
            }
          }
    });

    // fn foo<'a, 'b>(x : &'a mut &'b mut i32, y : &'b mut i32) {
    //   () // For example: *x = y;
    // }

    // fn bar<'a, 'b>(u : &'a mut &'b mut i32, v : &'b mut i32) {
    //   foo(u, &mut *v);
    // }

    // fn main() {}
}

/// See `escapes_ok`, but here we use `y` again (and hence get an error).
#[test]
fn escapes_err_use_again() {
    crate::assert_err!({
          class R[ty T] {
            value: T;
          }

          class Main {
            fn foo[perm A, perm B](given self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              mut(A),
              mut(B),
            {
              ();
            }

            fn bar[perm A, perm B](given self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              mut(A),
              mut(B),
            {
              self.give.foo[A, B](x.give, y.mut);
              y.give;
            }
          }
    }, expect_test::expect![[r#"
        the rule "check_class" at (classes.rs) failed because
          judgment `check_method { decl: fn bar [perm, perm] (given self x : ^perm0_0 R[^perm0_1 R[Int]], y : ^perm0_1 R[Int]) -> () where mut(^perm0_0), mut(^perm0_1) { self . give . foo [^perm0_0, ^perm0_1] (x . give, y . mut) ; y . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
            the rule "check_method" at (methods.rs) failed because
              judgment `check_body { body: { self . give . foo [!perm_0, !perm_1] (x . give, y . mut) ; y . give ; }, output: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                the rule "block" at (methods.rs) failed because
                  judgment `can_type_expr_as { expr: { self . give . foo [!perm_0, !perm_1] (x . give, y . mut) ; y . give ; }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                    the rule "can_type_expr_as" at (expressions.rs) failed because
                      judgment `type_expr_as { expr: { self . give . foo [!perm_0, !perm_1] (x . give, y . mut) ; y . give ; }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr { expr: { self . give . foo [!perm_0, !perm_1] (x . give, y . mut) ; y . give ; }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "block" at (expressions.rs) failed because
                              judgment `type_block { block: { self . give . foo [!perm_0, !perm_1] (x . give, y . mut) ; y . give ; }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "place" at (blocks.rs) failed because
                                  judgment `type_statements_with_final_ty { statements: [self . give . foo [!perm_0, !perm_1] (x . give, y . mut) ;, y . give ;], ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "cons" at (statements.rs) failed because
                                      judgment `type_statement { statement: self . give . foo [!perm_0, !perm_1] (x . give, y . mut) ;, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {y}, traversed: {} } }` failed at the following rule(s):
                                        the rule "expr" at (statements.rs) failed because
                                          judgment `type_expr { expr: self . give . foo [!perm_0, !perm_1] (x . give, y . mut), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {y}, traversed: {} } }` failed at the following rule(s):
                                            the rule "call" at (expressions.rs) failed because
                                              judgment `type_method_arguments_as { exprs: [x . give, y . mut], input_temps: [@ fresh(0)], input_names: [x, y], input_tys: [!perm_0 R[!perm_1 R[Int]], !perm_1 R[Int]], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, @ fresh(0): given Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 1 }, live_after: LivePlaces { accessed: {y}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (expressions.rs) failed because
                                                  judgment `type_method_arguments_as { exprs: [y . mut], input_temps: [@ fresh(1), @ fresh(0)], input_names: [y], input_tys: [!perm_1 R[Int]], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, @ fresh(0): given Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 2 }, live_after: LivePlaces { accessed: {y}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "cons" at (expressions.rs) failed because
                                                      judgment `sub { a: mut [y] R[Int], b: !perm_1 R[Int], live_after: LivePlaces { accessed: {@ fresh(0), @ fresh(1), y}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, @ fresh(0): given Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                        the rule "sub-classes" at (subtypes.rs) failed because
                                                          judgment `sub_perms { perm_a: mut [y], perm_b: !perm_1, live_after: LivePlaces { accessed: {@ fresh(0), @ fresh(1), y}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, @ fresh(0): given Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                                              judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Mtl(y), Var(!perm_1)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Var(!perm_1)] }} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, @ fresh(0): given Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                                  judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtl(y), Var(!perm_1)] }, red_chain_b: RedChain { links: [Var(!perm_1)] }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, @ fresh(0): given Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                    the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                                                      judgment `prove_is_copy_owned { a: mut [y], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, @ fresh(0): given Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                        the rule "prove" at (predicates.rs) failed because
                                                                          judgment `prove_is_copy { a: mut [y], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, @ fresh(0): given Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                            the rule "is" at (predicates.rs) failed because
                                                                              judgment `prove_predicate { predicate: copy(mut [y]), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, @ fresh(0): given Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                                the rule "parameter" at (predicates.rs) failed because
                                                                                  pattern `true` did not match value `false`"#]]);
}

/// See `escapes_ok`, but here we don't know that `B` is leased (and hence get an error).
/// In particular you can't convert e.g. `mut[y] given R[Int]`.
///
/// Equivalent in Rust would be
///
/// ```rust
/// fn foo(x: &mut T, y: T) { }
///
/// fn bar(x: &mut T, y: T) {
///     foo(x, &mut y);
/// }
/// ```
#[test]
fn escapes_err_not_leased() {
    crate::assert_err!({
          class R[ty T] {
            value: T;
          }

          class Main {
            fn foo[perm A, perm B](given self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              mut(A),
            {
              ();
            }

            fn bar[perm A, perm B](given self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              mut(A),
            {
              self.give.foo[A, B](x.give, y.mut);
            }
          }
    }, expect_test::expect![[r#"
        the rule "check_class" at (classes.rs) failed because
          judgment `check_method { decl: fn bar [perm, perm] (given self x : ^perm0_0 R[^perm0_1 R[Int]], y : ^perm0_1 R[Int]) -> () where mut(^perm0_0) { self . give . foo [^perm0_0, ^perm0_1] (x . give, y . mut) ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
            the rule "check_method" at (methods.rs) failed because
              judgment `check_body { body: { self . give . foo [!perm_0, !perm_1] (x . give, y . mut) ; }, output: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                the rule "block" at (methods.rs) failed because
                  judgment `can_type_expr_as { expr: { self . give . foo [!perm_0, !perm_1] (x . give, y . mut) ; }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                    the rule "can_type_expr_as" at (expressions.rs) failed because
                      judgment `type_expr_as { expr: { self . give . foo [!perm_0, !perm_1] (x . give, y . mut) ; }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr { expr: { self . give . foo [!perm_0, !perm_1] (x . give, y . mut) ; }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "block" at (expressions.rs) failed because
                              judgment `type_block { block: { self . give . foo [!perm_0, !perm_1] (x . give, y . mut) ; }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "place" at (blocks.rs) failed because
                                  judgment `type_statements_with_final_ty { statements: [self . give . foo [!perm_0, !perm_1] (x . give, y . mut) ;], ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "cons" at (statements.rs) failed because
                                      judgment `type_statement { statement: self . give . foo [!perm_0, !perm_1] (x . give, y . mut) ;, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "expr" at (statements.rs) failed because
                                          judgment `type_expr { expr: self . give . foo [!perm_0, !perm_1] (x . give, y . mut), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "call" at (expressions.rs) failed because
                                              judgment `type_method_arguments_as { exprs: [x . give, y . mut], input_temps: [@ fresh(0)], input_names: [x, y], input_tys: [!perm_0 R[!perm_1 R[Int]], !perm_1 R[Int]], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, @ fresh(0): given Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (expressions.rs) failed because
                                                  judgment `type_method_arguments_as { exprs: [y . mut], input_temps: [@ fresh(1), @ fresh(0)], input_names: [y], input_tys: [!perm_1 R[Int]], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, @ fresh(0): given Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 2 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "cons" at (expressions.rs) failed because
                                                      judgment `sub { a: mut [y] R[Int], b: !perm_1 R[Int], live_after: LivePlaces { accessed: {@ fresh(0), @ fresh(1)}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, @ fresh(0): given Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                        the rule "sub-classes" at (subtypes.rs) failed because
                                                          judgment `sub_perms { perm_a: mut [y], perm_b: !perm_1, live_after: LivePlaces { accessed: {@ fresh(0), @ fresh(1)}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, @ fresh(0): given Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                                              judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Mtd(y), Var(!perm_1)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Var(!perm_1)] }} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, @ fresh(0): given Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                                  judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtd(y), Var(!perm_1)] }, red_chain_b: RedChain { links: [Var(!perm_1)] }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, @ fresh(0): given Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                    the rule "(mut-dead::P) vs Q ~~> (P) vs Q" at (redperms.rs) failed because
                                                                      judgment `prove_is_mut { a: !perm_1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, @ fresh(0): given Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                        the rule "is-mut" at (predicates.rs) failed because
                                                                          judgment `prove_predicate { predicate: mut(!perm_1), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, @ fresh(0): given Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                              pattern `true` did not match value `false`
                                                                    the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                                                      judgment `prove_is_copy_owned { a: mut [y], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, @ fresh(0): given Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                        the rule "prove" at (predicates.rs) failed because
                                                                          judgment `prove_is_copy { a: mut [y], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, @ fresh(0): given Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                            the rule "is" at (predicates.rs) failed because
                                                                              judgment `prove_predicate { predicate: copy(mut [y]), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, @ fresh(0): given Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {mut(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                                the rule "parameter" at (predicates.rs) failed because
                                                                                  pattern `true` did not match value `false`"#]]);
}

/// Check that a `ref[d1, d2]` in parameters prohibits writes to `d1`.
#[test]
fn shared_d1_in_parameters() {
    crate::assert_err!({
          class Pair[ty T] {
            value1: T;
            value2: T;
          }

          class Data { }

          class Main {
            fn main(given self) {
              let d1 = new Data();
              let d2 = new Data();
              let p = new Pair[ref[d1, d2] Data](d1.ref, d2.ref);
              d1 = new Data();
              let _keep_alive = p.give;
            }
          }
    }, expect_test::expect![[r#"
        the rule "check_class" at (classes.rs) failed because
          judgment `check_method { decl: fn main (given self) -> () { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ; d1 = new Data () ; let _keep_alive = p . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
            the rule "check_method" at (methods.rs) failed because
              judgment `check_body { body: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ; d1 = new Data () ; let _keep_alive = p . give ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "block" at (methods.rs) failed because
                  judgment `can_type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ; d1 = new Data () ; let _keep_alive = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                    the rule "can_type_expr_as" at (expressions.rs) failed because
                      judgment `type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ; d1 = new Data () ; let _keep_alive = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ; d1 = new Data () ; let _keep_alive = p . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "block" at (expressions.rs) failed because
                              judgment `type_block { block: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ; d1 = new Data () ; let _keep_alive = p . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "place" at (blocks.rs) failed because
                                  judgment `type_statements_with_final_ty { statements: [let d1 = new Data () ;, let d2 = new Data () ;, let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ;, d1 = new Data () ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "cons" at (statements.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let d2 = new Data () ;, let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ;, d1 = new Data () ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ;, d1 = new Data () ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [d1 = new Data () ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statement { statement: d1 = new Data () ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "reassign" at (statements.rs) failed because
                                                      judgment `env_permits_access { access: mut, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "env_permits_access" at (accesses.rs) failed because
                                                          judgment `parameters_permit_access { parameters: [Pair[ref [d1, d2] Data]], access: mut, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                            the rule "cons" at (accesses.rs) failed because
                                                              judgment `parameter_permits_access { parameter: Pair[ref [d1, d2] Data], access: mut, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                the rule "parameter" at (accesses.rs) failed because
                                                                  judgment `lien_permit_access { lien: rf(d1), access: mut, accessed_place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                    the rule "ref'd" at (accesses.rs) failed because
                                                                      judgment `ref_place_permits_access { shared_place: d1, access: mut, accessed_place: d1 }` failed at the following rule(s):
                                                                        the rule "share-mutation" at (accesses.rs) failed because
                                                                          condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                                                                            &accessed_place = d1
                                                                            &shared_place = d1"#]]);
}

/// Check that a `ref[d1, d2]` in parameters prohibits writes to `d2`.
#[test]
fn shared_d2_in_parameters() {
    crate::assert_err!({
          class Pair[ty T] {
            value1: T;
            value2: T;
          }

          class Data { }

          class Main {
            fn main(given self) {
              let d1 = new Data();
              let d2 = new Data();
              let p = new Pair[ref[d1, d2] Data](d1.ref, d2.ref);
              d2 = new Data();
              let _keep_alive = p.give;
            }
          }
    }, expect_test::expect![[r#"
        the rule "check_class" at (classes.rs) failed because
          judgment `check_method { decl: fn main (given self) -> () { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ; d2 = new Data () ; let _keep_alive = p . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
            the rule "check_method" at (methods.rs) failed because
              judgment `check_body { body: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ; d2 = new Data () ; let _keep_alive = p . give ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "block" at (methods.rs) failed because
                  judgment `can_type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ; d2 = new Data () ; let _keep_alive = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                    the rule "can_type_expr_as" at (expressions.rs) failed because
                      judgment `type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ; d2 = new Data () ; let _keep_alive = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ; d2 = new Data () ; let _keep_alive = p . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "block" at (expressions.rs) failed because
                              judgment `type_block { block: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ; d2 = new Data () ; let _keep_alive = p . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "place" at (blocks.rs) failed because
                                  judgment `type_statements_with_final_ty { statements: [let d1 = new Data () ;, let d2 = new Data () ;, let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ;, d2 = new Data () ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "cons" at (statements.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let d2 = new Data () ;, let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ;, d2 = new Data () ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ;, d2 = new Data () ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [d2 = new Data () ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statement { statement: d2 = new Data () ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "reassign" at (statements.rs) failed because
                                                      judgment `env_permits_access { access: mut, place: d2, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "env_permits_access" at (accesses.rs) failed because
                                                          judgment `parameters_permit_access { parameters: [Pair[ref [d1, d2] Data]], access: mut, place: d2, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                            the rule "cons" at (accesses.rs) failed because
                                                              judgment `parameter_permits_access { parameter: Pair[ref [d1, d2] Data], access: mut, place: d2, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                the rule "parameter" at (accesses.rs) failed because
                                                                  judgment `"flat_map"` failed at the following rule(s):
                                                                    failed at (quantifiers.rs) because
                                                                      judgment `lien_permit_access { lien: rf(d2), access: mut, accessed_place: d2, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                        the rule "ref'd" at (accesses.rs) failed because
                                                                          judgment `ref_place_permits_access { shared_place: d2, access: mut, accessed_place: d2 }` failed at the following rule(s):
                                                                            the rule "share-mutation" at (accesses.rs) failed because
                                                                              condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                                                                                &accessed_place = d2
                                                                                &shared_place = d2"#]]);
}

/// Check that a `mut[d1, d2]` in parameters prohibits reads from `d1`.
#[test]
fn leased_d1_in_parameters() {
    crate::assert_err!({
          class Pair[ty T] {
            value1: T;
            value2: T;
          }

          class Data { }

          class Main {
            fn main(given self) {
              let d1 = new Data();
              let d2 = new Data();
              let p = new Pair[mut[d1, d2] Data](d1.mut, d2.mut);
              d1.ref;
              let _keep_alive = p.give;
            }
          }
    }, expect_test::expect![[r#"
        the rule "check_class" at (classes.rs) failed because
          judgment `check_method { decl: fn main (given self) -> () { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [mut [d1, d2] Data] (d1 . mut, d2 . mut) ; d1 . ref ; let _keep_alive = p . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
            the rule "check_method" at (methods.rs) failed because
              judgment `check_body { body: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [mut [d1, d2] Data] (d1 . mut, d2 . mut) ; d1 . ref ; let _keep_alive = p . give ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "block" at (methods.rs) failed because
                  judgment `can_type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [mut [d1, d2] Data] (d1 . mut, d2 . mut) ; d1 . ref ; let _keep_alive = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                    the rule "can_type_expr_as" at (expressions.rs) failed because
                      judgment `type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [mut [d1, d2] Data] (d1 . mut, d2 . mut) ; d1 . ref ; let _keep_alive = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [mut [d1, d2] Data] (d1 . mut, d2 . mut) ; d1 . ref ; let _keep_alive = p . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "block" at (expressions.rs) failed because
                              judgment `type_block { block: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [mut [d1, d2] Data] (d1 . mut, d2 . mut) ; d1 . ref ; let _keep_alive = p . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "place" at (blocks.rs) failed because
                                  judgment `type_statements_with_final_ty { statements: [let d1 = new Data () ;, let d2 = new Data () ;, let p = new Pair [mut [d1, d2] Data] (d1 . mut, d2 . mut) ;, d1 . ref ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "cons" at (statements.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let d2 = new Data () ;, let p = new Pair [mut [d1, d2] Data] (d1 . mut, d2 . mut) ;, d1 . ref ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let p = new Pair [mut [d1, d2] Data] (d1 . mut, d2 . mut) ;, d1 . ref ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [d1 . ref ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: Data, d2: Data, p: Pair[mut [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statement { statement: d1 . ref ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: Data, d2: Data, p: Pair[mut [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "expr" at (statements.rs) failed because
                                                      judgment `type_expr { expr: d1 . ref, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: Data, d2: Data, p: Pair[mut [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "ref|mut place" at (expressions.rs) failed because
                                                          judgment `access_permitted { access: ref, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: Data, d2: Data, p: Pair[mut [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "access_permitted" at (accesses.rs) failed because
                                                              judgment `env_permits_access { access: ref, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: Data, d2: Data, p: Pair[mut [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                                the rule "env_permits_access" at (accesses.rs) failed because
                                                                  judgment `parameters_permit_access { parameters: [Pair[mut [d1, d2] Data]], access: ref, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: Data, d2: Data, p: Pair[mut [d1, d2] Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "cons" at (accesses.rs) failed because
                                                                      judgment `parameter_permits_access { parameter: Pair[mut [d1, d2] Data], access: ref, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: Data, d2: Data, p: Pair[mut [d1, d2] Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "parameter" at (accesses.rs) failed because
                                                                          judgment `lien_permit_access { lien: mt(d1), access: ref, accessed_place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: Data, d2: Data, p: Pair[mut [d1, d2] Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "mut'd" at (accesses.rs) failed because
                                                                              judgment `mut_place_permits_access { leased_place: d1, access: ref, accessed_place: d1 }` failed at the following rule(s):
                                                                                the rule "lease-mutation" at (accesses.rs) failed because
                                                                                  condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                                                                                    &accessed_place = d1
                                                                                    &leased_place = d1"#]]);
}
