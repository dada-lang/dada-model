use formality_core::test;

#[test]
fn give_int_value_twice() {
    crate::assert_ok!({
                class Foo {
                    i: Int;
                }

                class Main {
                    fn main(given self, foo: given Foo) {
                        foo.i.give;
                        foo.i.give;
                        ();
                    }
                }
            })
}

#[test]
fn give_point_value_twice() {
    crate::assert_ok!({
                struct class Point {
                    x: Int;
                    y: Int;
                }

                class Main {
                    fn main(given self) {
                        let p: Point = new Point(22, 44);
                        let q: Point = p.give;
                        let r: Point = p.give;
                        ();
                    }
                }
            })
}

#[test]
fn move_our_class_of_our_class_twice() {
    // `Pair[Elem]` is an `shared` type because both `Pair` and `Elem` are declared as `shared`.
    // Moving `p` twice is ok.
    crate::assert_ok!({
                struct class Elem { }

                struct class Pair[ty T] {
                    a: T;
                    b: T;
                }

                class Main {
                    fn main(given self) {
                        let p: Pair[Elem] = new Pair[Elem](new Elem(), new Elem());
                        let q = p.give;
                        let r = p.give;
                        ();
                    }
                }
            });
}

#[test]
fn move_our_class_of_regular_class_twice() {
    // `Pair[Elem]` is not an `shared` type even though `Pair` is declared as `shared`
    // because `Elem` is not. So moving `p` twice yields an error.
    crate::assert_err!({
                class Elem { }

                struct class Pair[ty T] {
                    a: T;
                    b: T;
                }

                class Main {
                    fn main(given self) {
                        let p: Pair[Elem] = new Pair[Elem](new Elem(), new Elem());
                        let q = p.give;
                        let r = p.give;
                        ();
                    }
                }
            }, expect_test::expect![[r#"
                the rule "check_class" at (classes.rs) failed because
                  judgment `check_method { decl: fn main (given self) -> () { let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ; let q = p . give ; let r = p . give ; () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "check_method" at (methods.rs) failed because
                      judgment `check_body { body: { let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ; let q = p . give ; let r = p . give ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                        the rule "block" at (methods.rs) failed because
                          judgment `can_type_expr_as { expr: { let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ; let q = p . give ; let r = p . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "can_type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr_as { expr: { let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ; let q = p . give ; let r = p . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "type_expr_as" at (expressions.rs) failed because
                                  judgment `type_expr { expr: { let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ; let q = p . give ; let r = p . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "block" at (expressions.rs) failed because
                                      judgment `type_block { block: { let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ; let q = p . give ; let r = p . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "place" at (blocks.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ;, let q = p . give ;, let r = p . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let q = p . give ;, let r = p . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: Pair[Elem]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statement { statement: let q = p . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: Pair[Elem]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "let" at (statements.rs) failed because
                                                      judgment `type_expr { expr: p . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: Pair[Elem]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "give place" at (expressions.rs) failed because
                                                          judgment `move_place { place: p, ty: Pair[Elem], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: Pair[Elem]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "copy" at (expressions.rs) failed because
                                                              judgment `prove_is_copy { a: Pair[Elem], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: Pair[Elem]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "is" at (predicates.rs) failed because
                                                                  judgment `prove_predicate { predicate: copy(Pair[Elem]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: Pair[Elem]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "parameter" at (predicates.rs) failed because
                                                                      pattern `true` did not match value `false`
                                                            the rule "give" at (expressions.rs) failed because
                                                              condition evaluted to false: `!live_after.is_live(&place)`
                                                                live_after = LivePlaces { accessed: {p}, traversed: {} }
                                                                &place = p"#]])
}

#[test]
fn mutate_field_of_our_class_applied_to_our() {
    // Because `Pair` is declared as an `shared` type, its fields cannot be individually
    // mutated when it is used with a non-shared type like `Elem`.
    crate::assert_err!({
                struct class Elem { }

                struct class Pair[ty T] {
                    a: T;
                    b: T;
                }

                class Main {
                    fn main(given self) {
                        let p: Pair[Elem] = new Pair[Elem](new Elem(), new Elem());
                        p.a = new Elem();
                        ();
                    }
                }
            }, expect_test::expect![[r#"
                the rule "check_class" at (classes.rs) failed because
                  judgment `check_method { decl: fn main (given self) -> () { let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ; p . a = new Elem () ; () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "check_method" at (methods.rs) failed because
                      judgment `check_body { body: { let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ; p . a = new Elem () ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                        the rule "block" at (methods.rs) failed because
                          judgment `can_type_expr_as { expr: { let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ; p . a = new Elem () ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "can_type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr_as { expr: { let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ; p . a = new Elem () ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "type_expr_as" at (expressions.rs) failed because
                                  judgment `type_expr { expr: { let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ; p . a = new Elem () ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "block" at (expressions.rs) failed because
                                      judgment `type_block { block: { let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ; p . a = new Elem () ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "place" at (blocks.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ;, p . a = new Elem () ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [p . a = new Elem () ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: Pair[Elem]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statement { statement: p . a = new Elem () ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, p: Pair[Elem]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "reassign" at (statements.rs) failed because
                                                      judgment `prove_is_move { a: Pair[Elem], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Elem, p: Pair[Elem]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                        the rule "is-moved" at (predicates.rs) failed because
                                                          judgment `prove_predicate { predicate: move(Pair[Elem]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Elem, p: Pair[Elem]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                            the rule "mut => move" at (predicates.rs) failed because
                                                              judgment `prove_is_mut { a: Pair[Elem], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Elem, p: Pair[Elem]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                the rule "is-mut" at (predicates.rs) failed because
                                                                  judgment `prove_predicate { predicate: mut(Pair[Elem]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Elem, p: Pair[Elem]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                    the rule "parameter" at (predicates.rs) failed because
                                                                      pattern `true` did not match value `false`
                                                            the rule "parameter" at (predicates.rs) failed because
                                                              pattern `true` did not match value `false`"#]])
}

#[test]
fn mutate_field_of_our_class_applied_to_share() {
    // Even though `Pair` is declared as an `shared` type, its fields can be individually
    // mutated when it is used with a non-shared type like `Elem`.
    //
    // FIXME: Is this good? Unclear, but it seems consistent with the idea that an `shared` class is
    // `shared` iff its generics are `shared`.
    crate::assert_ok!({
                class Elem { }

                struct class Pair[ty T] {
                    a: T;
                    b: T;
                }

                class Main {
                    fn main(given self) {
                        let p: Pair[Elem] = new Pair[Elem](new Elem(), new Elem());
                        p.a = new Elem();
                        ();
                    }
                }
            })
}
