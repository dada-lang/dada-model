//! # Liveness and cancellation
//!
//! When variables are dead, subtyping allows for *cancellation*, so e.g. if `d1` is dead,
//! then `ref[d1] mut[d2] Foo` is a subtype of `mut[d2] Foo`. Cancellation only
//! applies when we have a shared/leased permission applies to a leased permission.
//!
//! Consideration to test:
//!
//! * C1. Cancellation can remove "relative" permissions like `shared` and `leased`, but not owned permissions
//!   like `given` or `shared` nor generic permissions (since in that case we do not know which variables they
//!   may refer to)
//! * C2. Cancellation can only occur if all variables in the permission are dead: so `ref[d1, d2]` can only
//!   be canceled if `d1` and `d2` are both dead.
//! * C3. Cancellation cannot convert a shared permission into a leased permission.
//! * C4. Subtyping must account for future cancellation. So e.g., `mut[d1, d2] Foo` cannot be a subtype of
//!   `mut[d1] mut[d2] Foo` since, if `d1` later goes dead, the supertype could be upcast
//!   to `mut[d2] Foo` but the subtype could not. That would be unsound.

use formality_core::test;

// C1. Cancellation can remove "relative" permissions like `shared` and `leased`.

#[test]
fn c1_remove_relative_shared() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: ref[m] Data = m.ref;
                let q: ref[p] ref[m] Data = p.ref;
                let r: ref[m] Data = q.give;
            }
        }
        });
}

#[test]
fn c1_remove_relative_leased() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: mut[m] Data = m.mut;
                let q: mut[p] Data = p.mut;
                let r: mut[m] Data = q.give;
            }
        }
        });
}

// C1. Cancellation and `given` permission are not very relevant.
//
// The `given given` type here is equivalent to `given` so this just becomes
// ownership transfer.

#[test]
fn c1_remove_given() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: given given Data = m.give;
                let q: given Data = p.give;
            }
        }
        });
}

// C1. Cancellation cannot remove owned permissions `shared`.

#[test]
fn c1_remove_our() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: shared given Data = m.give;
                let q: given Data = p.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self) -> () { let m : given Data = new Data () ; let p : shared given Data = m . give ; let q : given Data = p . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let m : given Data = new Data () ; let p : shared given Data = m . give ; let q : given Data = p . give ; }, output: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let m : given Data = new Data () ; let p : shared given Data = m . give ; let q : given Data = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let m : given Data = new Data () ; let p : shared given Data = m . give ; let q : given Data = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let m : given Data = new Data () ; let p : shared given Data = m . give ; let q : given Data = p . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let m : given Data = new Data () ; let p : shared given Data = m . give ; let q : given Data = p . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements { statements: [let m : given Data = new Data () ;, let p : shared given Data = m . give ;, let q : given Data = p . give ;], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "type_statements" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let m : given Data = new Data () ;, let p : shared given Data = m . give ;, let q : given Data = p . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let p : shared given Data = m . give ;, let q : given Data = p . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statement { statement: let p : shared given Data = m . give ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "let" at (statements.rs) failed because
                                                      judgment `type_expr_as { expr: m . give, as_ty: shared given Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "type_expr_as" at (expressions.rs) failed because
                                                          judgment `sub { a: given Data, b: shared given Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "sub-classes" at (subtypes.rs) failed because
                                                              judgment `sub_perms { perm_a: given, perm_b: shared given, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                                  judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Shared] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                                                      judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Shared] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "(given) vs (given)" at (redperms.rs) failed because
                                                                          judgment `prove_is_given { a: shared, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "prove" at (predicates.rs) failed because
                                                                              judgment `prove_is_move { a: shared, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "is-moved" at (predicates.rs) failed because
                                                                                  judgment `prove_predicate { predicate: move(shared), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "mut => move" at (predicates.rs) failed because
                                                                                      judgment `prove_is_mut { a: shared, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "is-mut" at (predicates.rs) failed because
                                                                                          judgment `prove_predicate { predicate: mut(shared), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                                              pattern `true` did not match value `false`
                                                                                    the rule "parameter" at (predicates.rs) failed because
                                                                                      pattern `true` did not match value `false`"#]]);
}

// C1. Cancellation cannot remove generic permissions `shared`.

#[test]
fn c1_remove_generic_permissions() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self, p: P given Data) {
                let q: given Data = p.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self p : ^perm0_0 given Data) -> () { let q : given Data = p . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let q : given Data = p . give ; }, output: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, p: !perm_0 given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let q : given Data = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, p: !perm_0 given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let q : given Data = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, p: !perm_0 given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let q : given Data = p . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, p: !perm_0 given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let q : given Data = p . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, p: !perm_0 given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements { statements: [let q : given Data = p . give ;], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, p: !perm_0 given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "type_statements" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let q : given Data = p . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, p: !perm_0 given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statement { statement: let q : given Data = p . give ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, p: !perm_0 given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "let" at (statements.rs) failed because
                                                  judgment `type_expr_as { expr: p . give, as_ty: given Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, p: !perm_0 given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "type_expr_as" at (expressions.rs) failed because
                                                      judgment `sub { a: !perm_0 given Data, b: given Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, p: !perm_0 given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "sub-classes" at (subtypes.rs) failed because
                                                          judgment `sub_perms { perm_a: !perm_0 given, perm_b: given, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, p: !perm_0 given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                                              judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Var(!perm_0)] }, red_perm_b: RedPerm { chains: {RedChain { links: [] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, p: !perm_0 given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                                  judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Var(!perm_0)] }, red_chain_b: RedChain { links: [] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, p: !perm_0 given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "(shared) vs (copy)" at (redperms.rs) failed because
                                                                      judgment `prove_is_copy_owned { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, p: !perm_0 given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "prove" at (predicates.rs) failed because
                                                                          judgment `prove_is_copy { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, p: !perm_0 given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "is" at (predicates.rs) failed because
                                                                              judgment `prove_predicate { predicate: copy(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, p: !perm_0 given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "parameter" at (predicates.rs) failed because
                                                                                  pattern `true` did not match value `false`"#]]);
}

// C2. Cancellation can only occur if all variables in the permission are dead.

#[test]
fn c2_shared_shared_one_of_one_variables_dead() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: ref[m] Data = m.ref;
                let q: ref[p] ref[m] Data = p.ref;
                let r: ref[m] Data = q.give;
            }
        }
        });
}

#[test]
fn c2_shared_shared_two_of_two_variables_dead() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: ref[m] Data = m.ref;
                let q: ref[m] Data = m.ref;
                let r: ref[p, q] ref[m] Data = p.ref;
                let s: ref[m] Data = r.give;
            }
        }
        });
}

#[test]
fn c2_shared_shared_one_of_two_variables_dead() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: ref[m] Data = m.ref;
                let q: ref[m] Data = m.ref;
                let r: ref[p, q] ref[m] Data = p.ref;
                let s: ref[m] Data = r.give;
                q.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self) -> () { let m : given Data = new Data () ; let p : ref [m] Data = m . ref ; let q : ref [m] Data = m . ref ; let r : ref [p, q] ref [m] Data = p . ref ; let s : ref [m] Data = r . give ; q . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let m : given Data = new Data () ; let p : ref [m] Data = m . ref ; let q : ref [m] Data = m . ref ; let r : ref [p, q] ref [m] Data = p . ref ; let s : ref [m] Data = r . give ; q . give ; }, output: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let m : given Data = new Data () ; let p : ref [m] Data = m . ref ; let q : ref [m] Data = m . ref ; let r : ref [p, q] ref [m] Data = p . ref ; let s : ref [m] Data = r . give ; q . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let m : given Data = new Data () ; let p : ref [m] Data = m . ref ; let q : ref [m] Data = m . ref ; let r : ref [p, q] ref [m] Data = p . ref ; let s : ref [m] Data = r . give ; q . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment had no applicable rules: `sub { a: ref [m] Data, b: (), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: ref [m] Data, q: ref [m] Data, r: ref [@ fresh(0), p] ref [m] Data, s: ref [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }`"#]]);
}

#[test]
fn c2_leased_leased_one_of_one_variables_dead() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: mut[m] Data = m.mut;
                let q: mut[p] Data = p.mut;
                let r: mut[m] Data = q.give;
            }
        }
        });
}

#[test]
fn c2_leased_leased_two_of_two_variables_dead() {
    crate::assert_ok!({
        class Data {}
        class Pair {
            a: given Data;
            b: given Data;
        }
        class Main {
            fn test[perm P](given self) {
                let m: given Pair = new Pair(new Data(), new Data());
                let p: mut[m.a] Data = m.a.mut;
                let q: mut[m.b] Data = m.b.mut;
                let r: mut[p, q] Data = p.mut;
                let s: mut[m] Data = r.give;
            }
        }
        });
}

#[test]
fn c2_leased_leased_one_of_two_variables_dead() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: mut[m] Data = m.mut;
                let q: mut[m] Data = m.mut;
                let r: mut[p, q] mut[m] Data = p.mut;
                let s: mut[m] Data = r.give;
                q.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self) -> () { let m : given Data = new Data () ; let p : mut [m] Data = m . mut ; let q : mut [m] Data = m . mut ; let r : mut [p, q] mut [m] Data = p . mut ; let s : mut [m] Data = r . give ; q . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let m : given Data = new Data () ; let p : mut [m] Data = m . mut ; let q : mut [m] Data = m . mut ; let r : mut [p, q] mut [m] Data = p . mut ; let s : mut [m] Data = r . give ; q . give ; }, output: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let m : given Data = new Data () ; let p : mut [m] Data = m . mut ; let q : mut [m] Data = m . mut ; let r : mut [p, q] mut [m] Data = p . mut ; let s : mut [m] Data = r . give ; q . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let m : given Data = new Data () ; let p : mut [m] Data = m . mut ; let q : mut [m] Data = m . mut ; let r : mut [p, q] mut [m] Data = p . mut ; let s : mut [m] Data = r . give ; q . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let m : given Data = new Data () ; let p : mut [m] Data = m . mut ; let q : mut [m] Data = m . mut ; let r : mut [p, q] mut [m] Data = p . mut ; let s : mut [m] Data = r . give ; q . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let m : given Data = new Data () ; let p : mut [m] Data = m . mut ; let q : mut [m] Data = m . mut ; let r : mut [p, q] mut [m] Data = p . mut ; let s : mut [m] Data = r . give ; q . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements { statements: [let m : given Data = new Data () ;, let p : mut [m] Data = m . mut ;, let q : mut [m] Data = m . mut ;, let r : mut [p, q] mut [m] Data = p . mut ;, let s : mut [m] Data = r . give ;, q . give ;], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "type_statements" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let m : given Data = new Data () ;, let p : mut [m] Data = m . mut ;, let q : mut [m] Data = m . mut ;, let r : mut [p, q] mut [m] Data = p . mut ;, let s : mut [m] Data = r . give ;, q . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let p : mut [m] Data = m . mut ;, let q : mut [m] Data = m . mut ;, let r : mut [p, q] mut [m] Data = p . mut ;, let s : mut [m] Data = r . give ;, q . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statements_with_final_ty { statements: [let q : mut [m] Data = m . mut ;, let r : mut [p, q] mut [m] Data = p . mut ;, let s : mut [m] Data = r . give ;, q . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "cons" at (statements.rs) failed because
                                                      judgment `type_statement { statement: let q : mut [m] Data = m . mut ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {p, q}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "let" at (statements.rs) failed because
                                                          judgment `type_expr_as { expr: m . mut, as_ty: mut [m] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "type_expr_as" at (expressions.rs) failed because
                                                              judgment `type_expr { expr: m . mut, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                                the rule "ref|mut place" at (expressions.rs) failed because
                                                                  judgment `access_permitted { access: mut, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                                    the rule "access_permitted" at (accesses.rs) failed because
                                                                      judgment `env_permits_access { access: mut, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                                        the rule "env_permits_access" at (accesses.rs) failed because
                                                                          judgment `parameters_permit_access { parameters: [mut [m] Data], access: mut, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "cons" at (accesses.rs) failed because
                                                                              judgment `parameter_permits_access { parameter: mut [m] Data, access: mut, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "parameter" at (accesses.rs) failed because
                                                                                  judgment `lien_permit_access { lien: mt(m), access: mut, accessed_place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "mut'd" at (accesses.rs) failed because
                                                                                      judgment `mut_place_permits_access { leased_place: m, access: mut, accessed_place: m }` failed at the following rule(s):
                                                                                        the rule "lease-mutation" at (accesses.rs) failed because
                                                                                          condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                                                                                            &accessed_place = m
                                                                                            &leased_place = m"#]]);
}

// C3. Cancellation cannot convert a shared permission into a leased permission.

#[test]
fn c3_shared_leased_one_of_one_variables_dead() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: mut[m] Data = m.mut;
                let q: ref[p] mut[m] Data = p.ref;
                let r: mut[m] Data = q.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self) -> () { let m : given Data = new Data () ; let p : mut [m] Data = m . mut ; let q : ref [p] mut [m] Data = p . ref ; let r : mut [m] Data = q . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let m : given Data = new Data () ; let p : mut [m] Data = m . mut ; let q : ref [p] mut [m] Data = p . ref ; let r : mut [m] Data = q . give ; }, output: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let m : given Data = new Data () ; let p : mut [m] Data = m . mut ; let q : ref [p] mut [m] Data = p . ref ; let r : mut [m] Data = q . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let m : given Data = new Data () ; let p : mut [m] Data = m . mut ; let q : ref [p] mut [m] Data = p . ref ; let r : mut [m] Data = q . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let m : given Data = new Data () ; let p : mut [m] Data = m . mut ; let q : ref [p] mut [m] Data = p . ref ; let r : mut [m] Data = q . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let m : given Data = new Data () ; let p : mut [m] Data = m . mut ; let q : ref [p] mut [m] Data = p . ref ; let r : mut [m] Data = q . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements { statements: [let m : given Data = new Data () ;, let p : mut [m] Data = m . mut ;, let q : ref [p] mut [m] Data = p . ref ;, let r : mut [m] Data = q . give ;], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "type_statements" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let m : given Data = new Data () ;, let p : mut [m] Data = m . mut ;, let q : ref [p] mut [m] Data = p . ref ;, let r : mut [m] Data = q . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let p : mut [m] Data = m . mut ;, let q : ref [p] mut [m] Data = p . ref ;, let r : mut [m] Data = q . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statements_with_final_ty { statements: [let q : ref [p] mut [m] Data = p . ref ;, let r : mut [m] Data = q . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "cons" at (statements.rs) failed because
                                                      judgment `type_statements_with_final_ty { statements: [let r : mut [m] Data = q . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data, q: ref [p] mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "cons" at (statements.rs) failed because
                                                          judgment `type_statement { statement: let r : mut [m] Data = q . give ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data, q: ref [p] mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "let" at (statements.rs) failed because
                                                              judgment `type_expr_as { expr: q . give, as_ty: mut [m] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data, q: ref [p] mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                the rule "type_expr_as" at (expressions.rs) failed because
                                                                  judgment `sub { a: ref [p] mut [m] Data, b: mut [m] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data, q: ref [p] mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "sub-classes" at (subtypes.rs) failed because
                                                                      judgment `sub_perms { perm_a: ref [p] mut [m], perm_b: mut [m], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data, q: ref [p] mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                                                          judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Rfd(p), Mtd(m)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Mtd(m)] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data, q: ref [p] mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                                                              judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Rfd(p), Mtd(m)] }, red_chain_b: RedChain { links: [Mtd(m)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data, q: ref [p] mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "(ref-dead::P) vs Q ~~> (shared::P) vs Q" at (redperms.rs) failed because
                                                                                  judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Shared, Mtd(m)] }, red_chain_b: RedChain { links: [Mtd(m)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data, q: ref [p] mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                                                                      judgment `prove_is_copy { a: mut [m], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data, q: ref [p] mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "is" at (predicates.rs) failed because
                                                                                          judgment `prove_predicate { predicate: copy(mut [m]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data, q: ref [p] mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                                              pattern `true` did not match value `false`
                                                                                the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                                                                  judgment `prove_is_copy_owned { a: ref [p], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data, q: ref [p] mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "prove" at (predicates.rs) failed because
                                                                                      judgment `prove_is_owned { a: ref [p], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data, q: ref [p] mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "is-owned" at (predicates.rs) failed because
                                                                                          judgment `prove_predicate { predicate: owned(ref [p]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: mut [m] Data, q: ref [p] mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                                              pattern `true` did not match value `false`"#]]);
}

#[test]
fn c3_shared_leased_two_of_two_variables_dead() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: mut[m] Data = m.ref;
                let q: mut[m] Data = m.ref;
                let r: ref[p, q] mut[m] Data = p.ref;
                let s: ref[m] Data = r.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self) -> () { let m : given Data = new Data () ; let p : mut [m] Data = m . ref ; let q : mut [m] Data = m . ref ; let r : ref [p, q] mut [m] Data = p . ref ; let s : ref [m] Data = r . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let m : given Data = new Data () ; let p : mut [m] Data = m . ref ; let q : mut [m] Data = m . ref ; let r : ref [p, q] mut [m] Data = p . ref ; let s : ref [m] Data = r . give ; }, output: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let m : given Data = new Data () ; let p : mut [m] Data = m . ref ; let q : mut [m] Data = m . ref ; let r : ref [p, q] mut [m] Data = p . ref ; let s : ref [m] Data = r . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let m : given Data = new Data () ; let p : mut [m] Data = m . ref ; let q : mut [m] Data = m . ref ; let r : ref [p, q] mut [m] Data = p . ref ; let s : ref [m] Data = r . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let m : given Data = new Data () ; let p : mut [m] Data = m . ref ; let q : mut [m] Data = m . ref ; let r : ref [p, q] mut [m] Data = p . ref ; let s : ref [m] Data = r . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let m : given Data = new Data () ; let p : mut [m] Data = m . ref ; let q : mut [m] Data = m . ref ; let r : ref [p, q] mut [m] Data = p . ref ; let s : ref [m] Data = r . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements { statements: [let m : given Data = new Data () ;, let p : mut [m] Data = m . ref ;, let q : mut [m] Data = m . ref ;, let r : ref [p, q] mut [m] Data = p . ref ;, let s : ref [m] Data = r . give ;], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "type_statements" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let m : given Data = new Data () ;, let p : mut [m] Data = m . ref ;, let q : mut [m] Data = m . ref ;, let r : ref [p, q] mut [m] Data = p . ref ;, let s : ref [m] Data = r . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let p : mut [m] Data = m . ref ;, let q : mut [m] Data = m . ref ;, let r : ref [p, q] mut [m] Data = p . ref ;, let s : ref [m] Data = r . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statement { statement: let p : mut [m] Data = m . ref ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m, p}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "let" at (statements.rs) failed because
                                                      judgment `type_expr_as { expr: m . ref, as_ty: mut [m] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "type_expr_as" at (expressions.rs) failed because
                                                          judgment `sub { a: ref [m] Data, b: mut [m] Data, live_after: LivePlaces { accessed: {m}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "sub-classes" at (subtypes.rs) failed because
                                                              judgment `sub_perms { perm_a: ref [m], perm_b: mut [m], live_after: LivePlaces { accessed: {m}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                                  judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Rfl(m)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Mtl(m)] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                                                      judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Rfl(m)] }, red_chain_b: RedChain { links: [Mtl(m)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                                                          judgment `prove_is_copy_owned { a: ref [m], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "prove" at (predicates.rs) failed because
                                                                              judgment `prove_is_owned { a: ref [m], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "is-owned" at (predicates.rs) failed because
                                                                                  judgment `prove_predicate { predicate: owned(ref [m]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "parameter" at (predicates.rs) failed because
                                                                                      pattern `true` did not match value `false`"#]]);
}

#[test]
fn c3_shared_leased_one_of_two_variables_dead() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: ref[m] Data = m.ref;
                let q: ref[m] Data = m.ref;
                let r: ref[p, q] ref[m] Data = p.ref;
                let s: ref[m] Data = r.give;
                q.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self) -> () { let m : given Data = new Data () ; let p : ref [m] Data = m . ref ; let q : ref [m] Data = m . ref ; let r : ref [p, q] ref [m] Data = p . ref ; let s : ref [m] Data = r . give ; q . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let m : given Data = new Data () ; let p : ref [m] Data = m . ref ; let q : ref [m] Data = m . ref ; let r : ref [p, q] ref [m] Data = p . ref ; let s : ref [m] Data = r . give ; q . give ; }, output: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let m : given Data = new Data () ; let p : ref [m] Data = m . ref ; let q : ref [m] Data = m . ref ; let r : ref [p, q] ref [m] Data = p . ref ; let s : ref [m] Data = r . give ; q . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let m : given Data = new Data () ; let p : ref [m] Data = m . ref ; let q : ref [m] Data = m . ref ; let r : ref [p, q] ref [m] Data = p . ref ; let s : ref [m] Data = r . give ; q . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment had no applicable rules: `sub { a: ref [m] Data, b: (), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data, p: ref [m] Data, q: ref [m] Data, r: ref [@ fresh(0), p] ref [m] Data, s: ref [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }`"#]]);
}

// C4. Subtyping must account for future cancellation.

#[test]
fn c4_shared_d1d2d3_not_subtype_of_shared_d1_shared_d2d3() {
    // This is interesting. It fails because `ref[d1] ref[d2, d3]`
    // is equivalent to `ref[d2, d3]` and there is clearly no subtyping relation.
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let d1: given Data = new Data();
                let d2: given Data = new Data();
                let d3: given Data = new Data();
                let s1: ref[d1, d2, d3] Data = d1.ref;
                let s2: ref[d1] ref[d2, d3] Data = s1.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self) -> () { let d1 : given Data = new Data () ; let d2 : given Data = new Data () ; let d3 : given Data = new Data () ; let s1 : ref [d1, d2, d3] Data = d1 . ref ; let s2 : ref [d1] ref [d2, d3] Data = s1 . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let d1 : given Data = new Data () ; let d2 : given Data = new Data () ; let d3 : given Data = new Data () ; let s1 : ref [d1, d2, d3] Data = d1 . ref ; let s2 : ref [d1] ref [d2, d3] Data = s1 . give ; }, output: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let d1 : given Data = new Data () ; let d2 : given Data = new Data () ; let d3 : given Data = new Data () ; let s1 : ref [d1, d2, d3] Data = d1 . ref ; let s2 : ref [d1] ref [d2, d3] Data = s1 . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let d1 : given Data = new Data () ; let d2 : given Data = new Data () ; let d3 : given Data = new Data () ; let s1 : ref [d1, d2, d3] Data = d1 . ref ; let s2 : ref [d1] ref [d2, d3] Data = s1 . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let d1 : given Data = new Data () ; let d2 : given Data = new Data () ; let d3 : given Data = new Data () ; let s1 : ref [d1, d2, d3] Data = d1 . ref ; let s2 : ref [d1] ref [d2, d3] Data = s1 . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let d1 : given Data = new Data () ; let d2 : given Data = new Data () ; let d3 : given Data = new Data () ; let s1 : ref [d1, d2, d3] Data = d1 . ref ; let s2 : ref [d1] ref [d2, d3] Data = s1 . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements { statements: [let d1 : given Data = new Data () ;, let d2 : given Data = new Data () ;, let d3 : given Data = new Data () ;, let s1 : ref [d1, d2, d3] Data = d1 . ref ;, let s2 : ref [d1] ref [d2, d3] Data = s1 . give ;], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "type_statements" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let d1 : given Data = new Data () ;, let d2 : given Data = new Data () ;, let d3 : given Data = new Data () ;, let s1 : ref [d1, d2, d3] Data = d1 . ref ;, let s2 : ref [d1] ref [d2, d3] Data = s1 . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let d2 : given Data = new Data () ;, let d3 : given Data = new Data () ;, let s1 : ref [d1, d2, d3] Data = d1 . ref ;, let s2 : ref [d1] ref [d2, d3] Data = s1 . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statements_with_final_ty { statements: [let d3 : given Data = new Data () ;, let s1 : ref [d1, d2, d3] Data = d1 . ref ;, let s2 : ref [d1] ref [d2, d3] Data = s1 . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "cons" at (statements.rs) failed because
                                                      judgment `type_statements_with_final_ty { statements: [let s1 : ref [d1, d2, d3] Data = d1 . ref ;, let s2 : ref [d1] ref [d2, d3] Data = s1 . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "cons" at (statements.rs) failed because
                                                          judgment `type_statements_with_final_ty { statements: [let s2 : ref [d1] ref [d2, d3] Data = s1 . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "cons" at (statements.rs) failed because
                                                              judgment `type_statement { statement: let s2 : ref [d1] ref [d2, d3] Data = s1 . give ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                the rule "let" at (statements.rs) failed because
                                                                  judgment `type_expr_as { expr: s1 . give, as_ty: ref [d1] ref [d2, d3] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                    the rule "type_expr_as" at (expressions.rs) failed because
                                                                      judgment `sub { a: ref [d1, d2, d3] Data, b: ref [d1] ref [d2, d3] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "sub-classes" at (subtypes.rs) failed because
                                                                          judgment `sub_perms { perm_a: ref [d1, d2, d3], perm_b: ref [d1] ref [d2, d3], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                                                              judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Rfd(d1)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Rfd(d2)] }, RedChain { links: [Rfd(d3)] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                                                  judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Rfd(d1)] }, red_chain_b: RedChain { links: [Rfd(d2)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "(ref-dead::P) vs Q ~~> (shared::P) vs Q" at (redperms.rs) failed because
                                                                                      judgment `prove_is_mut { a: given, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "is-mut" at (predicates.rs) failed because
                                                                                          judgment `prove_predicate { predicate: mut(given), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                                              pattern `true` did not match value `false`
                                                                                    the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
                                                                                      condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                                                                        place_b = d2
                                                                                        &place_a = d1
                                                                                    the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                                                                      judgment `prove_is_copy_owned { a: ref [d1], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "prove" at (predicates.rs) failed because
                                                                                          judgment `prove_is_owned { a: ref [d1], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "is-owned" at (predicates.rs) failed because
                                                                                              judgment `prove_predicate { predicate: owned(ref [d1]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                                the rule "parameter" at (predicates.rs) failed because
                                                                                                  pattern `true` did not match value `false`
                                                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                                                  judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Rfd(d1)] }, red_chain_b: RedChain { links: [Rfd(d3)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "(ref-dead::P) vs Q ~~> (shared::P) vs Q" at (redperms.rs) failed because
                                                                                      judgment `prove_is_mut { a: given, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "is-mut" at (predicates.rs) failed because
                                                                                          judgment `prove_predicate { predicate: mut(given), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                                              pattern `true` did not match value `false`
                                                                                    the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
                                                                                      condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                                                                        place_b = d3
                                                                                        &place_a = d1
                                                                                    the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                                                                      judgment `prove_is_copy_owned { a: ref [d1], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "prove" at (predicates.rs) failed because
                                                                                          judgment `prove_is_owned { a: ref [d1], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "is-owned" at (predicates.rs) failed because
                                                                                              judgment `prove_predicate { predicate: owned(ref [d1]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                                the rule "parameter" at (predicates.rs) failed because
                                                                                                  pattern `true` did not match value `false`"#]]);
}

#[test]
fn c4_leased_d1d2d3_subtype_of_leased_d1_leased_d2d3() {
    // This one fails because `mut[d1, d2, d3]` and `mut[d1] mut[d2, d3]` are
    // different; the latter would require that `d1` contained data leased from `d2` or `d3`.
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let d1: given Data = new Data();
                let d2: given Data = new Data();
                let d3: given Data = new Data();
                let s1: mut[d1, d2, d3] Data = d1.mut;
                let s2: mut[d1] mut[d2, d3] Data = s1.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self) -> () { let d1 : given Data = new Data () ; let d2 : given Data = new Data () ; let d3 : given Data = new Data () ; let s1 : mut [d1, d2, d3] Data = d1 . mut ; let s2 : mut [d1] mut [d2, d3] Data = s1 . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let d1 : given Data = new Data () ; let d2 : given Data = new Data () ; let d3 : given Data = new Data () ; let s1 : mut [d1, d2, d3] Data = d1 . mut ; let s2 : mut [d1] mut [d2, d3] Data = s1 . give ; }, output: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let d1 : given Data = new Data () ; let d2 : given Data = new Data () ; let d3 : given Data = new Data () ; let s1 : mut [d1, d2, d3] Data = d1 . mut ; let s2 : mut [d1] mut [d2, d3] Data = s1 . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let d1 : given Data = new Data () ; let d2 : given Data = new Data () ; let d3 : given Data = new Data () ; let s1 : mut [d1, d2, d3] Data = d1 . mut ; let s2 : mut [d1] mut [d2, d3] Data = s1 . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let d1 : given Data = new Data () ; let d2 : given Data = new Data () ; let d3 : given Data = new Data () ; let s1 : mut [d1, d2, d3] Data = d1 . mut ; let s2 : mut [d1] mut [d2, d3] Data = s1 . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let d1 : given Data = new Data () ; let d2 : given Data = new Data () ; let d3 : given Data = new Data () ; let s1 : mut [d1, d2, d3] Data = d1 . mut ; let s2 : mut [d1] mut [d2, d3] Data = s1 . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements { statements: [let d1 : given Data = new Data () ;, let d2 : given Data = new Data () ;, let d3 : given Data = new Data () ;, let s1 : mut [d1, d2, d3] Data = d1 . mut ;, let s2 : mut [d1] mut [d2, d3] Data = s1 . give ;], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "type_statements" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let d1 : given Data = new Data () ;, let d2 : given Data = new Data () ;, let d3 : given Data = new Data () ;, let s1 : mut [d1, d2, d3] Data = d1 . mut ;, let s2 : mut [d1] mut [d2, d3] Data = s1 . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let d2 : given Data = new Data () ;, let d3 : given Data = new Data () ;, let s1 : mut [d1, d2, d3] Data = d1 . mut ;, let s2 : mut [d1] mut [d2, d3] Data = s1 . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statements_with_final_ty { statements: [let d3 : given Data = new Data () ;, let s1 : mut [d1, d2, d3] Data = d1 . mut ;, let s2 : mut [d1] mut [d2, d3] Data = s1 . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "cons" at (statements.rs) failed because
                                                      judgment `type_statements_with_final_ty { statements: [let s1 : mut [d1, d2, d3] Data = d1 . mut ;, let s2 : mut [d1] mut [d2, d3] Data = s1 . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "cons" at (statements.rs) failed because
                                                          judgment `type_statements_with_final_ty { statements: [let s2 : mut [d1] mut [d2, d3] Data = s1 . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "cons" at (statements.rs) failed because
                                                              judgment `type_statement { statement: let s2 : mut [d1] mut [d2, d3] Data = s1 . give ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                the rule "let" at (statements.rs) failed because
                                                                  judgment `type_expr_as { expr: s1 . give, as_ty: mut [d1] mut [d2, d3] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                    the rule "type_expr_as" at (expressions.rs) failed because
                                                                      judgment `sub { a: mut [d1, d2, d3] Data, b: mut [d1] mut [d2, d3] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "sub-classes" at (subtypes.rs) failed because
                                                                          judgment `sub_perms { perm_a: mut [d1, d2, d3], perm_b: mut [d1] mut [d2, d3], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                                                              judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Mtd(d1)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Mtd(d1), Mtd(d2)] }, RedChain { links: [Mtd(d1), Mtd(d3)] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                                                  judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtd(d1)] }, red_chain_b: RedChain { links: [Mtd(d1), Mtd(d2)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "(mut-dead::P) vs Q ~~> (P) vs Q" at (redperms.rs) failed because
                                                                                      judgment `prove_is_mut { a: given, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "is-mut" at (predicates.rs) failed because
                                                                                          judgment `prove_predicate { predicate: mut(given), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                                              pattern `true` did not match value `false`
                                                                                    the rule "(mut::P) vs (mut::P)" at (redperms.rs) failed because
                                                                                      judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Mtd(d2)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "(given) vs (given)" at (redperms.rs) failed because
                                                                                          judgment `prove_is_given { a: mut [d2], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "prove" at (predicates.rs) failed because
                                                                                              judgment `prove_is_owned { a: mut [d2], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                                the rule "is-owned" at (predicates.rs) failed because
                                                                                                  judgment `prove_predicate { predicate: owned(mut [d2]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                                    the rule "parameter" at (predicates.rs) failed because
                                                                                                      pattern `true` did not match value `false`
                                                                                    the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                                                                      judgment `prove_is_copy_owned { a: mut [d1], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "prove" at (predicates.rs) failed because
                                                                                          judgment `prove_is_copy { a: mut [d1], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "is" at (predicates.rs) failed because
                                                                                              judgment `prove_predicate { predicate: copy(mut [d1]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                                the rule "parameter" at (predicates.rs) failed because
                                                                                                  pattern `true` did not match value `false`
                                                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                                                  judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtd(d1)] }, red_chain_b: RedChain { links: [Mtd(d1), Mtd(d3)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "(mut-dead::P) vs Q ~~> (P) vs Q" at (redperms.rs) failed because
                                                                                      judgment `prove_is_mut { a: given, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "is-mut" at (predicates.rs) failed because
                                                                                          judgment `prove_predicate { predicate: mut(given), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                                              pattern `true` did not match value `false`
                                                                                    the rule "(mut::P) vs (mut::P)" at (redperms.rs) failed because
                                                                                      judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Mtd(d3)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "(given) vs (given)" at (redperms.rs) failed because
                                                                                          judgment `prove_is_given { a: mut [d3], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "prove" at (predicates.rs) failed because
                                                                                              judgment `prove_is_owned { a: mut [d3], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                                the rule "is-owned" at (predicates.rs) failed because
                                                                                                  judgment `prove_predicate { predicate: owned(mut [d3]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                                    the rule "parameter" at (predicates.rs) failed because
                                                                                                      pattern `true` did not match value `false`
                                                                                    the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                                                                      judgment `prove_is_copy_owned { a: mut [d1], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "prove" at (predicates.rs) failed because
                                                                                          judgment `prove_is_copy { a: mut [d1], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "is" at (predicates.rs) failed because
                                                                                              judgment `prove_predicate { predicate: copy(mut [d1]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: given Data, d3: given Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                                the rule "parameter" at (predicates.rs) failed because
                                                                                                  pattern `true` did not match value `false`"#]]);
}

#[test]
fn c4_leased_d1d2_leased_pair_not_subtype_of_leased_d2() {
    // This one fails because you after cancelling `d1` you don't get `d2`.
    crate::assert_err!({
        class Pair {
            a: given Data;
            b: given Data;
        }
        class Data { }
        class Main {
            fn test[perm P](given self, pair: P Pair) where mut(P) {
                let d1: mut[pair.a] Data = pair.a.mut;
                let d2: mut[pair.b] Data = pair.b.mut;
                let s1: mut[d1, d2] Data = d1.mut;
                let s2: mut[d2] Data = s1.give;
                let _x = self.give.consume(pair.give, s2.give);
            }

            fn consume[perm P](given self, pair: P Pair, from_b: mut[pair.b] Data) where mut(P) { (); }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self pair : ^perm0_0 Pair) -> () where mut(^perm0_0) { let d1 : mut [pair . a] Data = pair . a . mut ; let d2 : mut [pair . b] Data = pair . b . mut ; let s1 : mut [d1, d2] Data = d1 . mut ; let s2 : mut [d2] Data = s1 . give ; let _x = self . give . consume (pair . give, s2 . give) ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let d1 : mut [pair . a] Data = pair . a . mut ; let d2 : mut [pair . b] Data = pair . b . mut ; let s1 : mut [d1, d2] Data = d1 . mut ; let s2 : mut [d2] Data = s1 . give ; let _x = self . give . consume (pair . give, s2 . give) ; }, output: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let d1 : mut [pair . a] Data = pair . a . mut ; let d2 : mut [pair . b] Data = pair . b . mut ; let s1 : mut [d1, d2] Data = d1 . mut ; let s2 : mut [d2] Data = s1 . give ; let _x = self . give . consume (pair . give, s2 . give) ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let d1 : mut [pair . a] Data = pair . a . mut ; let d2 : mut [pair . b] Data = pair . b . mut ; let s1 : mut [d1, d2] Data = d1 . mut ; let s2 : mut [d2] Data = s1 . give ; let _x = self . give . consume (pair . give, s2 . give) ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let d1 : mut [pair . a] Data = pair . a . mut ; let d2 : mut [pair . b] Data = pair . b . mut ; let s1 : mut [d1, d2] Data = d1 . mut ; let s2 : mut [d2] Data = s1 . give ; let _x = self . give . consume (pair . give, s2 . give) ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let d1 : mut [pair . a] Data = pair . a . mut ; let d2 : mut [pair . b] Data = pair . b . mut ; let s1 : mut [d1, d2] Data = d1 . mut ; let s2 : mut [d2] Data = s1 . give ; let _x = self . give . consume (pair . give, s2 . give) ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements { statements: [let d1 : mut [pair . a] Data = pair . a . mut ;, let d2 : mut [pair . b] Data = pair . b . mut ;, let s1 : mut [d1, d2] Data = d1 . mut ;, let s2 : mut [d2] Data = s1 . give ;, let _x = self . give . consume (pair . give, s2 . give) ;], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "type_statements" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let d1 : mut [pair . a] Data = pair . a . mut ;, let d2 : mut [pair . b] Data = pair . b . mut ;, let s1 : mut [d1, d2] Data = d1 . mut ;, let s2 : mut [d2] Data = s1 . give ;, let _x = self . give . consume (pair . give, s2 . give) ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let d2 : mut [pair . b] Data = pair . b . mut ;, let s1 : mut [d1, d2] Data = d1 . mut ;, let s2 : mut [d2] Data = s1 . give ;, let _x = self . give . consume (pair . give, s2 . give) ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: mut [pair . a] Data, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statements_with_final_ty { statements: [let s1 : mut [d1, d2] Data = d1 . mut ;, let s2 : mut [d2] Data = s1 . give ;, let _x = self . give . consume (pair . give, s2 . give) ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "cons" at (statements.rs) failed because
                                                      judgment `type_statements_with_final_ty { statements: [let s2 : mut [d2] Data = s1 . give ;, let _x = self . give . consume (pair . give, s2 . give) ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "cons" at (statements.rs) failed because
                                                          judgment `type_statement { statement: let s2 : mut [d2] Data = s1 . give ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {self, pair, s2}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "let" at (statements.rs) failed because
                                                              judgment `type_expr_as { expr: s1 . give, as_ty: mut [d2] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {self, pair}, traversed: {} } }` failed at the following rule(s):
                                                                the rule "type_expr_as" at (expressions.rs) failed because
                                                                  judgment `sub { a: mut [d1, d2] Data, b: mut [d2] Data, live_after: LivePlaces { accessed: {self, pair}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "sub-classes" at (subtypes.rs) failed because
                                                                      judgment `sub_perms { perm_a: mut [d1, d2], perm_b: mut [d2], live_after: LivePlaces { accessed: {self, pair}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                                                          judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Mtd(d1), Mtl(pair . a), Var(!perm_0)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Mtd(d2), Mtl(pair . b), Var(!perm_0)] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                                                              judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtd(d1), Mtl(pair . a), Var(!perm_0)] }, red_chain_b: RedChain { links: [Mtd(d2), Mtl(pair . b), Var(!perm_0)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "(mut-dead::P) vs Q ~~> (P) vs Q" at (redperms.rs) failed because
                                                                                  judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtl(pair . a), Var(!perm_0)] }, red_chain_b: RedChain { links: [Mtd(d2), Mtl(pair . b), Var(!perm_0)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "(mut::P) vs (mut::P)" at (redperms.rs) failed because
                                                                                      condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                                                                        place_b = d2
                                                                                        &place_a = pair . a
                                                                                    the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                                                                      judgment `prove_is_copy_owned { a: mut [pair . a], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "prove" at (predicates.rs) failed because
                                                                                          judgment `prove_is_copy { a: mut [pair . a], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "is" at (predicates.rs) failed because
                                                                                              judgment `prove_predicate { predicate: copy(mut [pair . a]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                                the rule "parameter" at (predicates.rs) failed because
                                                                                                  pattern `true` did not match value `false`
                                                                                the rule "(mut::P) vs (mut::P)" at (redperms.rs) failed because
                                                                                  condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                                                                    place_b = d2
                                                                                    &place_a = d1
                                                                                the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                                                                  judgment `prove_is_copy_owned { a: mut [d1], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "prove" at (predicates.rs) failed because
                                                                                      judgment `prove_is_copy { a: mut [d1], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "is" at (predicates.rs) failed because
                                                                                          judgment `prove_predicate { predicate: copy(mut [d1]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                                              pattern `true` did not match value `false`"#]]);
}
