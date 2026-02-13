//! # Subpermission
//!
//! All operations permitted by supertype must be permitted by the subtype.
//!
//! C1. This begins with edits on the data structure itself, so `shared Foo` cannot be a subtype of `given Foo`
//! since the latter permits field mutation.
//!
//! C2. This also includes restrictions on what can be done in the environment. So `ref[d1] Foo` cannot
//! be a subtype of `ref[d2] Foo` since the latter permits `d1` to be modified but the subtype does not.
//! (The latter also restricts edits to `d2`, but that's ok in the supertype, it can be more restrictive.)

use formality_core::test;

// C1. This begins with edits on the data structure itself, so `shared Foo` cannot be a subtype of `given Foo`
// since the latter permits field mutation.

#[test]
fn c1_given_subtype_of_our() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test(given self) {
                let m: given Data = new Data();
                let p: shared Data = m.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self) -> () { let m : given Data = new Data () ; let p : shared Data = m . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let m : given Data = new Data () ; let p : shared Data = m . give ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let m : given Data = new Data () ; let p : shared Data = m . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let m : given Data = new Data () ; let p : shared Data = m . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let m : given Data = new Data () ; let p : shared Data = m . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let m : given Data = new Data () ; let p : shared Data = m . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let m : given Data = new Data () ;, let p : shared Data = m . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let p : shared Data = m . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statement { statement: let p : shared Data = m . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "let" at (statements.rs) failed because
                                                  judgment `type_expr_as { expr: m . give, as_ty: shared Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "type_expr_as" at (expressions.rs) failed because
                                                      judgment `sub { a: given Data, b: shared Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "sub-classes" at (subtypes.rs) failed because
                                                          judgment `sub_perms { perm_a: given, perm_b: shared, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                                              judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Shared] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                                  judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Shared] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "(given) vs (given)" at (redperms.rs) failed because
                                                                      judgment `prove_is_given { a: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "prove" at (predicates.rs) failed because
                                                                          judgment `prove_is_move { a: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "is-moved" at (predicates.rs) failed because
                                                                              judgment `prove_predicate { predicate: move(shared), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "mut => move" at (predicates.rs) failed because
                                                                                  judgment `prove_is_mut { a: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "is-mut" at (predicates.rs) failed because
                                                                                      judgment `prove_predicate { predicate: mut(shared), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "parameter" at (predicates.rs) failed because
                                                                                          pattern `true` did not match value `false`
                                                                                the rule "parameter" at (predicates.rs) failed because
                                                                                  pattern `true` did not match value `false`"#]]);
}

#[test]
fn c1_our_not_subtype_of_given() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test(given self) {
                let m: shared Data = new Data();
                let p: given Data = m.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self) -> () { let m : shared Data = new Data () ; let p : given Data = m . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let m : shared Data = new Data () ; let p : given Data = m . give ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let m : shared Data = new Data () ; let p : given Data = m . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let m : shared Data = new Data () ; let p : given Data = m . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let m : shared Data = new Data () ; let p : given Data = m . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let m : shared Data = new Data () ; let p : given Data = m . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let m : shared Data = new Data () ;, let p : given Data = m . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statement { statement: let m : shared Data = new Data () ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                            the rule "let" at (statements.rs) failed because
                                              judgment `type_expr_as { expr: new Data (), as_ty: shared Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "type_expr_as" at (expressions.rs) failed because
                                                  judgment `sub { a: Data, b: shared Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "sub-classes" at (subtypes.rs) failed because
                                                      judgment `sub_perms { perm_a: given, perm_b: shared, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                                          judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Shared] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                                              judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Shared] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "(given) vs (given)" at (redperms.rs) failed because
                                                                  judgment `prove_is_given { a: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "prove" at (predicates.rs) failed because
                                                                      judgment `prove_is_move { a: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "is-moved" at (predicates.rs) failed because
                                                                          judgment `prove_predicate { predicate: move(shared), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "mut => move" at (predicates.rs) failed because
                                                                              judgment `prove_is_mut { a: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "is-mut" at (predicates.rs) failed because
                                                                                  judgment `prove_predicate { predicate: mut(shared), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "parameter" at (predicates.rs) failed because
                                                                                      pattern `true` did not match value `false`
                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                              pattern `true` did not match value `false`"#]]);
}

#[test]
fn c1_given_subtype_of_shared() {
    // In this test, the data is given from `n` and hence has type `given Data`.
    // But the type indicates it is shared from `m`.
    crate::assert_err!({
        class Data { }
        class Main {
            fn test(given self) {
                let m: given Data = new Data();
                let n: given Data = new Data();
                let p: ref[m] Data = n.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self) -> () { let m : given Data = new Data () ; let n : given Data = new Data () ; let p : ref [m] Data = n . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let m : given Data = new Data () ; let n : given Data = new Data () ; let p : ref [m] Data = n . give ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let m : given Data = new Data () ; let n : given Data = new Data () ; let p : ref [m] Data = n . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let m : given Data = new Data () ; let n : given Data = new Data () ; let p : ref [m] Data = n . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let m : given Data = new Data () ; let n : given Data = new Data () ; let p : ref [m] Data = n . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let m : given Data = new Data () ; let n : given Data = new Data () ; let p : ref [m] Data = n . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let m : given Data = new Data () ;, let n : given Data = new Data () ;, let p : ref [m] Data = n . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let n : given Data = new Data () ;, let p : ref [m] Data = n . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let p : ref [m] Data = n . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statement { statement: let p : ref [m] Data = n . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "let" at (statements.rs) failed because
                                                      judgment `type_expr_as { expr: n . give, as_ty: ref [m] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "type_expr_as" at (expressions.rs) failed because
                                                          judgment `sub { a: given Data, b: ref [m] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "sub-classes" at (subtypes.rs) failed because
                                                              judgment `sub_perms { perm_a: given, perm_b: ref [m], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                                  judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Rfd(m)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                                                      judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Rfd(m)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "(given) vs (given)" at (redperms.rs) failed because
                                                                          judgment `prove_is_given { a: ref [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "prove" at (predicates.rs) failed because
                                                                              judgment `prove_is_move { a: ref [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "is-moved" at (predicates.rs) failed because
                                                                                  judgment `prove_predicate { predicate: move(ref [m]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "mut => move" at (predicates.rs) failed because
                                                                                      judgment `prove_is_mut { a: ref [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "is-mut" at (predicates.rs) failed because
                                                                                          judgment `prove_predicate { predicate: mut(ref [m]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                                              pattern `true` did not match value `false`
                                                                                    the rule "parameter" at (predicates.rs) failed because
                                                                                      pattern `true` did not match value `false`"#]]);
}

#[test]
fn c1_our_subtype_of_shared() {
    // In this test, the data is given from `n` and hence has type `shared Data`.
    // But the type indicates it is shared from `m`.
    // This is less accurate than the ideal but allowed by subtyping.
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test(given self) {
                let m: given Data = new Data();
                let n: shared Data = m.share;
                let p: ref[m] Data = n.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn c1_given_not_subtype_of_P() {
    // given is not a subtype of generic permission `P` because it may be leased
    // (which would violate compatible layout rules).
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: P Data = n.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self) -> () { let m : given Data = new Data () ; let p : ^perm0_0 Data = n . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let m : given Data = new Data () ; let p : !perm_0 Data = n . give ; }, output: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let m : given Data = new Data () ; let p : !perm_0 Data = n . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let m : given Data = new Data () ; let p : !perm_0 Data = n . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let m : given Data = new Data () ; let p : !perm_0 Data = n . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let m : given Data = new Data () ; let p : !perm_0 Data = n . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let m : given Data = new Data () ;, let p : !perm_0 Data = n . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let p : !perm_0 Data = n . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statement { statement: let p : !perm_0 Data = n . give ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "let" at (statements.rs) failed because
                                                  judgment `type_expr_as { expr: n . give, as_ty: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "type_expr_as" at (expressions.rs) failed because
                                                      judgment `type_expr { expr: n . give, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "give place" at (expressions.rs) failed because
                                                          no variable named `n`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn c1_given_subtype_of_P_where_P_shared() {
    // given IS a subtype of generic permission `P`
    // because it is declared as `shared` and hence is layout compatible.
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) where copy(P) {
                let m: given Data = new Data();
                let p: P Data = m.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self) -> () where copy(^perm0_0) { let m : given Data = new Data () ; let p : ^perm0_0 Data = m . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let m : given Data = new Data () ; let p : !perm_0 Data = m . give ; }, output: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let m : given Data = new Data () ; let p : !perm_0 Data = m . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let m : given Data = new Data () ; let p : !perm_0 Data = m . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let m : given Data = new Data () ; let p : !perm_0 Data = m . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let m : given Data = new Data () ; let p : !perm_0 Data = m . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let m : given Data = new Data () ;, let p : !perm_0 Data = m . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let p : !perm_0 Data = m . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statement { statement: let p : !perm_0 Data = m . give ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "let" at (statements.rs) failed because
                                                  judgment `type_expr_as { expr: m . give, as_ty: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "type_expr_as" at (expressions.rs) failed because
                                                      judgment `sub { a: given Data, b: !perm_0 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "sub-classes" at (subtypes.rs) failed because
                                                          judgment `sub_perms { perm_a: given, perm_b: !perm_0, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                                              judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Var(!perm_0)] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                                  judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Var(!perm_0)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "(given) vs (given)" at (redperms.rs) failed because
                                                                      judgment `prove_is_given { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "prove" at (predicates.rs) failed because
                                                                          judgment `prove_is_move { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "is-moved" at (predicates.rs) failed because
                                                                              judgment `prove_predicate { predicate: move(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "mut => move" at (predicates.rs) failed because
                                                                                  judgment `prove_is_mut { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "is-mut" at (predicates.rs) failed because
                                                                                      judgment `prove_predicate { predicate: mut(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, m: given Data}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "parameter" at (predicates.rs) failed because
                                                                                          pattern `true` did not match value `false`
                                                                                the rule "parameter" at (predicates.rs) failed because
                                                                                  pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn c1_newData_assignable_to_P_where_P_shared() {
    // given IS a subtype of generic permission `P`
    // because it is declared as `shared` and hence is layout compatible.
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) where copy(P) {
                let m: P Data = new Data();
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self) -> () where copy(^perm0_0) { let m : ^perm0_0 Data = new Data () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let m : !perm_0 Data = new Data () ; }, output: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let m : !perm_0 Data = new Data () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let m : !perm_0 Data = new Data () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let m : !perm_0 Data = new Data () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let m : !perm_0 Data = new Data () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let m : !perm_0 Data = new Data () ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statement { statement: let m : !perm_0 Data = new Data () ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "let" at (statements.rs) failed because
                                              judgment `type_expr_as { expr: new Data (), as_ty: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "type_expr_as" at (expressions.rs) failed because
                                                  judgment `sub { a: Data, b: !perm_0 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "sub-classes" at (subtypes.rs) failed because
                                                      judgment `sub_perms { perm_a: given, perm_b: !perm_0, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                                          judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Var(!perm_0)] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                                              judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Var(!perm_0)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "(given) vs (given)" at (redperms.rs) failed because
                                                                  judgment `prove_is_given { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "prove" at (predicates.rs) failed because
                                                                      judgment `prove_is_move { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "is-moved" at (predicates.rs) failed because
                                                                          judgment `prove_predicate { predicate: move(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "mut => move" at (predicates.rs) failed because
                                                                              judgment `prove_is_mut { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "is-mut" at (predicates.rs) failed because
                                                                                  judgment `prove_predicate { predicate: mut(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "parameter" at (predicates.rs) failed because
                                                                                      pattern `true` did not match value `false`
                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn c1_our_not_subtype_of_P_where_P_copy() {
    // `shared` is a subtype of generic permission `P`
    // when it is declared as `copy`.
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self) where copy(P) {
                let m: given Data = new Data();
                let o: shared Data = m.share;
                let p: P Data = o.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn c1_P_not_subtype_of_given_where_P_shared() {
    // P is *not* a subtype of `given`, even though it is declared as `shared`.
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) where copy(P) {
                let m: P Data = new Data();
                let p: given Data = n.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self) -> () where copy(^perm0_0) { let m : ^perm0_0 Data = new Data () ; let p : given Data = n . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let m : !perm_0 Data = new Data () ; let p : given Data = n . give ; }, output: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let m : !perm_0 Data = new Data () ; let p : given Data = n . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let m : !perm_0 Data = new Data () ; let p : given Data = n . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let m : !perm_0 Data = new Data () ; let p : given Data = n . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let m : !perm_0 Data = new Data () ; let p : given Data = n . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let m : !perm_0 Data = new Data () ;, let p : given Data = n . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statement { statement: let m : !perm_0 Data = new Data () ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {n}, traversed: {} } }` failed at the following rule(s):
                                            the rule "let" at (statements.rs) failed because
                                              judgment `type_expr_as { expr: new Data (), as_ty: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {n}, traversed: {} } }` failed at the following rule(s):
                                                the rule "type_expr_as" at (expressions.rs) failed because
                                                  judgment `sub { a: Data, b: !perm_0 Data, live_after: LivePlaces { accessed: {n}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "sub-classes" at (subtypes.rs) failed because
                                                      judgment `sub_perms { perm_a: given, perm_b: !perm_0, live_after: LivePlaces { accessed: {n}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                                          judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Var(!perm_0)] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                                              judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Var(!perm_0)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "(given) vs (given)" at (redperms.rs) failed because
                                                                  judgment `prove_is_given { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "prove" at (predicates.rs) failed because
                                                                      judgment `prove_is_move { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "is-moved" at (predicates.rs) failed because
                                                                          judgment `prove_predicate { predicate: move(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "mut => move" at (predicates.rs) failed because
                                                                              judgment `prove_is_mut { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "is-mut" at (predicates.rs) failed because
                                                                                  judgment `prove_predicate { predicate: mut(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "parameter" at (predicates.rs) failed because
                                                                                      pattern `true` did not match value `false`
                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn c1_P_not_subtype_of_our_where_P_shared() {
    // P is *not* a subtype of `shared`, even though it is declared as shared.
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) where copy(P) {
                let m: P Data = new Data();
                let p: shared Data = n.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self) -> () where copy(^perm0_0) { let m : ^perm0_0 Data = new Data () ; let p : shared Data = n . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let m : !perm_0 Data = new Data () ; let p : shared Data = n . give ; }, output: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let m : !perm_0 Data = new Data () ; let p : shared Data = n . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let m : !perm_0 Data = new Data () ; let p : shared Data = n . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let m : !perm_0 Data = new Data () ; let p : shared Data = n . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let m : !perm_0 Data = new Data () ; let p : shared Data = n . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let m : !perm_0 Data = new Data () ;, let p : shared Data = n . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statement { statement: let m : !perm_0 Data = new Data () ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {n}, traversed: {} } }` failed at the following rule(s):
                                            the rule "let" at (statements.rs) failed because
                                              judgment `type_expr_as { expr: new Data (), as_ty: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {n}, traversed: {} } }` failed at the following rule(s):
                                                the rule "type_expr_as" at (expressions.rs) failed because
                                                  judgment `sub { a: Data, b: !perm_0 Data, live_after: LivePlaces { accessed: {n}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "sub-classes" at (subtypes.rs) failed because
                                                      judgment `sub_perms { perm_a: given, perm_b: !perm_0, live_after: LivePlaces { accessed: {n}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                                          judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Var(!perm_0)] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                                              judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Var(!perm_0)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "(given) vs (given)" at (redperms.rs) failed because
                                                                  judgment `prove_is_given { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "prove" at (predicates.rs) failed because
                                                                      judgment `prove_is_move { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "is-moved" at (predicates.rs) failed because
                                                                          judgment `prove_predicate { predicate: move(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "mut => move" at (predicates.rs) failed because
                                                                              judgment `prove_is_mut { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "is-mut" at (predicates.rs) failed because
                                                                                  judgment `prove_predicate { predicate: mut(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "parameter" at (predicates.rs) failed because
                                                                                      pattern `true` did not match value `false`
                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn c1_P_not_subtype_of_Q_where_PQ_shared() {
    // P is *not* a subtype of `shared`, even though it is declared as shared.
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P, perm Q](given self) where copy(P), copy(Q) {
                let m: P Data = new Data();
                let p: Q Data = m.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm, perm] (given self) -> () where copy(^perm0_0), copy(^perm0_1) { let m : ^perm0_0 Data = new Data () ; let p : ^perm0_1 Data = m . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let m : !perm_0 Data = new Data () ; let p : !perm_1 Data = m . give ; }, output: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main}, assumptions: {copy(!perm_0), copy(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let m : !perm_0 Data = new Data () ; let p : !perm_1 Data = m . give ; }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main}, assumptions: {copy(!perm_0), copy(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let m : !perm_0 Data = new Data () ; let p : !perm_1 Data = m . give ; }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main}, assumptions: {copy(!perm_0), copy(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let m : !perm_0 Data = new Data () ; let p : !perm_1 Data = m . give ; }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main}, assumptions: {copy(!perm_0), copy(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let m : !perm_0 Data = new Data () ; let p : !perm_1 Data = m . give ; }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main}, assumptions: {copy(!perm_0), copy(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let m : !perm_0 Data = new Data () ;, let p : !perm_1 Data = m . give ;], ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main}, assumptions: {copy(!perm_0), copy(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statement { statement: let m : !perm_0 Data = new Data () ;, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main}, assumptions: {copy(!perm_0), copy(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                            the rule "let" at (statements.rs) failed because
                                              judgment `type_expr_as { expr: new Data (), as_ty: !perm_0 Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main}, assumptions: {copy(!perm_0), copy(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "type_expr_as" at (expressions.rs) failed because
                                                  judgment `sub { a: Data, b: !perm_0 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main}, assumptions: {copy(!perm_0), copy(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "sub-classes" at (subtypes.rs) failed because
                                                      judgment `sub_perms { perm_a: given, perm_b: !perm_0, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main}, assumptions: {copy(!perm_0), copy(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                                          judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Var(!perm_0)] }} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main}, assumptions: {copy(!perm_0), copy(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                                              judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Var(!perm_0)] }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main}, assumptions: {copy(!perm_0), copy(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "(given) vs (given)" at (redperms.rs) failed because
                                                                  judgment `prove_is_given { a: !perm_0, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main}, assumptions: {copy(!perm_0), copy(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "prove" at (predicates.rs) failed because
                                                                      judgment `prove_is_move { a: !perm_0, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main}, assumptions: {copy(!perm_0), copy(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "is-moved" at (predicates.rs) failed because
                                                                          judgment `prove_predicate { predicate: move(!perm_0), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main}, assumptions: {copy(!perm_0), copy(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "mut => move" at (predicates.rs) failed because
                                                                              judgment `prove_is_mut { a: !perm_0, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main}, assumptions: {copy(!perm_0), copy(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "is-mut" at (predicates.rs) failed because
                                                                                  judgment `prove_predicate { predicate: mut(!perm_0), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main}, assumptions: {copy(!perm_0), copy(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "parameter" at (predicates.rs) failed because
                                                                                      pattern `true` did not match value `false`
                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn c1_newData_assignable_to_shared() {
    // Variation of [`c1_given_subtype_of_shared`][] in which
    // `new Data()` is assigned to a `ref[m] Data` variable.
    crate::assert_err!({
        class Data { }
        class Main {
            fn test(given self) {
                let p: ref[m] Data = new Data();
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self) -> () { let p : ref [m] Data = new Data () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let p : ref [m] Data = new Data () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let p : ref [m] Data = new Data () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let p : ref [m] Data = new Data () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let p : ref [m] Data = new Data () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let p : ref [m] Data = new Data () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let p : ref [m] Data = new Data () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statement { statement: let p : ref [m] Data = new Data () ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "let" at (statements.rs) failed because
                                              judgment `type_expr_as { expr: new Data (), as_ty: ref [m] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "type_expr_as" at (expressions.rs) failed because
                                                  judgment `sub { a: Data, b: ref [m] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "sub-classes" at (subtypes.rs) failed because
                                                      judgment `sub_perms { perm_a: given, perm_b: ref [m], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                                          judgment `red_perm { env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} }, perm: ref [m] }` failed at the following rule(s):
                                                            the rule "collect" at (redperms.rs) failed because
                                                              judgment `some_expanded_red_chain { perm: ref [m], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "(mut | ref) from given" at (redperms.rs) failed because
                                                                  no variable named `m`
                                                                the rule "(mut | ref) from non-given" at (redperms.rs) failed because
                                                                  no variable named `m`
                                                                the rule "inextensible" at (redperms.rs) failed because
                                                                  pattern `None | Some(RedLink::Shared) | Some(RedLink::Var(_))` did not match value `Some(Rfd(m))`
                                                                the rule "mv" at (redperms.rs) failed because
                                                                  pattern `Some((red_chain_head, RedLink::Mv(place)))` did not match value `Some((RedChain { links: [] }, Rfd(m)))`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn c1_given_not_subtype_of_leased() {
    // `given` is not a subtype of leased. This is actually because of the layout rules;
    // permissions-wise they would be compatible.
    crate::assert_err!({
        class Data { }
        class Main {
            fn test(given self) {
                let m: given Data = new Data();
                let p: mut[m] Data = new Data();
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self) -> () { let m : given Data = new Data () ; let p : mut [m] Data = new Data () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let m : given Data = new Data () ; let p : mut [m] Data = new Data () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let m : given Data = new Data () ; let p : mut [m] Data = new Data () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let m : given Data = new Data () ; let p : mut [m] Data = new Data () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let m : given Data = new Data () ; let p : mut [m] Data = new Data () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let m : given Data = new Data () ; let p : mut [m] Data = new Data () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let m : given Data = new Data () ;, let p : mut [m] Data = new Data () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let p : mut [m] Data = new Data () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statement { statement: let p : mut [m] Data = new Data () ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "let" at (statements.rs) failed because
                                                  judgment `type_expr_as { expr: new Data (), as_ty: mut [m] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "type_expr_as" at (expressions.rs) failed because
                                                      judgment `sub { a: Data, b: mut [m] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "sub-classes" at (subtypes.rs) failed because
                                                          judgment `sub_perms { perm_a: given, perm_b: mut [m], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                                              judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Mtd(m)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                                  judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Mtd(m)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "(given) vs (given)" at (redperms.rs) failed because
                                                                      judgment `prove_is_given { a: mut [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "prove" at (predicates.rs) failed because
                                                                          judgment `prove_is_owned { a: mut [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "is-owned" at (predicates.rs) failed because
                                                                              judgment `prove_predicate { predicate: owned(mut [m]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "parameter" at (predicates.rs) failed because
                                                                                  pattern `true` did not match value `false`"#]]);
}

#[test]
fn c1_leased_not_subtype_of_shared() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test(given self) {
                let m: given Data = new Data();
                let p: mut[m] Data = m.mut;
                let q: ref[m] Data = p.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self) -> () { let m : given Data = new Data () ; let p : mut [m] Data = m . mut ; let q : ref [m] Data = p . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let m : given Data = new Data () ; let p : mut [m] Data = m . mut ; let q : ref [m] Data = p . give ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let m : given Data = new Data () ; let p : mut [m] Data = m . mut ; let q : ref [m] Data = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let m : given Data = new Data () ; let p : mut [m] Data = m . mut ; let q : ref [m] Data = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let m : given Data = new Data () ; let p : mut [m] Data = m . mut ; let q : ref [m] Data = p . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let m : given Data = new Data () ; let p : mut [m] Data = m . mut ; let q : ref [m] Data = p . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let m : given Data = new Data () ;, let p : mut [m] Data = m . mut ;, let q : ref [m] Data = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let p : mut [m] Data = m . mut ;, let q : ref [m] Data = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let q : ref [m] Data = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: mut [m] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statement { statement: let q : ref [m] Data = p . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: mut [m] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "let" at (statements.rs) failed because
                                                      judgment `type_expr_as { expr: p . give, as_ty: ref [m] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: mut [m] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "type_expr_as" at (expressions.rs) failed because
                                                          judgment `sub { a: mut [m] Data, b: ref [m] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "sub-classes" at (subtypes.rs) failed because
                                                              judgment `sub_perms { perm_a: mut [m], perm_b: ref [m], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                                  judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Mtd(m)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Rfd(m)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                                                      judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtd(m)] }, red_chain_b: RedChain { links: [Rfd(m)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "(mut-dead::P) vs Q ~~> (P) vs Q" at (redperms.rs) failed because
                                                                          judgment `prove_is_mut { a: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "is-mut" at (predicates.rs) failed because
                                                                              judgment `prove_predicate { predicate: mut(given), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "parameter" at (predicates.rs) failed because
                                                                                  pattern `true` did not match value `false`
                                                                        the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                                                          judgment `prove_is_copy_owned { a: mut [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "prove" at (predicates.rs) failed because
                                                                              judgment `prove_is_copy { a: mut [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "is" at (predicates.rs) failed because
                                                                                  judgment `prove_predicate { predicate: copy(mut [m]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "parameter" at (predicates.rs) failed because
                                                                                      pattern `true` did not match value `false`"#]]);
}

#[test]
fn c1_shared_not_subtype_of_leased() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test(given self) {
                let m: given Data = new Data();
                let p: ref[m] Data = m.ref;
                let q: mut[m] Data = p.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self) -> () { let m : given Data = new Data () ; let p : ref [m] Data = m . ref ; let q : mut [m] Data = p . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let m : given Data = new Data () ; let p : ref [m] Data = m . ref ; let q : mut [m] Data = p . give ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let m : given Data = new Data () ; let p : ref [m] Data = m . ref ; let q : mut [m] Data = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let m : given Data = new Data () ; let p : ref [m] Data = m . ref ; let q : mut [m] Data = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let m : given Data = new Data () ; let p : ref [m] Data = m . ref ; let q : mut [m] Data = p . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let m : given Data = new Data () ; let p : ref [m] Data = m . ref ; let q : mut [m] Data = p . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let m : given Data = new Data () ;, let p : ref [m] Data = m . ref ;, let q : mut [m] Data = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let p : ref [m] Data = m . ref ;, let q : mut [m] Data = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let q : mut [m] Data = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: ref [m] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statement { statement: let q : mut [m] Data = p . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: ref [m] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "let" at (statements.rs) failed because
                                                      judgment `type_expr_as { expr: p . give, as_ty: mut [m] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: ref [m] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "type_expr_as" at (expressions.rs) failed because
                                                          judgment `sub { a: ref [m] Data, b: mut [m] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "sub-classes" at (subtypes.rs) failed because
                                                              judgment `sub_perms { perm_a: ref [m], perm_b: mut [m], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                                  judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Rfd(m)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Mtd(m)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                                                      judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Rfd(m)] }, red_chain_b: RedChain { links: [Mtd(m)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "(ref-dead::P) vs Q ~~> (shared::P) vs Q" at (redperms.rs) failed because
                                                                          judgment `prove_is_mut { a: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "is-mut" at (predicates.rs) failed because
                                                                              judgment `prove_predicate { predicate: mut(given), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "parameter" at (predicates.rs) failed because
                                                                                  pattern `true` did not match value `false`
                                                                        the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                                                          judgment `prove_is_copy_owned { a: ref [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "prove" at (predicates.rs) failed because
                                                                              judgment `prove_is_owned { a: ref [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "is-owned" at (predicates.rs) failed because
                                                                                  judgment `prove_predicate { predicate: owned(ref [m]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "parameter" at (predicates.rs) failed because
                                                                                      pattern `true` did not match value `false`"#]]);
}

// C2. This also includes restrictions on what can be done in the environment. So `ref[d1] Foo` cannot
// be a subtype of `ref[d2] Foo` since the latter permits `d1` to be modified but the subtype does not.
// (The latter also restricts edits to `d2`, but that's ok in the supertype, it can be more restrictive.)

#[test]
#[allow(non_snake_case)]
fn c2_shared_m_subtype_of_shared_mn() {
    // `ref[m]` is a subtype of `ref[m, n]`: neither permit `m` to be modified.
    // The supertype `ref[m, n]` additionally prohibits `n` from being modified.
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test(given self) {
                let m: given Data = new Data();
                let n: given Data = new Data();
                let p: ref[m] Data = m.ref;
                let q: ref[m, n] Data = p.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn c2_leased_m_subtype_of_leased_mn() {
    // `mut[m]` is a subtype of `mut[m, n]`: neither permit `m` to be modified.
    // The supertype `mut[m, n]` additionally prohibits `n` from being modified.
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test(given self) {
                let m: given Data = new Data();
                let n: given Data = new Data();
                let p: mut[m] Data = m.mut;
                let q: mut[m, n] Data = p.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn c2_leased_mn_not_subtype_of_leased_m() {
    // `mut[m, n]` is not a subtype of `mut[m]`: the supertype permits `n` to be modified.
    crate::assert_err!({
        class Data { }
        class Main {
            fn test(given self) {
                let m: given Data = new Data();
                let n: given Data = new Data();
                let p: mut[m, n] Data = m.mut;
                let q: mut[m] Data = p.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self) -> () { let m : given Data = new Data () ; let n : given Data = new Data () ; let p : mut [m, n] Data = m . mut ; let q : mut [m] Data = p . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let m : given Data = new Data () ; let n : given Data = new Data () ; let p : mut [m, n] Data = m . mut ; let q : mut [m] Data = p . give ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let m : given Data = new Data () ; let n : given Data = new Data () ; let p : mut [m, n] Data = m . mut ; let q : mut [m] Data = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let m : given Data = new Data () ; let n : given Data = new Data () ; let p : mut [m, n] Data = m . mut ; let q : mut [m] Data = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let m : given Data = new Data () ; let n : given Data = new Data () ; let p : mut [m, n] Data = m . mut ; let q : mut [m] Data = p . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let m : given Data = new Data () ; let n : given Data = new Data () ; let p : mut [m, n] Data = m . mut ; let q : mut [m] Data = p . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let m : given Data = new Data () ;, let n : given Data = new Data () ;, let p : mut [m, n] Data = m . mut ;, let q : mut [m] Data = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let n : given Data = new Data () ;, let p : mut [m, n] Data = m . mut ;, let q : mut [m] Data = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let p : mut [m, n] Data = m . mut ;, let q : mut [m] Data = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statements_with_final_ty { statements: [let q : mut [m] Data = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "cons" at (statements.rs) failed because
                                                      judgment `type_statement { statement: let q : mut [m] Data = p . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "let" at (statements.rs) failed because
                                                          judgment `type_expr_as { expr: p . give, as_ty: mut [m] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "type_expr_as" at (expressions.rs) failed because
                                                              judgment `sub { a: mut [m, n] Data, b: mut [m] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "sub-classes" at (subtypes.rs) failed because
                                                                  judgment `sub_perms { perm_a: mut [m, n], perm_b: mut [m], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                                                      judgment `"flat_map"` failed at the following rule(s):
                                                                        failed at (quantifiers.rs) because
                                                                          judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Mtd(n)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Mtd(m)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                                                              judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtd(n)] }, red_chain_b: RedChain { links: [Mtd(m)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "(mut-dead::P) vs Q ~~> (P) vs Q" at (redperms.rs) failed because
                                                                                  judgment `prove_is_mut { a: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "is-mut" at (predicates.rs) failed because
                                                                                      judgment `prove_predicate { predicate: mut(given), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "parameter" at (predicates.rs) failed because
                                                                                          pattern `true` did not match value `false`
                                                                                the rule "(mut::P) vs (mut::P)" at (redperms.rs) failed because
                                                                                  condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                                                                    place_b = m
                                                                                    &place_a = n
                                                                                the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                                                                  judgment `prove_is_copy_owned { a: mut [n], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "prove" at (predicates.rs) failed because
                                                                                      judgment `prove_is_copy { a: mut [n], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "is" at (predicates.rs) failed because
                                                                                          judgment `prove_predicate { predicate: copy(mut [n]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, m: given Data, n: given Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                                              pattern `true` did not match value `false`"#]]);
}
