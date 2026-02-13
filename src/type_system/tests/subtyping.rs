//! Tests for subtyping. These tests can be grouped into various categories.
//!
//! ## Liskov Substitution Principle (LSP)
//!
//! The "Liskov Substitution Principle" is that if T1 <: T2, then a value of type T1 can be
//! substituted for a value of type T2 and nothing can go wrong. The "liskov" directory
//! aims to systematically explore this area.
//!
//! ## Other stuff
//!
//! The other tests here need to be categorized. =)

use formality_core::test;

mod liskov;

#[test]
#[allow(non_snake_case)]
fn forall__P__give__from__given_d1__to__ref_to_shared_d2() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self, d1: given Data, d2: P Data) -> ref[d2] Data {
                d1.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self d1 : given Data, d2 : ^perm0_0 Data) -> ref [d2] Data { d1 . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { d1 . give ; }, output: ref [d2] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { d1 . give ; }, as_ty: ref [d2] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { d1 . give ; }, as_ty: ref [d2] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: given Data, b: ref [d2] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_perms { perm_a: given, perm_b: ref [d2], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                      judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Rfd(d2), Var(!perm_0)] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                          judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Rfd(d2), Var(!perm_0)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "(given) vs (given)" at (redperms.rs) failed because
                                              judgment `prove_is_given { a: ref [d2] !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "prove" at (predicates.rs) failed because
                                                  judgment `prove_is_move { a: ref [d2] !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "is-moved" at (predicates.rs) failed because
                                                      judgment `prove_predicate { predicate: move(ref [d2] !perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "mut => move" at (predicates.rs) failed because
                                                          judgment `prove_is_mut { a: ref [d2] !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "is-mut" at (predicates.rs) failed because
                                                              judgment `prove_predicate { predicate: mut(ref [d2] !perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: given Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "parameter" at (predicates.rs) failed because
                                                                  pattern `true` did not match value `false`
                                                        the rule "parameter" at (predicates.rs) failed because
                                                          pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall__P__give__from__shared_given_d1__to__ref_to_shared_d2() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self, d1: given Data, d2: P Data) -> ref[d2] Data {
                d1.share;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn forall_copy_P_give_from_shared_d2_P_to_shared_d2() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self, d1: given Data, d2: P Data) -> ref[d2] Data
            where
                copy(P),
            {
                d2.ref;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn forall_copy_P_give_from_shared_d2_P_to_P() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self, d1: given Data, d2: P Data) -> P Data
            where
                copy(P),
            {
                d2.ref;
            }
        }
        });
}

#[test]
fn move_from_given_d1_to_our_d2() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test(given self, d1: given Data) -> shared Data {
                d1.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self d1 : given Data) -> shared Data { d1 . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { d1 . give ; }, output: shared Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { d1 . give ; }, as_ty: shared Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { d1 . give ; }, as_ty: shared Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: given Data, b: shared Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_perms { perm_a: given, perm_b: shared, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                      judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Shared] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                          judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Shared] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "(given) vs (given)" at (redperms.rs) failed because
                                              judgment `prove_is_given { a: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "prove" at (predicates.rs) failed because
                                                  judgment `prove_is_move { a: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "is-moved" at (predicates.rs) failed because
                                                      judgment `prove_predicate { predicate: move(shared), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "mut => move" at (predicates.rs) failed because
                                                          judgment `prove_is_mut { a: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "is-mut" at (predicates.rs) failed because
                                                              judgment `prove_predicate { predicate: mut(shared), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "parameter" at (predicates.rs) failed because
                                                                  pattern `true` did not match value `false`
                                                        the rule "parameter" at (predicates.rs) failed because
                                                          pattern `true` did not match value `false`"#]]);
}

#[test]
fn share_from_given_d1_to_our_d2() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test(given self, d1: given Data) -> shared Data {
                d1.share;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn give_from_our_Data_to_shared_self() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test(given self) -> ref[self] Data {
                let d: shared Data = new Data().share;
                d.give;
            }
        }
        });
}

/// `shared` is a subtype of `copy(P)`.
#[test]
#[allow(non_snake_case)]
fn give_from_our_Data_to_copy_P() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self) -> P Data
            where
              copy(P)
            {
                let d: shared Data = new Data().share;
                d.give;
            }
        }
        });
}

/// `shared` is not a subtype of arbitrary P.
#[test]
#[allow(non_snake_case)]
fn give_from_our_Data_to_any_P() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) -> P Data
            {
                let d: shared Data = new Data();
                d.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self) -> ^perm0_0 Data { let d : shared Data = new Data () ; d . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let d : shared Data = new Data () ; d . give ; }, output: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let d : shared Data = new Data () ; d . give ; }, as_ty: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let d : shared Data = new Data () ; d . give ; }, as_ty: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let d : shared Data = new Data () ; d . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let d : shared Data = new Data () ; d . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let d : shared Data = new Data () ;, d . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statement { statement: let d : shared Data = new Data () ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {d}, traversed: {} } }` failed at the following rule(s):
                                            the rule "let" at (statements.rs) failed because
                                              judgment `type_expr_as { expr: new Data (), as_ty: shared Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "type_expr_as" at (expressions.rs) failed because
                                                  judgment `sub { a: Data, b: shared Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "sub-classes" at (subtypes.rs) failed because
                                                      judgment `sub_perms { perm_a: given, perm_b: shared, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                                          judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Shared] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                                              judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Shared] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "(given) vs (given)" at (redperms.rs) failed because
                                                                  judgment `prove_is_given { a: shared, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "prove" at (predicates.rs) failed because
                                                                      judgment `prove_is_move { a: shared, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "is-moved" at (predicates.rs) failed because
                                                                          judgment `prove_predicate { predicate: move(shared), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "mut => move" at (predicates.rs) failed because
                                                                              judgment `prove_is_mut { a: shared, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "is-mut" at (predicates.rs) failed because
                                                                                  judgment `prove_predicate { predicate: mut(shared), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "parameter" at (predicates.rs) failed because
                                                                                      pattern `true` did not match value `false`
                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                              pattern `true` did not match value `false`"#]]);
}

/// `shared` is not a subtype of arbitrary P.
#[test]
#[allow(non_snake_case)]
fn give_from_our_Data_to_leased_P() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) -> P Data
            where
                mut(P),
            {
                let d: shared Data = new Data();
                d.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self) -> ^perm0_0 Data where mut(^perm0_0) { let d : shared Data = new Data () ; d . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let d : shared Data = new Data () ; d . give ; }, output: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let d : shared Data = new Data () ; d . give ; }, as_ty: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let d : shared Data = new Data () ; d . give ; }, as_ty: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let d : shared Data = new Data () ; d . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let d : shared Data = new Data () ; d . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let d : shared Data = new Data () ;, d . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statement { statement: let d : shared Data = new Data () ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {d}, traversed: {} } }` failed at the following rule(s):
                                            the rule "let" at (statements.rs) failed because
                                              judgment `type_expr_as { expr: new Data (), as_ty: shared Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "type_expr_as" at (expressions.rs) failed because
                                                  judgment `sub { a: Data, b: shared Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "sub-classes" at (subtypes.rs) failed because
                                                      judgment `sub_perms { perm_a: given, perm_b: shared, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                                          judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Shared] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                                              judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Shared] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "(given) vs (given)" at (redperms.rs) failed because
                                                                  judgment `prove_is_given { a: shared, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "prove" at (predicates.rs) failed because
                                                                      judgment `prove_is_move { a: shared, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "is-moved" at (predicates.rs) failed because
                                                                          judgment `prove_predicate { predicate: move(shared), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "mut => move" at (predicates.rs) failed because
                                                                              judgment `prove_is_mut { a: shared, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "is-mut" at (predicates.rs) failed because
                                                                                  judgment `prove_predicate { predicate: mut(shared), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "parameter" at (predicates.rs) failed because
                                                                                      pattern `true` did not match value `false`
                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                              pattern `true` did not match value `false`"#]]);
}

#[test]
fn share_from_given_d1_our_d2_to_given_from_d2() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test(given self, d1: given Data, d2: shared Data) -> given_from[d2] Data {
                d1.share;
            }
        }
        });
}

/// Return "given" from `d1` and give from `d1`.
/// It is indistinguishable as both of them are `shared` Data, so the result is `shared`.
#[test]
fn share_from_our_d1_our_d2_to_given_from_d1() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test(given self, d1: shared Data, d2: shared Data) -> given_from[d1] Data {
                d1.ref;
            }
        }
        });
}

/// Return "given" from `d2` even though we really give from `d1`.
/// It is indistinguishable as both of them are `shared` Data, so the result is `shared`.
#[test]
fn share_from_our_d1_our_d2_to_given_from_d2() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test(given self, d1: shared Data, d2: shared Data) -> given_from[d2] Data {
                d1.ref;
            }
        }
        });
}

/// Return "given" from `d2` even though we really give from `d1`.
/// It is indistinguishable as both of them are `shared` Data, so the result is `shared`.
#[test]
fn share_from_local_to_our() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test(given self, d1: shared Data, d2: shared Data) -> given_from[d2] Data {
                let d = new Data();
                d.ref;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self d1 : shared Data, d2 : shared Data) -> given_from [d2] Data { let d = new Data () ; d . ref ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let d = new Data () ; d . ref ; }, output: given_from [d2] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Data, d2: shared Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let d = new Data () ; d . ref ; }, as_ty: given_from [d2] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Data, d2: shared Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let d = new Data () ; d . ref ; }, as_ty: given_from [d2] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Data, d2: shared Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: ref [d] Data, b: given_from [d2] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, d1: shared Data, d2: shared Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_perms { perm_a: ref [d], perm_b: given_from [d2], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, d1: shared Data, d2: shared Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                      judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Rfd(d)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Shared] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, d1: shared Data, d2: shared Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                          judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Rfd(d)] }, red_chain_b: RedChain { links: [Shared] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, d1: shared Data, d2: shared Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "(ref-dead::P) vs Q ~~> (shared::P) vs Q" at (redperms.rs) failed because
                                              judgment `prove_is_mut { a: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, d1: shared Data, d2: shared Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "is-mut" at (predicates.rs) failed because
                                                  judgment `prove_predicate { predicate: mut(given), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, d1: shared Data, d2: shared Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "parameter" at (predicates.rs) failed because
                                                      pattern `true` did not match value `false`
                                            the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                              judgment `prove_is_copy_owned { a: ref [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, d1: shared Data, d2: shared Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "prove" at (predicates.rs) failed because
                                                  judgment `prove_is_owned { a: ref [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, d1: shared Data, d2: shared Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "is-owned" at (predicates.rs) failed because
                                                      judgment `prove_predicate { predicate: owned(ref [d]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, d1: shared Data, d2: shared Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "parameter" at (predicates.rs) failed because
                                                          pattern `true` did not match value `false`"#]]);
}

#[test]
fn provide_shared_from_d1_expect_shared_from_d1() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test(given self, d1: given Data, d2: given Data) -> ref[d1] Data {
                d1.ref;
            }
        }
        });
}

#[test]
fn provide_shared_from_d2_expect_shared_from_d1() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test(given self, d1: given Data, d2: given Data) -> ref[d1] Data {
                d2.ref;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self d1 : given Data, d2 : given Data) -> ref [d1] Data { d2 . ref ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { d2 . ref ; }, output: ref [d1] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { d2 . ref ; }, as_ty: ref [d1] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { d2 . ref ; }, as_ty: ref [d1] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: ref [d2] Data, b: ref [d1] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_perms { perm_a: ref [d2], perm_b: ref [d1], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                      judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Rfd(d2)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Rfd(d1)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                          judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Rfd(d2)] }, red_chain_b: RedChain { links: [Rfd(d1)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "(ref-dead::P) vs Q ~~> (shared::P) vs Q" at (redperms.rs) failed because
                                              judgment `prove_is_mut { a: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "is-mut" at (predicates.rs) failed because
                                                  judgment `prove_predicate { predicate: mut(given), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "parameter" at (predicates.rs) failed because
                                                      pattern `true` did not match value `false`
                                            the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
                                              condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                                place_b = d1
                                                &place_a = d2
                                            the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                              judgment `prove_is_copy_owned { a: ref [d2], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "prove" at (predicates.rs) failed because
                                                  judgment `prove_is_owned { a: ref [d2], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "is-owned" at (predicates.rs) failed because
                                                      judgment `prove_predicate { predicate: owned(ref [d2]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "parameter" at (predicates.rs) failed because
                                                          pattern `true` did not match value `false`"#]]);
}

#[test]
fn provide_shared_from_d2_expect_shared_from_d1_or_d2() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test(given self, d1: given Data, d2: given Data) -> ref[d1, d2] Data {
                d2.ref;
            }
        }
        });
}

#[test]
fn provide_shared_from_d1_next_expect_shared_from_d1() {
    crate::assert_ok!({
        class Data {
            next: given Data;
        }

        class Main {
            fn test(given self, d1: given Data, d2: given Data) -> ref[d1] Data {
                d1.next.ref;
            }
        }
        });
}

#[test]
fn provide_shared_from_d1_next_expect_shared_from_d2() {
    crate::assert_err!({
        class Data {
            next: given Data;
        }

        class Main {
            fn test(given self, d1: given Data, d2: given Data) -> ref[d2] Data {
                d1.next.ref;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self d1 : given Data, d2 : given Data) -> ref [d2] Data { d1 . next . ref ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { d1 . next . ref ; }, output: ref [d2] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { d1 . next . ref ; }, as_ty: ref [d2] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { d1 . next . ref ; }, as_ty: ref [d2] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: ref [d1 . next] Data, b: ref [d2] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_perms { perm_a: ref [d1 . next], perm_b: ref [d2], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                      judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Rfd(d1 . next)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Rfd(d2)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                          judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Rfd(d1 . next)] }, red_chain_b: RedChain { links: [Rfd(d2)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "(ref-dead::P) vs Q ~~> (shared::P) vs Q" at (redperms.rs) failed because
                                              judgment `prove_is_mut { a: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "is-mut" at (predicates.rs) failed because
                                                  judgment `prove_predicate { predicate: mut(given), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "parameter" at (predicates.rs) failed because
                                                      pattern `true` did not match value `false`
                                            the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
                                              condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                                place_b = d2
                                                &place_a = d1 . next
                                            the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                              judgment `prove_is_copy_owned { a: ref [d1 . next], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "prove" at (predicates.rs) failed because
                                                  judgment `prove_is_owned { a: ref [d1 . next], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "is-owned" at (predicates.rs) failed because
                                                      judgment `prove_predicate { predicate: owned(ref [d1 . next]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "parameter" at (predicates.rs) failed because
                                                          pattern `true` did not match value `false`"#]]);
}

#[test]
fn provide_shared_from_d1_expect_shared_from_d1_next() {
    crate::assert_err!({
        class Data {
            next: given Data;
        }

        class Main {
            fn test(given self, d1: given Data, d2: given Data) -> ref[d1.next] Data {
                d1.ref;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self d1 : given Data, d2 : given Data) -> ref [d1 . next] Data { d1 . ref ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { d1 . ref ; }, output: ref [d1 . next] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { d1 . ref ; }, as_ty: ref [d1 . next] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { d1 . ref ; }, as_ty: ref [d1 . next] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: ref [d1] Data, b: ref [d1 . next] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_perms { perm_a: ref [d1], perm_b: ref [d1 . next], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                      judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Rfd(d1)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Rfd(d1 . next)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                          judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Rfd(d1)] }, red_chain_b: RedChain { links: [Rfd(d1 . next)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "(ref-dead::P) vs Q ~~> (shared::P) vs Q" at (redperms.rs) failed because
                                              judgment `prove_is_mut { a: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "is-mut" at (predicates.rs) failed because
                                                  judgment `prove_predicate { predicate: mut(given), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "parameter" at (predicates.rs) failed because
                                                      pattern `true` did not match value `false`
                                            the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
                                              condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                                place_b = d1 . next
                                                &place_a = d1
                                            the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                              judgment `prove_is_copy_owned { a: ref [d1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "prove" at (predicates.rs) failed because
                                                  judgment `prove_is_owned { a: ref [d1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "is-owned" at (predicates.rs) failed because
                                                      judgment `prove_predicate { predicate: owned(ref [d1]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "parameter" at (predicates.rs) failed because
                                                          pattern `true` did not match value `false`"#]]);
}

#[test]
fn provide_leased_from_d1_next_expect_shared_from_d1() {
    crate::assert_err!({
        class Data {
            next: given Data;
        }

        class Main {
            fn test(given self, d1: given Data, d2: given Data) -> ref[d1] Data {
                d1.next.mut;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self d1 : given Data, d2 : given Data) -> ref [d1] Data { d1 . next . mut ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { d1 . next . mut ; }, output: ref [d1] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { d1 . next . mut ; }, as_ty: ref [d1] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { d1 . next . mut ; }, as_ty: ref [d1] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: mut [d1 . next] Data, b: ref [d1] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_perms { perm_a: mut [d1 . next], perm_b: ref [d1], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                      judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Mtd(d1 . next)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Rfd(d1)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                          judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtd(d1 . next)] }, red_chain_b: RedChain { links: [Rfd(d1)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "(mut-dead::P) vs Q ~~> (P) vs Q" at (redperms.rs) failed because
                                              judgment `prove_is_mut { a: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "is-mut" at (predicates.rs) failed because
                                                  judgment `prove_predicate { predicate: mut(given), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "parameter" at (predicates.rs) failed because
                                                      pattern `true` did not match value `false`
                                            the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                              judgment `prove_is_copy_owned { a: mut [d1 . next], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "prove" at (predicates.rs) failed because
                                                  judgment `prove_is_copy { a: mut [d1 . next], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "is" at (predicates.rs) failed because
                                                      judgment `prove_predicate { predicate: copy(mut [d1 . next]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: given Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "parameter" at (predicates.rs) failed because
                                                          pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn shared_from_P_d1_to_given_from_P_d1() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self, d1: P Data, d2: shared Data) -> given_from[d1] Data {
                d1.ref;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self d1 : ^perm0_0 Data, d2 : shared Data) -> given_from [d1] Data { d1 . ref ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { d1 . ref ; }, output: given_from [d1] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: !perm_0 Data, d2: shared Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { d1 . ref ; }, as_ty: given_from [d1] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: !perm_0 Data, d2: shared Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { d1 . ref ; }, as_ty: given_from [d1] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: !perm_0 Data, d2: shared Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: ref [d1] Data, b: given_from [d1] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: !perm_0 Data, d2: shared Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_perms { perm_a: ref [d1], perm_b: given_from [d1], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: !perm_0 Data, d2: shared Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                      judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Rfd(d1), Var(!perm_0)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Var(!perm_0)] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: !perm_0 Data, d2: shared Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                          judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Rfd(d1), Var(!perm_0)] }, red_chain_b: RedChain { links: [Var(!perm_0)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: !perm_0 Data, d2: shared Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "(ref-dead::P) vs Q ~~> (shared::P) vs Q" at (redperms.rs) failed because
                                              judgment `prove_is_mut { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: !perm_0 Data, d2: shared Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "is-mut" at (predicates.rs) failed because
                                                  judgment `prove_predicate { predicate: mut(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: !perm_0 Data, d2: shared Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "parameter" at (predicates.rs) failed because
                                                      pattern `true` did not match value `false`
                                            the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                              judgment `prove_is_copy_owned { a: ref [d1], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: !perm_0 Data, d2: shared Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "prove" at (predicates.rs) failed because
                                                  judgment `prove_is_owned { a: ref [d1], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: !perm_0 Data, d2: shared Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "is-owned" at (predicates.rs) failed because
                                                      judgment `prove_predicate { predicate: owned(ref [d1]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: !perm_0 Data, d2: shared Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "parameter" at (predicates.rs) failed because
                                                          pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn given_from_P_d1_to_given_from_P_d1() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self, d1: P Data, d2: shared Data) -> given_from[d1] Data {
                d1.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn given_from_P_d1_to_given_from_P_d2() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P, perm Q](given self, d1: P Data, d2: P Data) -> given_from[d2] Data {
                d1.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn given_from_P_d1_to_given_from_Q_d2() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P, perm Q](given self, d1: P Data, d2: Q Data) -> given_from[d2] Data {
                d1.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm, perm] (given self d1 : ^perm0_0 Data, d2 : ^perm0_1 Data) -> given_from [d2] Data { d1 . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { d1 . give ; }, output: given_from [d2] Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { d1 . give ; }, as_ty: given_from [d2] Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { d1 . give ; }, as_ty: given_from [d2] Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: !perm_0 Data, b: given_from [d2] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_perms { perm_a: !perm_0, perm_b: given_from [d2], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                      judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Var(!perm_0)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Var(!perm_1)] }} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                          judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Var(!perm_0)] }, red_chain_b: RedChain { links: [Var(!perm_1)] }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "(shared) vs (copy)" at (redperms.rs) failed because
                                              judgment `prove_is_copy_owned { a: !perm_0, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "prove" at (predicates.rs) failed because
                                                  judgment `prove_is_copy { a: !perm_0, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "is" at (predicates.rs) failed because
                                                      judgment `prove_predicate { predicate: copy(!perm_0), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "parameter" at (predicates.rs) failed because
                                                          pattern `true` did not match value `false`
                                            the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                              judgment `prove_is_copy_owned { a: !perm_0, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "prove" at (predicates.rs) failed because
                                                  judgment `prove_is_copy { a: !perm_0, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "is" at (predicates.rs) failed because
                                                      judgment `prove_predicate { predicate: copy(!perm_0), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "parameter" at (predicates.rs) failed because
                                                          pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn shared_from_P_d1_to_shared_from_P_d1() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P, perm Q](given self, d1: P Data, d2: P Data) -> ref[d1] Data {
                d1.ref;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn shared_from_P_d1_to_shared_from_P_d2() {
    // Interesting example: we declare `ref[d2]` but return `ref[d1]`.
    // Even though both of them have permission `P`, we give an error.
    // The distinction of which `P` we shared from is important: we are not going to be incrementing
    // the ref count, so if `d1` were dropped, which the type signature suggests would be ok,
    // then the data would be freed.
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P, perm Q](given self, d1: P Data, d2: P Data) -> ref[d2] Data {
                d1.ref;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm, perm] (given self d1 : ^perm0_0 Data, d2 : ^perm0_0 Data) -> ref [d2] Data { d1 . ref ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { d1 . ref ; }, output: ref [d2] Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { d1 . ref ; }, as_ty: ref [d2] Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { d1 . ref ; }, as_ty: ref [d2] Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: ref [d1] Data, b: ref [d2] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_perms { perm_a: ref [d1], perm_b: ref [d2], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                      judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Rfd(d1), Var(!perm_0)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Rfd(d2), Var(!perm_0)] }} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                          judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Rfd(d1), Var(!perm_0)] }, red_chain_b: RedChain { links: [Rfd(d2), Var(!perm_0)] }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "(ref-dead::P) vs Q ~~> (shared::P) vs Q" at (redperms.rs) failed because
                                              judgment `prove_is_mut { a: !perm_0, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "is-mut" at (predicates.rs) failed because
                                                  judgment `prove_predicate { predicate: mut(!perm_0), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "parameter" at (predicates.rs) failed because
                                                      pattern `true` did not match value `false`
                                            the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
                                              condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                                place_b = d2
                                                &place_a = d1
                                            the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                              judgment `prove_is_copy_owned { a: ref [d1], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "prove" at (predicates.rs) failed because
                                                  judgment `prove_is_owned { a: ref [d1], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "is-owned" at (predicates.rs) failed because
                                                      judgment `prove_predicate { predicate: owned(ref [d1]), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "parameter" at (predicates.rs) failed because
                                                          pattern `true` did not match value `false`"#]]);
}

/// This case is wacky. The type of `data` is not really possible, as it indicates that data which was `mut[pair2]` was
/// shared from `pair1`, but `pair1` does not have any data leased from `pair2` in its type.
/// Currently we allow this to be upcast to `ref[pair1]` on the premise that is ok to lose history.
/// It seems to me that the type of `data` should (ideally) not be considered well-formed, but otherwise
/// this function is ok, it just could never actually be called.
#[test]
#[allow(non_snake_case)]
fn shared_pair1_leased_pair2_to_shared_pair1() {
    crate::assert_err!({
        class Pair {
            d1: Data;
            d2: Data;
        }
        class Data {
        }
        class Main {
            fn test(given self, pair1: Pair, pair2: Pair, data: ref[pair1] mut[pair2] Data) -> ref[pair1] Data {
                data.share;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self pair1 : Pair, pair2 : Pair, data : ref [pair1] mut [pair2] Data) -> ref [pair1] Data { data . share ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { data . share ; }, output: ref [pair1] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: ref [pair1] mut [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { data . share ; }, as_ty: ref [pair1] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: ref [pair1] mut [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { data . share ; }, as_ty: ref [pair1] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: ref [pair1] mut [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: shared ref [pair1] mut [pair2] Data, b: ref [pair1] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: ref [pair1] mut [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_perms { perm_a: shared ref [pair1] mut [pair2], perm_b: ref [pair1], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: ref [pair1] mut [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                      judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Rfd(pair1), Mtd(pair2)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Rfd(pair1)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: ref [pair1] mut [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                          judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Rfd(pair1), Mtd(pair2)] }, red_chain_b: RedChain { links: [Rfd(pair1)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: ref [pair1] mut [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "(ref-dead::P) vs Q ~~> (shared::P) vs Q" at (redperms.rs) failed because
                                              judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Shared, Mtd(pair2)] }, red_chain_b: RedChain { links: [Rfd(pair1)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: ref [pair1] mut [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                                  judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtd(pair2)] }, red_chain_b: RedChain { links: [] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: ref [pair1] mut [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "(mut-dead::P) vs Q ~~> (P) vs Q" at (redperms.rs) failed because
                                                      judgment `prove_is_mut { a: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: ref [pair1] mut [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "is-mut" at (predicates.rs) failed because
                                                          judgment `prove_predicate { predicate: mut(given), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: ref [pair1] mut [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "parameter" at (predicates.rs) failed because
                                                              pattern `true` did not match value `false`
                                            the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
                                              judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtd(pair2)] }, red_chain_b: RedChain { links: [] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: ref [pair1] mut [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "(mut-dead::P) vs Q ~~> (P) vs Q" at (redperms.rs) failed because
                                                  judgment `prove_is_mut { a: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: ref [pair1] mut [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "is-mut" at (predicates.rs) failed because
                                                      judgment `prove_predicate { predicate: mut(given), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: ref [pair1] mut [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "parameter" at (predicates.rs) failed because
                                                          pattern `true` did not match value `false`
                                            the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                              judgment `prove_is_copy_owned { a: ref [pair1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: ref [pair1] mut [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "prove" at (predicates.rs) failed because
                                                  judgment `prove_is_owned { a: ref [pair1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: ref [pair1] mut [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "is-owned" at (predicates.rs) failed because
                                                      judgment `prove_predicate { predicate: owned(ref [pair1]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: ref [pair1] mut [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "parameter" at (predicates.rs) failed because
                                                          pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn our_leased_to_our() {
    crate::assert_err!({
        class Pair {
            d1: Data;
            d2: Data;
        }
        class Data {
        }
        class Main {
            fn test(given self, pair: Pair, data: shared mut[pair] Data) -> shared Data {
                data.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self pair : Pair, data : shared mut [pair] Data) -> shared Data { data . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { data . give ; }, output: shared Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: shared mut [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { data . give ; }, as_ty: shared Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: shared mut [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { data . give ; }, as_ty: shared Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: shared mut [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: shared mut [pair] Data, b: shared Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: shared mut [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_perms { perm_a: shared mut [pair], perm_b: shared, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: shared mut [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                      judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Shared, Mtd(pair)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Shared] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: shared mut [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                          judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Shared, Mtd(pair)] }, red_chain_b: RedChain { links: [Shared] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: shared mut [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                              judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtd(pair)] }, red_chain_b: RedChain { links: [] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: shared mut [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "(mut-dead::P) vs Q ~~> (P) vs Q" at (redperms.rs) failed because
                                                  judgment `prove_is_mut { a: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: shared mut [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "is-mut" at (predicates.rs) failed because
                                                      judgment `prove_predicate { predicate: mut(given), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: shared mut [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "parameter" at (predicates.rs) failed because
                                                          pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn our_leased_pair_to_our_leased_pair() {
    crate::assert_ok!({
        class Pair {
            d1: Data;
            d2: Data;
        }
        class Data {
        }
        class Main {
            fn test(given self, pair: Pair, data: shared mut[pair] Data) -> shared mut[pair] Data {
                data.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn our_leased_pair_d1_to_our_leased_pair() {
    crate::assert_ok!({
        class Pair {
            d1: Data;
            d2: Data;
        }
        class Data {
        }
        class Main {
            fn test(given self, pair: Pair, data: shared mut[pair.d1] Data) -> shared mut[pair] Data {
                data.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn shared_vec_given_Data_to_shared_vec_given_Data() {
    crate::assert_ok!({
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(given self, source: given Vec[given Data], data: ref[source] Vec[given Data]) -> ref[source] Vec[given Data] {
                data.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn shared_vec_given_Data_to_shared_vec_shared_Data() {
    crate::assert_ok!({
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(given self, source: given Vec[given Data], data: ref[source] Vec[given Data]) -> ref[source] Vec[ref[source] Data] {
                data.share;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn leased_vec_given_Data_to_leased_vec_given_Data() {
    crate::assert_ok!({
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(given self, source: given Vec[given Data], data: mut[source] Vec[given Data]) -> mut[source] Vec[given Data] {
                data.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn leased_vec_given_Data_to_leased_vec_leased_Data() {
    crate::assert_err!({
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(given self, source: given Vec[given Data], data: mut[source] Vec[given Data]) -> mut[source] Vec[mut[source] Data] {
                data.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self source : given Vec[given Data], data : mut [source] Vec[given Data]) -> mut [source] Vec[mut [source] Data] { data . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { data . give ; }, output: mut [source] Vec[mut [source] Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[given Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { data . give ; }, as_ty: mut [source] Vec[mut [source] Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[given Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { data . give ; }, as_ty: mut [source] Vec[mut [source] Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[given Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: mut [source] Vec[given Data], b: mut [source] Vec[mut [source] Data], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[given Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_generic_parameter { perm_a: mut [source], a: given Data, perm_b: mut [source], b: mut [source] Data, variances: [], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[given Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "covariant-copy" at (subtypes.rs) failed because
                                      judgment `prove_is_copy { a: mut [source], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[given Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "is" at (predicates.rs) failed because
                                          judgment `prove_predicate { predicate: copy(mut [source]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[given Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "parameter" at (predicates.rs) failed because
                                              pattern `true` did not match value `false`
                                    the rule "covariant-owned" at (subtypes.rs) failed because
                                      judgment `prove_is_owned { a: mut [source], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[given Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "is-owned" at (predicates.rs) failed because
                                          judgment `prove_predicate { predicate: owned(mut [source]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[given Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "parameter" at (predicates.rs) failed because
                                              pattern `true` did not match value `false`
                                    the rule "invariant" at (subtypes.rs) failed because
                                      judgment `sub { a: given Data, b: mut [source] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[given Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub-classes" at (subtypes.rs) failed because
                                          judgment `sub_perms { perm_a: given, perm_b: mut [source], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[given Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                              judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Mtd(source)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[given Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                  judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Mtd(source)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[given Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "(given) vs (given)" at (redperms.rs) failed because
                                                      judgment `prove_is_given { a: mut [source], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[given Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "prove" at (predicates.rs) failed because
                                                          judgment `prove_is_owned { a: mut [source], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[given Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "is-owned" at (predicates.rs) failed because
                                                              judgment `prove_predicate { predicate: owned(mut [source]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[given Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "parameter" at (predicates.rs) failed because
                                                                  pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn leased_vec_leased_Data_to_leased_vec_given_Data() {
    crate::assert_err!({
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(given self, source: given Vec[given Data], data: mut[source] Vec[mut[source] Data]) -> mut[source] Vec[given Data] {
                data.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self source : given Vec[given Data], data : mut [source] Vec[mut [source] Data]) -> mut [source] Vec[given Data] { data . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { data . give ; }, output: mut [source] Vec[given Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[mut [source] Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { data . give ; }, as_ty: mut [source] Vec[given Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[mut [source] Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { data . give ; }, as_ty: mut [source] Vec[given Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[mut [source] Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: mut [source] Vec[mut [source] Data], b: mut [source] Vec[given Data], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[mut [source] Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_generic_parameter { perm_a: mut [source], a: mut [source] Data, perm_b: mut [source], b: given Data, variances: [], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[mut [source] Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "covariant-copy" at (subtypes.rs) failed because
                                      judgment `prove_is_copy { a: mut [source], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[mut [source] Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "is" at (predicates.rs) failed because
                                          judgment `prove_predicate { predicate: copy(mut [source]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[mut [source] Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "parameter" at (predicates.rs) failed because
                                              pattern `true` did not match value `false`
                                    the rule "covariant-owned" at (subtypes.rs) failed because
                                      judgment `prove_is_owned { a: mut [source], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[mut [source] Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "is-owned" at (predicates.rs) failed because
                                          judgment `prove_predicate { predicate: owned(mut [source]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[mut [source] Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "parameter" at (predicates.rs) failed because
                                              pattern `true` did not match value `false`
                                    the rule "invariant" at (subtypes.rs) failed because
                                      judgment `sub { a: mut [source] Data, b: given Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[mut [source] Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub-classes" at (subtypes.rs) failed because
                                          judgment `sub_perms { perm_a: mut [source], perm_b: given, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[mut [source] Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                              judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Mtd(source)] }, red_perm_b: RedPerm { chains: {RedChain { links: [] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[mut [source] Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                  judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtd(source)] }, red_chain_b: RedChain { links: [] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[mut [source] Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "(mut-dead::P) vs Q ~~> (P) vs Q" at (redperms.rs) failed because
                                                      judgment `prove_is_mut { a: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[mut [source] Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "is-mut" at (predicates.rs) failed because
                                                          judgment `prove_predicate { predicate: mut(given), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [source] Vec[mut [source] Data], source: given Vec[given Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "parameter" at (predicates.rs) failed because
                                                              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn leased_vec_leased_Data_to_leased_vec_leased_Data() {
    crate::assert_ok!({
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(given self, source: given Vec[given Data], data: mut[source] Vec[mut[source] Data]) -> mut[source] Vec[mut[source] Data] {
                data.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn forall_P_vec_given_Data_to_P_vec_P_Data() {
    crate::assert_err!({
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test[perm P](given self, source: given Vec[given Data], data: P Vec[Data]) -> P Vec[P Data] {
                data.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self source : given Vec[given Data], data : ^perm0_0 Vec[Data]) -> ^perm0_0 Vec[^perm0_0 Data] { data . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { data . give ; }, output: !perm_0 Vec[!perm_0 Data], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Vec[Data], source: given Vec[given Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { data . give ; }, as_ty: !perm_0 Vec[!perm_0 Data], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Vec[Data], source: given Vec[given Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { data . give ; }, as_ty: !perm_0 Vec[!perm_0 Data], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Vec[Data], source: given Vec[given Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: !perm_0 Vec[Data], b: !perm_0 Vec[!perm_0 Data], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Vec[Data], source: given Vec[given Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_generic_parameter { perm_a: !perm_0, a: Data, perm_b: !perm_0, b: !perm_0 Data, variances: [], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Vec[Data], source: given Vec[given Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "covariant-copy" at (subtypes.rs) failed because
                                      judgment `prove_is_copy { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Vec[Data], source: given Vec[given Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "is" at (predicates.rs) failed because
                                          judgment `prove_predicate { predicate: copy(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Vec[Data], source: given Vec[given Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "parameter" at (predicates.rs) failed because
                                              pattern `true` did not match value `false`
                                    the rule "covariant-owned" at (subtypes.rs) failed because
                                      judgment `prove_is_owned { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Vec[Data], source: given Vec[given Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "is-owned" at (predicates.rs) failed because
                                          judgment `prove_predicate { predicate: owned(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Vec[Data], source: given Vec[given Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "parameter" at (predicates.rs) failed because
                                              pattern `true` did not match value `false`
                                    the rule "invariant" at (subtypes.rs) failed because
                                      judgment `sub { a: Data, b: !perm_0 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Vec[Data], source: given Vec[given Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub-classes" at (subtypes.rs) failed because
                                          judgment `sub_perms { perm_a: given, perm_b: !perm_0, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Vec[Data], source: given Vec[given Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                              judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Var(!perm_0)] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Vec[Data], source: given Vec[given Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                  judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Var(!perm_0)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Vec[Data], source: given Vec[given Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "(given) vs (given)" at (redperms.rs) failed because
                                                      judgment `prove_is_given { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Vec[Data], source: given Vec[given Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "prove" at (predicates.rs) failed because
                                                          judgment `prove_is_move { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Vec[Data], source: given Vec[given Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "is-moved" at (predicates.rs) failed because
                                                              judgment `prove_predicate { predicate: move(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Vec[Data], source: given Vec[given Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "mut => move" at (predicates.rs) failed because
                                                                  judgment `prove_is_mut { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Vec[Data], source: given Vec[given Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "is-mut" at (predicates.rs) failed because
                                                                      judgment `prove_predicate { predicate: mut(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Vec[Data], source: given Vec[given Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "parameter" at (predicates.rs) failed because
                                                                          pattern `true` did not match value `false`
                                                                the rule "parameter" at (predicates.rs) failed because
                                                                  pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_shared_P_P_vec_given_Data_to_P_vec_P_Data() {
    crate::assert_ok!({
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test[perm P](given self, source: given Vec[given Data], data: P Vec[Data]) -> P Vec[P Data]
            where
                copy(P),
            {
                data.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn our_vec_given_Data_to_our_vec_our_Data() {
    crate::assert_ok!({
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(given self, source: given Vec[given Data], data: shared Vec[Data]) -> shared Vec[shared Data]
            {
                data.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn our_vec_our_Data_to_our_vec_given_Data() {
    crate::assert_ok!({
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(given self, source: given Vec[given Data], data: shared Vec[shared Data]) -> shared Vec[given Data]
            {
                data.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn our_vec_shared_Data_to_shared_vec_given_Data() {
    crate::assert_ok!({
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(given self, source: given Vec[given Data], data: given Vec[ref[source] Data]) -> ref[source] Vec[given Data]
            {
                data.share;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn ordering_matters() {
    crate::assert_err!({
        class Data { }
        class Pair[ty D] {
          first: D;
          second: D;
        }
        class Main {
            fn test[perm P, perm Q](given self, pair: P Pair[Q Data]) -> Q P Data {
                pair.first.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm, perm] (given self pair : ^perm0_0 Pair[^perm0_1 Data]) -> ^perm0_1 ^perm0_0 Data { pair . first . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { pair . first . give ; }, output: !perm_1 !perm_0 Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, pair: !perm_0 Pair[!perm_1 Data]}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { pair . first . give ; }, as_ty: !perm_1 !perm_0 Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, pair: !perm_0 Pair[!perm_1 Data]}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { pair . first . give ; }, as_ty: !perm_1 !perm_0 Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, pair: !perm_0 Pair[!perm_1 Data]}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: !perm_0 !perm_1 Data, b: !perm_1 !perm_0 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, pair: !perm_0 Pair[!perm_1 Data]}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_perms { perm_a: !perm_0 !perm_1, perm_b: !perm_1 !perm_0, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, pair: !perm_0 Pair[!perm_1 Data]}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                      judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Var(!perm_0), Var(!perm_1)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Var(!perm_1), Var(!perm_0)] }} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, pair: !perm_0 Pair[!perm_1 Data]}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                          judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Var(!perm_0), Var(!perm_1)] }, red_chain_b: RedChain { links: [Var(!perm_1), Var(!perm_0)] }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, pair: !perm_0 Pair[!perm_1 Data]}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                              judgment `prove_is_copy_owned { a: !perm_0, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, pair: !perm_0 Pair[!perm_1 Data]}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "prove" at (predicates.rs) failed because
                                                  judgment `prove_is_copy { a: !perm_0, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, pair: !perm_0 Pair[!perm_1 Data]}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "is" at (predicates.rs) failed because
                                                      judgment `prove_predicate { predicate: copy(!perm_0), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, pair: !perm_0 Pair[!perm_1 Data]}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "parameter" at (predicates.rs) failed because
                                                          pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn pair_a_to_pair_generic() {
    // Here we upcast from `mut[pair.a] T` to `mut[pair] T`.
    // This is fine.
    crate::assert_ok!({
        class Pair[ty T] {
          a: T;
          b: T;
        }

        class Main {
          fn main[ty T](given self, pair: given Pair[T]) {
            let p: mut[pair] T = pair.a.mut;
          }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn pair_a_to_pair_monomorphized() {
    // Here we upcast from `mut[pair.a] T` to `mut[pair] P T`.
    // This is fine -- we lose precision on precisely what is borrowed,
    // but we remember the `P` (vs `Q`).
    crate::assert_ok!({
      class Pair[ty A, ty B] {
        a: A;
        b: B;
      }

      class Data { }

      class Main {
        fn main[perm P, perm Q](given self, pair: given Pair[P Data, Q Data]) {
          let p: mut[pair] P Data = pair.a.mut;
        }
      }
      });
}

#[test]
#[allow(non_snake_case)]
fn pair_a_to_pair_bad() {
    // Here we upcast from `mut[pair.a] T` to `mut[pair] T`.
    // This is not allowed because it effectively 'forgets' the `P` perm.
    crate::assert_err!({
      class Pair[ty T] {
        a: T;
        b: T;
      }

      class Data { }

      class Main {
        fn main[perm P](given self, pair: given Pair[P Data]) {
          let p: mut[pair] Data = pair.a.mut;
        }
      }
      }, expect_test::expect![[r#"
          the rule "check_class" at (classes.rs) failed because
            judgment `check_method { decl: fn main [perm] (given self pair : given Pair[^perm0_0 Data]) -> () { let p : mut [pair] Data = pair . a . mut ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
              the rule "check_method" at (methods.rs) failed because
                judgment `check_body { body: { let p : mut [pair] Data = pair . a . mut ; }, output: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: given Pair[!perm_0 Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                  the rule "block" at (methods.rs) failed because
                    judgment `can_type_expr_as { expr: { let p : mut [pair] Data = pair . a . mut ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: given Pair[!perm_0 Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                      the rule "can_type_expr_as" at (expressions.rs) failed because
                        judgment `type_expr_as { expr: { let p : mut [pair] Data = pair . a . mut ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: given Pair[!perm_0 Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                          the rule "type_expr_as" at (expressions.rs) failed because
                            judgment `type_expr { expr: { let p : mut [pair] Data = pair . a . mut ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: given Pair[!perm_0 Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                              the rule "block" at (expressions.rs) failed because
                                judgment `type_block { block: { let p : mut [pair] Data = pair . a . mut ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: given Pair[!perm_0 Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                  the rule "place" at (blocks.rs) failed because
                                    judgment `type_statements_with_final_ty { statements: [let p : mut [pair] Data = pair . a . mut ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: given Pair[!perm_0 Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                      the rule "cons" at (statements.rs) failed because
                                        judgment `type_statement { statement: let p : mut [pair] Data = pair . a . mut ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: given Pair[!perm_0 Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                          the rule "let" at (statements.rs) failed because
                                            judgment `type_expr_as { expr: pair . a . mut, as_ty: mut [pair] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: given Pair[!perm_0 Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                              the rule "type_expr_as" at (expressions.rs) failed because
                                                judgment `sub { a: mut [pair . a] Data, b: mut [pair] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: given Pair[!perm_0 Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                  the rule "sub-classes" at (subtypes.rs) failed because
                                                    judgment `sub_perms { perm_a: mut [pair . a], perm_b: mut [pair], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: given Pair[!perm_0 Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                      the rule "sub_red_perms" at (redperms.rs) failed because
                                                        judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Mtd(pair . a), Var(!perm_0)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Mtd(pair)] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: given Pair[!perm_0 Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                          the rule "sub_red_perms" at (redperms.rs) failed because
                                                            judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtd(pair . a), Var(!perm_0)] }, red_chain_b: RedChain { links: [Mtd(pair)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: given Pair[!perm_0 Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                              the rule "(mut-dead::P) vs Q ~~> (P) vs Q" at (redperms.rs) failed because
                                                                judgment `prove_is_mut { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: given Pair[!perm_0 Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                  the rule "is-mut" at (predicates.rs) failed because
                                                                    judgment `prove_predicate { predicate: mut(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: given Pair[!perm_0 Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                      the rule "parameter" at (predicates.rs) failed because
                                                                        pattern `true` did not match value `false`
                                                              the rule "(mut::P) vs (mut::P)" at (redperms.rs) failed because
                                                                judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Var(!perm_0)] }, red_chain_b: RedChain { links: [] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: given Pair[!perm_0 Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                  the rule "(shared) vs (copy)" at (redperms.rs) failed because
                                                                    judgment `prove_is_copy_owned { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: given Pair[!perm_0 Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                      the rule "prove" at (predicates.rs) failed because
                                                                        judgment `prove_is_copy { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: given Pair[!perm_0 Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                          the rule "is" at (predicates.rs) failed because
                                                                            judgment `prove_predicate { predicate: copy(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: given Pair[!perm_0 Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                              the rule "parameter" at (predicates.rs) failed because
                                                                                pattern `true` did not match value `false`
                                                              the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                                                judgment `prove_is_copy_owned { a: mut [pair . a], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: given Pair[!perm_0 Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                  the rule "prove" at (predicates.rs) failed because
                                                                    judgment `prove_is_copy { a: mut [pair . a], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: given Pair[!perm_0 Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                      the rule "is" at (predicates.rs) failed because
                                                                        judgment `prove_predicate { predicate: copy(mut [pair . a]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, pair: given Pair[!perm_0 Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                          the rule "parameter" at (predicates.rs) failed because
                                                                            pattern `true` did not match value `false`"#]]);
}
