//! Tests for subpermissions.
//!
//! Perm P is a *subpermission* of perm Q when `P T` is a subtype of `Q T` for all types `T`.

use formality_core::test;

#[test]
#[allow(non_snake_case)]
fn PermDataMy_is_subtype_of_PermDataMy() {
    crate::assert_ok!({
        class Data { }

        class PermData[perm P] {
            data: P Data;
        }

        class Main {
            fn test(given self, data: PermData[given]) {
                let m: PermData[given] = data.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn PermDataMy_not_subtype_of_PermDataOur() {
    crate::assert_err!({
        class Data { }

        class PermData[perm P] {
            data: P Data;
        }

        class Main {
            fn test(given self, data: PermData[given]) {
                let m: PermData[shared] = data.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self data : PermData[given]) -> () { let m : PermData[shared] = data . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let m : PermData[shared] = data . give ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let m : PermData[shared] = data . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let m : PermData[shared] = data . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let m : PermData[shared] = data . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let m : PermData[shared] = data . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let m : PermData[shared] = data . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statement { statement: let m : PermData[shared] = data . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "let" at (statements.rs) failed because
                                              judgment `type_expr_as { expr: data . give, as_ty: PermData[shared], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "type_expr_as" at (expressions.rs) failed because
                                                  judgment `sub { a: PermData[given], b: PermData[shared], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "sub-classes" at (subtypes.rs) failed because
                                                      judgment `sub_generic_parameter { perm_a: given, a: given, perm_b: given, b: shared, variances: [], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "covariant-copy" at (subtypes.rs) failed because
                                                          judgment `prove_is_copy { a: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "is" at (predicates.rs) failed because
                                                              judgment `prove_predicate { predicate: copy(given), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "parameter" at (predicates.rs) failed because
                                                                  pattern `true` did not match value `false`
                                                        the rule "covariant-owned" at (subtypes.rs) failed because
                                                          judgment `sub { a: given given, b: given shared, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "sub-perms" at (subtypes.rs) failed because
                                                              judgment `sub_perms { perm_a: given given, perm_b: given shared, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                                  judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Shared] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                                                      judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Shared] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "(given) vs (given)" at (redperms.rs) failed because
                                                                          judgment `prove_is_given { a: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "prove" at (predicates.rs) failed because
                                                                              judgment `prove_is_move { a: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "is-moved" at (predicates.rs) failed because
                                                                                  judgment `prove_predicate { predicate: move(shared), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "mut => move" at (predicates.rs) failed because
                                                                                      judgment `prove_is_mut { a: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "is-mut" at (predicates.rs) failed because
                                                                                          judgment `prove_predicate { predicate: mut(shared), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                                              pattern `true` did not match value `false`
                                                                                    the rule "parameter" at (predicates.rs) failed because
                                                                                      pattern `true` did not match value `false`
                                                        the rule "invariant" at (subtypes.rs) failed because
                                                          judgment `sub { a: given, b: shared, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "sub-perms" at (subtypes.rs) failed because
                                                              judgment `sub_perms { perm_a: given, perm_b: shared, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                                  judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Shared] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                                                      judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Shared] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "(given) vs (given)" at (redperms.rs) failed because
                                                                          judgment `prove_is_given { a: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "prove" at (predicates.rs) failed because
                                                                              judgment `prove_is_move { a: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "is-moved" at (predicates.rs) failed because
                                                                                  judgment `prove_predicate { predicate: move(shared), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "mut => move" at (predicates.rs) failed because
                                                                                      judgment `prove_is_mut { a: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "is-mut" at (predicates.rs) failed because
                                                                                          judgment `prove_predicate { predicate: mut(shared), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                                              pattern `true` did not match value `false`
                                                                                    the rule "parameter" at (predicates.rs) failed because
                                                                                      pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn PermDataMy_is_not_subtype_of_PermDataLeased() {
    crate::assert_err!({
        class Data { }

        class PermData[perm P] {
            data: P Data;
        }

        class Main {
            fn test(given self, data: PermData[given]) {
                let d = new Data();
                let m: PermData[mut[d]] = data.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self data : PermData[given]) -> () { let d = new Data () ; let m : PermData[mut [d]] = data . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let d = new Data () ; let m : PermData[mut [d]] = data . give ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let d = new Data () ; let m : PermData[mut [d]] = data . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let d = new Data () ; let m : PermData[mut [d]] = data . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let d = new Data () ; let m : PermData[mut [d]] = data . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let d = new Data () ; let m : PermData[mut [d]] = data . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let d = new Data () ;, let m : PermData[mut [d]] = data . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let m : PermData[mut [d]] = data . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statement { statement: let m : PermData[mut [d]] = data . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "let" at (statements.rs) failed because
                                                  judgment `type_expr_as { expr: data . give, as_ty: PermData[mut [d]], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "type_expr_as" at (expressions.rs) failed because
                                                      judgment `sub { a: PermData[given], b: PermData[mut [d]], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "sub-classes" at (subtypes.rs) failed because
                                                          judgment `sub_generic_parameter { perm_a: given, a: given, perm_b: given, b: mut [d], variances: [], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "covariant-copy" at (subtypes.rs) failed because
                                                              judgment `prove_is_copy { a: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "is" at (predicates.rs) failed because
                                                                  judgment `prove_predicate { predicate: copy(given), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "parameter" at (predicates.rs) failed because
                                                                      pattern `true` did not match value `false`
                                                            the rule "covariant-owned" at (subtypes.rs) failed because
                                                              judgment `sub { a: given given, b: given mut [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "sub-perms" at (subtypes.rs) failed because
                                                                  judgment `sub_perms { perm_a: given given, perm_b: given mut [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                                                      judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Mtd(d)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                                                          judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Mtd(d)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "(given) vs (given)" at (redperms.rs) failed because
                                                                              judgment `prove_is_given { a: mut [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "prove" at (predicates.rs) failed because
                                                                                  judgment `prove_is_owned { a: mut [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "is-owned" at (predicates.rs) failed because
                                                                                      judgment `prove_predicate { predicate: owned(mut [d]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "parameter" at (predicates.rs) failed because
                                                                                          pattern `true` did not match value `false`
                                                            the rule "invariant" at (subtypes.rs) failed because
                                                              judgment `sub { a: given, b: mut [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "sub-perms" at (subtypes.rs) failed because
                                                                  judgment `sub_perms { perm_a: given, perm_b: mut [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                                                      judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Mtd(d)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                                                          judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Mtd(d)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "(given) vs (given)" at (redperms.rs) failed because
                                                                              judgment `prove_is_given { a: mut [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "prove" at (predicates.rs) failed because
                                                                                  judgment `prove_is_owned { a: mut [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "is-owned" at (predicates.rs) failed because
                                                                                      judgment `prove_predicate { predicate: owned(mut [d]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "parameter" at (predicates.rs) failed because
                                                                                          pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn PermDataMy_is_not_subtype_of_PermDataShared() {
    crate::assert_err!({
        class Data { }

        class PermData[perm P] {
            data: P Data;
        }

        class Main {
            fn test(given self, data: PermData[given]) {
                let d = new Data();
                let m: PermData[ref[d]] = data.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self data : PermData[given]) -> () { let d = new Data () ; let m : PermData[ref [d]] = data . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let d = new Data () ; let m : PermData[ref [d]] = data . give ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let d = new Data () ; let m : PermData[ref [d]] = data . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let d = new Data () ; let m : PermData[ref [d]] = data . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let d = new Data () ; let m : PermData[ref [d]] = data . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let d = new Data () ; let m : PermData[ref [d]] = data . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let d = new Data () ;, let m : PermData[ref [d]] = data . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let m : PermData[ref [d]] = data . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statement { statement: let m : PermData[ref [d]] = data . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "let" at (statements.rs) failed because
                                                  judgment `type_expr_as { expr: data . give, as_ty: PermData[ref [d]], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "type_expr_as" at (expressions.rs) failed because
                                                      judgment `sub { a: PermData[given], b: PermData[ref [d]], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "sub-classes" at (subtypes.rs) failed because
                                                          judgment `sub_generic_parameter { perm_a: given, a: given, perm_b: given, b: ref [d], variances: [], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "covariant-copy" at (subtypes.rs) failed because
                                                              judgment `prove_is_copy { a: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "is" at (predicates.rs) failed because
                                                                  judgment `prove_predicate { predicate: copy(given), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "parameter" at (predicates.rs) failed because
                                                                      pattern `true` did not match value `false`
                                                            the rule "covariant-owned" at (subtypes.rs) failed because
                                                              judgment `sub { a: given given, b: given ref [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "sub-perms" at (subtypes.rs) failed because
                                                                  judgment `sub_perms { perm_a: given given, perm_b: given ref [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                                                      judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Rfd(d)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                                                          judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Rfd(d)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "(given) vs (given)" at (redperms.rs) failed because
                                                                              judgment `prove_is_given { a: ref [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "prove" at (predicates.rs) failed because
                                                                                  judgment `prove_is_move { a: ref [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "is-moved" at (predicates.rs) failed because
                                                                                      judgment `prove_predicate { predicate: move(ref [d]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "mut => move" at (predicates.rs) failed because
                                                                                          judgment `prove_is_mut { a: ref [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "is-mut" at (predicates.rs) failed because
                                                                                              judgment `prove_predicate { predicate: mut(ref [d]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                                the rule "parameter" at (predicates.rs) failed because
                                                                                                  pattern `true` did not match value `false`
                                                                                        the rule "parameter" at (predicates.rs) failed because
                                                                                          pattern `true` did not match value `false`
                                                            the rule "invariant" at (subtypes.rs) failed because
                                                              judgment `sub { a: given, b: ref [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "sub-perms" at (subtypes.rs) failed because
                                                                  judgment `sub_perms { perm_a: given, perm_b: ref [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                                                      judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Rfd(d)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                                                          judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Rfd(d)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "(given) vs (given)" at (redperms.rs) failed because
                                                                              judgment `prove_is_given { a: ref [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "prove" at (predicates.rs) failed because
                                                                                  judgment `prove_is_move { a: ref [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "is-moved" at (predicates.rs) failed because
                                                                                      judgment `prove_predicate { predicate: move(ref [d]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "mut => move" at (predicates.rs) failed because
                                                                                          judgment `prove_is_mut { a: ref [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "is-mut" at (predicates.rs) failed because
                                                                                              judgment `prove_predicate { predicate: mut(ref [d]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                                the rule "parameter" at (predicates.rs) failed because
                                                                                                  pattern `true` did not match value `false`
                                                                                        the rule "parameter" at (predicates.rs) failed because
                                                                                          pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn unsound_upgrade() {
    crate::assert_err!({
        class Data {
            fn mutate[perm P](P self)
            where
                mut(P),
            { }
        }

        class Query {
            data: shared Data;
        }

        class Main {
            fn test(given self, q1: Query, q2: Query) {
                let a: mut[q1.data] Data = q1.data.mut;
                let b: mut[q1] Data = a.give;
                b.mut.mutate[mut[q1]]();
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self q1 : Query, q2 : Query) -> () { let a : mut [q1 . data] Data = q1 . data . mut ; let b : mut [q1] Data = a . give ; b . mut . mutate [mut [q1]] () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let a : mut [q1 . data] Data = q1 . data . mut ; let b : mut [q1] Data = a . give ; b . mut . mutate [mut [q1]] () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let a : mut [q1 . data] Data = q1 . data . mut ; let b : mut [q1] Data = a . give ; b . mut . mutate [mut [q1]] () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let a : mut [q1 . data] Data = q1 . data . mut ; let b : mut [q1] Data = a . give ; b . mut . mutate [mut [q1]] () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let a : mut [q1 . data] Data = q1 . data . mut ; let b : mut [q1] Data = a . give ; b . mut . mutate [mut [q1]] () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let a : mut [q1 . data] Data = q1 . data . mut ; let b : mut [q1] Data = a . give ; b . mut . mutate [mut [q1]] () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let a : mut [q1 . data] Data = q1 . data . mut ;, let b : mut [q1] Data = a . give ;, b . mut . mutate [mut [q1]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let b : mut [q1] Data = a . give ;, b . mut . mutate [mut [q1]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statement { statement: let b : mut [q1] Data = a . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {b}, traversed: {} } }` failed at the following rule(s):
                                                the rule "let" at (statements.rs) failed because
                                                  judgment `type_expr_as { expr: a . give, as_ty: mut [q1] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "type_expr_as" at (expressions.rs) failed because
                                                      judgment `sub { a: mut [q1 . data] Data, b: mut [q1] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "sub-classes" at (subtypes.rs) failed because
                                                          judgment `sub_perms { perm_a: mut [q1 . data], perm_b: mut [q1], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                                              judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Shared] }, red_perm_b: RedPerm { chains: {RedChain { links: [Mtd(q1)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                                  judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Shared] }, red_chain_b: RedChain { links: [Mtd(q1)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "(shared) vs (copy)" at (redperms.rs) failed because
                                                                      judgment `prove_is_copy { a: mut [q1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "is" at (predicates.rs) failed because
                                                                          judgment `prove_predicate { predicate: copy(mut [q1]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                              pattern `true` did not match value `false`
                                                                    the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                                                      judgment `prove_is_copy { a: mut [q1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "is" at (predicates.rs) failed because
                                                                          judgment `prove_predicate { predicate: copy(mut [q1]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_exists() {
    crate::assert_ok!({
        class Query {
        }

        class Main {
            fn test(given self, q1: Query, q2: Query) {
                let a: ref[q1] Query = q1.ref;
                let b: ref[q2] Query = q2.ref;
                let c: ref[a] ref[q1] Query = a.ref;
                let d: ref[b] ref[q2] Query = b.ref;
                let x: ref[a, b] Query = c.give;
                let y: ref[a, b] Query = d.give;
            }
        }
        });
}
