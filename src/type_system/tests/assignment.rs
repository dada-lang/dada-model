use formality_core::test;

/// Pair is leased from P, but when you assign to its fields,
/// you must meet the full type as if it were owned (i.e., here, we need
/// to assign a `given` Data).
#[test]
fn assign_leased_to_field_of_lease_that_is_typed_as_given() {
    crate::assert_err!({
        class Data { }
        class Pair { d1: Data; d2: Data; }
        class Main {
            fn test[perm P](given self, pair: P Pair, data: P Data) -> ()
            where
                mut(P),
            {
                pair.d1 = data.give;
                ();
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self pair : ^perm0_0 Pair, data : ^perm0_0 Data) -> () where mut(^perm0_0) { pair . d1 = data . give ; () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { pair . d1 = data . give ; () ; }, output: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { pair . d1 = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { pair . d1 = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { pair . d1 = data . give ; () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { pair . d1 = data . give ; () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [pair . d1 = data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statement { statement: pair . d1 = data . give ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "reassign" at (statements.rs) failed because
                                              judgment `type_expr_as { expr: data . give, as_ty: Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {pair} } }` failed at the following rule(s):
                                                the rule "type_expr_as" at (expressions.rs) failed because
                                                  judgment `sub { a: !perm_0 Data, b: Data, live_after: LivePlaces { accessed: {}, traversed: {pair} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "sub-classes" at (subtypes.rs) failed because
                                                      judgment `sub_perms { perm_a: !perm_0, perm_b: given, live_after: LivePlaces { accessed: {}, traversed: {pair} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                                          judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Var(!perm_0)] }, red_perm_b: RedPerm { chains: {RedChain { links: [] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                                              judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Var(!perm_0)] }, red_chain_b: RedChain { links: [] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "(shared) vs (copy)" at (redperms.rs) failed because
                                                                  judgment `prove_is_copy_owned { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "prove" at (predicates.rs) failed because
                                                                      judgment `prove_is_copy { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "is" at (predicates.rs) failed because
                                                                          judgment `prove_predicate { predicate: copy(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                              pattern `true` did not match value `false`"#]]);
}

/// Pair is leased from P, but when you assign to its fields,
/// you must meet the full type as if it were owned (i.e., here, we need
/// to assign a `given` Data).
#[test]
fn assign_owned_to_field_of_lease_that_is_typed_as_given() {
    crate::assert_ok!({
        class Data { }
        class Pair { d1: Data; d2: Data; }
        class Main {
            fn test[perm P](given self, pair: P Pair, data: given Data) -> ()
            where
                mut(P),
            {
                pair.d1 = data.give;
                ();
            }
        }
        });
}

/// Test that field is not assignable when using a perm var that is not shared.
#[test]
#[allow(non_snake_case)]
fn forall_shared_P_assign_to_field_of_P_pair() {
    crate::assert_err!({
        class Data { }
        class Pair { d1: Data; d2: Data; }
        class Main {
            fn test[perm P](given self, pair: P Pair, data: given Data) -> ()
            where
                copy(P),
            {
                pair.d1 = data.give;
                ();
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self pair : ^perm0_0 Pair, data : given Data) -> () where copy(^perm0_0) { pair . d1 = data . give ; () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { pair . d1 = data . give ; () ; }, output: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: given Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { pair . d1 = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: given Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { pair . d1 = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: given Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { pair . d1 = data . give ; () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: given Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { pair . d1 = data . give ; () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: given Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [pair . d1 = data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: given Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statement { statement: pair . d1 = data . give ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: given Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "reassign" at (statements.rs) failed because
                                              judgment `prove_is_move { a: !perm_0 Pair, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, @ fresh(0): Data, data: given Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                                the rule "is-moved" at (predicates.rs) failed because
                                                  judgment `prove_predicate { predicate: move(!perm_0 Pair), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, @ fresh(0): Data, data: given Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                                    the rule "mut => move" at (predicates.rs) failed because
                                                      judgment `prove_is_mut { a: !perm_0 Pair, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, @ fresh(0): Data, data: given Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                                        the rule "is-mut" at (predicates.rs) failed because
                                                          judgment `prove_predicate { predicate: mut(!perm_0 Pair), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, @ fresh(0): Data, data: given Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                                            the rule "parameter" at (predicates.rs) failed because
                                                              pattern `true` did not match value `false`
                                                    the rule "parameter" at (predicates.rs) failed because
                                                      pattern `true` did not match value `false`"#]]);
}

/// Test that field is not assignable when using a perm var that is not shared.
#[test]
#[allow(non_snake_case)]
fn forall_P_assign_to_field_of_P_pair() {
    crate::assert_err!({
        class Data { }
        class Pair { d1: Data; d2: Data; }
        class Main {
            fn test[perm P](given self, pair: P Pair, data: given Data) -> () {
                pair.d1 = data.give;
                ();
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self pair : ^perm0_0 Pair, data : given Data) -> () { pair . d1 = data . give ; () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { pair . d1 = data . give ; () ; }, output: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: given Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { pair . d1 = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: given Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { pair . d1 = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: given Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { pair . d1 = data . give ; () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: given Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { pair . d1 = data . give ; () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: given Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [pair . d1 = data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: given Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statement { statement: pair . d1 = data . give ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: given Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "reassign" at (statements.rs) failed because
                                              judgment `prove_is_move { a: !perm_0 Pair, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, @ fresh(0): Data, data: given Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                                the rule "is-moved" at (predicates.rs) failed because
                                                  judgment `prove_predicate { predicate: move(!perm_0 Pair), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, @ fresh(0): Data, data: given Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                                    the rule "mut => move" at (predicates.rs) failed because
                                                      judgment `prove_is_mut { a: !perm_0 Pair, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, @ fresh(0): Data, data: given Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                                        the rule "is-mut" at (predicates.rs) failed because
                                                          judgment `prove_predicate { predicate: mut(!perm_0 Pair), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, @ fresh(0): Data, data: given Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                                            the rule "parameter" at (predicates.rs) failed because
                                                              pattern `true` did not match value `false`
                                                    the rule "parameter" at (predicates.rs) failed because
                                                      pattern `true` did not match value `false`"#]]);
}
