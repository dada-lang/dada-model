use formality_core::test;

#[test]
#[allow(non_snake_case)]
fn pair_given_Data_given_Data_to_pair_given_Data_given_Data() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self, d1: (given Data, given Data)) -> (given Data, given Data) {
                d1.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn pair_our_Data_our_Data_to_pair_given_Data_given_Data() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self, d1: (shared Data, shared Data)) -> (given Data, given Data) {
                d1.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self d1 : (shared Data, shared Data)) -> (given Data, given Data) { d1 . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { d1 . give ; }, output: (given Data, given Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { d1 . give ; }, as_ty: (given Data, given Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { d1 . give ; }, as_ty: (given Data, given Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: (shared Data, shared Data), b: (given Data, given Data), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_generic_parameter { perm_a: given, a: shared Data, perm_b: given, b: given Data, variances: [], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "covariant-copy" at (subtypes.rs) failed because
                                      judgment `prove_is_copy { a: given, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "is" at (predicates.rs) failed because
                                          judgment `prove_predicate { predicate: copy(given), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "parameter" at (predicates.rs) failed because
                                              pattern `true` did not match value `false`
                                    the rule "covariant-owned" at (subtypes.rs) failed because
                                      judgment `sub { a: given shared Data, b: given given Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub-classes" at (subtypes.rs) failed because
                                          judgment `sub_perms { perm_a: given shared, perm_b: given, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                              judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Shared] }, red_perm_b: RedPerm { chains: {RedChain { links: [] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                  judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Shared] }, red_chain_b: RedChain { links: [] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "(shared) vs (copy)" at (redperms.rs) failed because
                                                      judgment `prove_is_copy { a: given, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "is" at (predicates.rs) failed because
                                                          judgment `prove_predicate { predicate: copy(given), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "parameter" at (predicates.rs) failed because
                                                              pattern `true` did not match value `false`
                                    the rule "invariant" at (subtypes.rs) failed because
                                      judgment `sub { a: shared Data, b: given Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub-classes" at (subtypes.rs) failed because
                                          judgment `sub_perms { perm_a: shared, perm_b: given, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                              judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Shared] }, red_perm_b: RedPerm { chains: {RedChain { links: [] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                  judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Shared] }, red_chain_b: RedChain { links: [] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "(shared) vs (copy)" at (redperms.rs) failed because
                                                      judgment `prove_is_copy { a: given, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "is" at (predicates.rs) failed because
                                                          judgment `prove_predicate { predicate: copy(given), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "parameter" at (predicates.rs) failed because
                                                              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn our_pair_Data_Data_to_pair_Data_Data() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self, d1: shared (Data, Data)) -> (Data, Data) {
                d1.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self d1 : shared (Data, Data)) -> (Data, Data) { d1 . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { d1 . give ; }, output: (Data, Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: shared (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { d1 . give ; }, as_ty: (Data, Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: shared (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { d1 . give ; }, as_ty: (Data, Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: shared (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: shared (Data, Data), b: (Data, Data), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: shared (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_perms { perm_a: shared, perm_b: given, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: shared (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                      judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Shared] }, red_perm_b: RedPerm { chains: {RedChain { links: [] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: shared (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                          judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Shared] }, red_chain_b: RedChain { links: [] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: shared (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "(shared) vs (copy)" at (redperms.rs) failed because
                                              judgment `prove_is_copy { a: given, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: shared (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "is" at (predicates.rs) failed because
                                                  judgment `prove_predicate { predicate: copy(given), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: shared (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "parameter" at (predicates.rs) failed because
                                                      pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn our_pair_Data_Data_to_given_pair_Data_Data() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self, d1: shared (Data, Data)) -> given (Data, Data) {
                d1.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self d1 : shared (Data, Data)) -> given (Data, Data) { d1 . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { d1 . give ; }, output: given (Data, Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: shared (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { d1 . give ; }, as_ty: given (Data, Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: shared (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { d1 . give ; }, as_ty: given (Data, Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: shared (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: shared (Data, Data), b: given (Data, Data), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: shared (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_perms { perm_a: shared, perm_b: given, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: shared (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                      judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Shared] }, red_perm_b: RedPerm { chains: {RedChain { links: [] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: shared (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                          judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Shared] }, red_chain_b: RedChain { links: [] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: shared (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "(shared) vs (copy)" at (redperms.rs) failed because
                                              judgment `prove_is_copy { a: given, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: shared (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "is" at (predicates.rs) failed because
                                                  judgment `prove_predicate { predicate: copy(given), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: shared (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "parameter" at (predicates.rs) failed because
                                                      pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn my_pair_Data_Data_share_to_our_pair_Data_Data() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self, d1: given (Data, Data)) -> shared (Data, Data) {
                d1.share;
            }
        }
        });
}
