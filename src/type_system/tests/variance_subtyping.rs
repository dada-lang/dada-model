use formality_core::test;

#[test]
#[allow(non_snake_case)]
fn Cell_T_our_Cell_Data_to_our_Cell_our_Data() {
    crate::assert_ok!({
        class Data {}
        class Cell[ty T]
        {
            f: T;
        }
        class Main {
            fn test(given self, d1: shared Cell[Data]) -> shared Cell[shared Data] {
                d1.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn Cell_atomic_T_our_Cell_Data_to_our_Cell_our_Data() {
    // Since T is atomic(T), we can't convert `shared Cell[Data]` to `shared Cell[shared Data]`.
    crate::assert_err!({
        class Data {}
        class Cell[ty T]
        where
            atomic(T),
        {
            atomic f: T;
        }
        class Main {
            fn test(given self, d1: shared Cell[Data]) -> shared Cell[shared Data] {
                d1.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self d1 : shared Cell[Data]) -> shared Cell[shared Data] { d1 . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { d1 . give ; }, output: shared Cell[shared Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { d1 . give ; }, as_ty: shared Cell[shared Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { d1 . give ; }, as_ty: shared Cell[shared Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: shared Cell[Data], b: shared Cell[shared Data], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_generic_parameter { perm_a: shared, a: Data, perm_b: shared, b: shared Data, variances: [atomic], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "invariant" at (subtypes.rs) failed because
                                      judgment `sub { a: Data, b: shared Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub-classes" at (subtypes.rs) failed because
                                          judgment `sub_perms { perm_a: given, perm_b: shared, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                              judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Shared] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                  judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Shared] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "(given) vs (given)" at (redperms.rs) failed because
                                                      judgment `prove_is_given { a: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "prove" at (predicates.rs) failed because
                                                          judgment `prove_is_move { a: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "is-moved" at (predicates.rs) failed because
                                                              judgment `prove_predicate { predicate: move(shared), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "mut => move" at (predicates.rs) failed because
                                                                  judgment `prove_is_mut { a: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "is-mut" at (predicates.rs) failed because
                                                                      judgment `prove_predicate { predicate: mut(shared), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "parameter" at (predicates.rs) failed because
                                                                          pattern `true` did not match value `false`
                                                                the rule "parameter" at (predicates.rs) failed because
                                                                  pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn Cell_rel_T_our_Cell_Data_to_our_Cell_our_Data() {
    // Since T is relative(T), we can't convert `shared Cell[Data]` to `shared Cell[shared Data]`.
    crate::assert_err!({
        class Data {}
        class Cell[ty T]
        where
            relative(T),
        {
        }
        class Main {
            fn test(given self, d1: shared Cell[Data]) -> shared Cell[shared Data] {
                d1.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self d1 : shared Cell[Data]) -> shared Cell[shared Data] { d1 . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { d1 . give ; }, output: shared Cell[shared Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { d1 . give ; }, as_ty: shared Cell[shared Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { d1 . give ; }, as_ty: shared Cell[shared Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `sub { a: shared Cell[Data], b: shared Cell[shared Data], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub-classes" at (subtypes.rs) failed because
                                  judgment `sub_generic_parameter { perm_a: shared, a: Data, perm_b: shared, b: shared Data, variances: [relative], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "invariant" at (subtypes.rs) failed because
                                      judgment `sub { a: Data, b: shared Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "sub-classes" at (subtypes.rs) failed because
                                          judgment `sub_perms { perm_a: given, perm_b: shared, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                              judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Shared] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                  judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Shared] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "(given) vs (given)" at (redperms.rs) failed because
                                                      judgment `prove_is_given { a: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "prove" at (predicates.rs) failed because
                                                          judgment `prove_is_move { a: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "is-moved" at (predicates.rs) failed because
                                                              judgment `prove_predicate { predicate: move(shared), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                the rule "mut => move" at (predicates.rs) failed because
                                                                  judgment `prove_is_mut { a: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "is-mut" at (predicates.rs) failed because
                                                                      judgment `prove_predicate { predicate: mut(shared), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "parameter" at (predicates.rs) failed because
                                                                          pattern `true` did not match value `false`
                                                                the rule "parameter" at (predicates.rs) failed because
                                                                  pattern `true` did not match value `false`"#]]);
}
