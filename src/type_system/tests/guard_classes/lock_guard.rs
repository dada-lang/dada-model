//! Tests demonstrating the lock guard pattern and how it interacts with various dada features.

use formality_core::test;

const LOCK_GUARD_PREAMBLE: &str = "
        class Data {
          field: Int;
        }
        
        class Lock[ty T]
        where
            relative(T),
        {
          fn lock[perm P](P self) -> Guard[P, T]
          where
            copy(P),
            ...;
        }
        
        guard class Guard[perm P, ty T]
        where
            relative(T),
        {
          fn get[perm S](S self) -> S T
          where
            ...;
        }
";

/// Demonstrate a lock being acquired and the data inside being updated.
#[test]
#[allow(non_snake_case)]
fn lock_guard_ok() {
    crate::assert_ok!(&format!(
        "{LOCK_GUARD_PREAMBLE}{suffix}",
        suffix = "
        class Main {
            fn main[perm S, perm L](given self, lock: S Lock[L Data]) -> ()
            where
              copy(S),
              mut(L),
            {
                let guard: Guard[ref[lock], L Data] = lock.ref.lock[ref[lock]]();
                let data: mut[guard] L Data = guard.mut.get[mut[guard]]();
                data.field = 2;
            }
        }
        "
    ));
}

/// Demonstrate a lock being acquired and an attempt to escape the data inside from the lock.
#[test]
#[allow(non_snake_case)]
fn lock_guard_cancellation() {
    crate::assert_err!(&format!(
        "{LOCK_GUARD_PREAMBLE}{suffix}",
        suffix = "
        class Main {
            fn escape[perm S, perm L](given self, lock: S Lock[L Data]) -> L Data
            where
              copy(S),
              mut(L),
            {
                let guard: Guard[ref[lock], L Data] = lock.ref.lock[ref[lock]]();
                let data: mut[guard] L Data = guard.mut.get[mut[guard]]();
                data.give;
            }
        }
        "
    ), expect_test::expect![[r#"
        the rule "check_class" at (classes.rs) failed because
          judgment `check_method { decl: fn escape [perm, perm] (given self lock : ^perm0_0 Lock[^perm0_1 Data]) -> ^perm0_1 Data where copy(^perm0_0), mut(^perm0_1) { let guard : Guard[ref [lock], ^perm0_1 Data] = lock . ref . lock [ref [lock]] () ; let data : mut [guard] ^perm0_1 Data = guard . mut . get [mut [guard]] () ; data . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
            the rule "check_method" at (methods.rs) failed because
              judgment `check_body { body: { let guard : Guard[ref [lock], !perm_1 Data] = lock . ref . lock [ref [lock]] () ; let data : mut [guard] !perm_1 Data = guard . mut . get [mut [guard]] () ; data . give ; }, output: !perm_1 Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                the rule "block" at (methods.rs) failed because
                  judgment `can_type_expr_as { expr: { let guard : Guard[ref [lock], !perm_1 Data] = lock . ref . lock [ref [lock]] () ; let data : mut [guard] !perm_1 Data = guard . mut . get [mut [guard]] () ; data . give ; }, as_ty: !perm_1 Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                    the rule "can_type_expr_as" at (expressions.rs) failed because
                      judgment `type_expr_as { expr: { let guard : Guard[ref [lock], !perm_1 Data] = lock . ref . lock [ref [lock]] () ; let data : mut [guard] !perm_1 Data = guard . mut . get [mut [guard]] () ; data . give ; }, as_ty: !perm_1 Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "type_expr_as" at (expressions.rs) failed because
                          judgment `sub { a: mut [guard] !perm_1 Data, b: !perm_1 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                            the rule "sub-classes" at (subtypes.rs) failed because
                              judgment `sub_perms { perm_a: mut [guard] !perm_1, perm_b: !perm_1, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                the rule "sub_red_perms" at (redperms.rs) failed because
                                  judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Mtd(guard), Var(!perm_1)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Var(!perm_1)] }} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                      judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtd(guard), Var(!perm_1)] }, red_chain_b: RedChain { links: [Var(!perm_1)] }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "(mut-dead::P) vs Q ~~> (P) vs Q" at (redperms.rs) failed because
                                          judgment `prove_is_shareable { a: Guard[ref [lock], !perm_1 Data], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "is" at (predicates.rs) failed because
                                              judgment `prove_predicate { predicate: share(Guard[ref [lock], !perm_1 Data]), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "parameter" at (predicates.rs) failed because
                                                  judgment `prove_class_predicate { kind: share, parameter: Guard[ref [lock], !perm_1 Data], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "class" at (predicates.rs) failed because
                                                      pattern `true` did not match value `false`
                                        the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                          judgment `prove_is_copy_owned { a: mut [guard], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "prove" at (predicates.rs) failed because
                                              judgment `prove_is_copy { a: mut [guard], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                the rule "is" at (predicates.rs) failed because
                                                  judgment `prove_predicate { predicate: copy(mut [guard]), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), mut(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                    the rule "parameter" at (predicates.rs) failed because
                                                      pattern `true` did not match value `false`"#]]);
}
