//! Tests demonstrating the lock guard pattern and how it interacts with various dada features.

use crate::{dada_lang::term, type_system::check_program};
use formality_core::{test, test_util::ResultTestExt};

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
            shared(P),
            lent(P),
            ...;
        }
        
        guard class Guard[perm P, ty T]
        where
            relative(T),
        {
          fn get[perm S](S self) -> S T
          where
            lent(S),
            ...;
        }
";

/// Demonstrate a lock being acquired and the data inside being updated.
#[test]
#[allow(non_snake_case)]
fn lock_guard_ok() {
    check_program(&term(&format!(
        "{LOCK_GUARD_PREAMBLE}{suffix}",
        suffix = "
        class Main {
            fn main[perm S, perm L](my self, lock: S Lock[L Data]) -> ()
            where
              shared(S),
              lent(S),
              unique(L),
              lent(L),
            {
                let guard: Guard[ref[lock], L Data] = lock.ref.lock[ref[lock]]();
                let data: mut[guard] L Data = guard.mut.get[mut[guard]]();
                data.field = 2;
            }
        }
        "
    )))
    .assert_ok(expect_test::expect!["()"]);
}

/// Demonstrate a lock being acquired and an attempt to escape the data inside from the lock.
#[test]
#[allow(non_snake_case)]
fn lock_guard_cancellation() {
    check_program(&term(&format!(
        "{LOCK_GUARD_PREAMBLE}{suffix}",
        suffix = "
        class Main {
            fn escape[perm S, perm L](my self, lock: S Lock[L Data]) -> L Data
            where
              shared(S),
              lent(S),
              unique(L),
              lent(L),
            {
                let guard: Guard[ref[lock], L Data] = lock.ref.lock[ref[lock]]();
                let data: mut[guard] L Data = guard.mut.get[mut[guard]]();
                data.move;
            }
        }
        "
    )))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { field : Int ; } class Lock [ty] where relative(^ty0_0) { fn lock [perm] (^perm0_0 self) -> Guard[^perm0_0, ^ty1_0] where shared(^perm0_0), lent(^perm0_0) ...; } guard class Guard [perm, ty] where relative(^ty0_1) { fn get [perm] (^perm0_0 self) -> ^perm0_0 ^ty1_1 where lent(^perm0_0) ...; } class Main { fn escape [perm, perm] (my self lock : ^perm0_0 Lock[^perm0_1 Data]) -> ^perm0_1 Data where shared(^perm0_0), lent(^perm0_0), unique(^perm0_1), lent(^perm0_1) { let guard : Guard[ref [lock], ^perm0_1 Data] = lock . ref . lock [ref [lock]] () ; let data : mut [guard] ^perm0_1 Data = guard . mut . get [mut [guard]] () ; data . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `escape`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let guard : Guard[ref [lock], !perm_1 Data] = lock . ref . lock [ref [lock]] () ; let data : mut [guard] !perm_1 Data = guard . mut . get [mut [guard]] () ; data . move ; }, as_ty: !perm_1 Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let guard : Guard[ref [lock], !perm_1 Data] = lock . ref . lock [ref [lock]] () ; let data : mut [guard] !perm_1 Data = guard . mut . get [mut [guard]] () ; data . move ; }, as_ty: !perm_1 Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: mut [guard] !perm_1 Data, b: !perm_1 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                           judgment `sub_perms_both_ways { a: mut [guard] !perm_1, b: !perm_1, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `sub_red_perms { perm_a: mut [guard] !perm_1, perm_b: !perm_1, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub_red_perms" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Mtd(guard), Var(!perm_1)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Var(!perm_1)] }} }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub_red_perms" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtd(guard), Var(!perm_1)] }, red_chain_b: RedChain { links: [Var(!perm_1)] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "mut dead" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `prove_is_shareable { a: Guard[ref [lock], !perm_1 Data], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: share(Guard[ref [lock], !perm_1 Data]), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `prove_class_predicate { kind: share, parameter: Guard[ref [lock], !perm_1 Data], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "class" failed at step #0 (src/file.rs:LL:CC) because
                                                       pattern `true` did not match value `false`
                                         the rule "our vs shared" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `prove_is_our { a: mut [guard], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "prove" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_is_shared { a: mut [guard], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `prove_predicate { predicate: shared(mut [guard]), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                       pattern `true` did not match value `false`"#]]);
}
