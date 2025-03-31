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
            copy(P),
            lent(P),
            ...;
        }
        
        class Guard[perm P, ty T]
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
              copy(S),
              lent(S),
              move(L),
              lent(L),
            {
                let guard: Guard[shared[lock], L Data] = lock.share.lock[shared[lock]]();
                let data: leased[guard] L Data = guard.lease.get[leased[guard]]();
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
              copy(S),
              lent(S),
              move(L),
              lent(L),
            {
                let guard: Guard[shared[lock], L Data] = lock.share.lock[shared[lock]]();
                let data: leased[guard] L Data = guard.lease.get[leased[guard]]();
                data.give;
            }
        }
        "
    )))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { field : Int ; } class Lock [ty] where relative(^ty0_0) { fn lock [perm] (^perm0_0 self) -> Guard[^perm0_0, ^ty1_0] where copy(^perm0_0), lent(^perm0_0) ...; } class Guard [perm, ty] where relative(^ty0_1) { fn get [perm] (^perm0_0 self) -> ^perm0_0 ^ty1_1 where lent(^perm0_0) ...; } class Main { fn escape [perm, perm] (my self lock : ^perm0_0 Lock[^perm0_1 Data]) -> ^perm0_1 Data where copy(^perm0_0), lent(^perm0_0), move(^perm0_1), lent(^perm0_1) { let guard : Guard[shared [lock], ^perm0_1 Data] = lock . share . lock [shared [lock]] () ; let data : leased [guard] ^perm0_1 Data = guard . lease . get [leased [guard]] () ; data . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `escape`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let guard : Guard[shared [lock], !perm_1 Data] = lock . share . lock [shared [lock]] () ; let data : leased [guard] !perm_1 Data = guard . lease . get [leased [guard]] () ; data . give ; }, as_ty: !perm_1 Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let guard : Guard[shared [lock], !perm_1 Data] = lock . share . lock [shared [lock]] () ; let data : leased [guard] !perm_1 Data = guard . lease . get [leased [guard]] () ; data . give ; }, as_ty: !perm_1 Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let guard : Guard[shared [lock], !perm_1 Data] = lock . share . lock [shared [lock]] () ; let data : leased [guard] !perm_1 Data = guard . lease . get [leased [guard]] () ; data . give ; }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let guard : Guard[shared [lock], !perm_1 Data] = lock . share . lock [shared [lock]] () ; let data : leased [guard] !perm_1 Data = guard . lease . get [leased [guard]] () ; data . give ; }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let guard : Guard[shared [lock], !perm_1 Data] = lock . share . lock [shared [lock]] () ;, let data : leased [guard] !perm_1 Data = guard . lease . get [leased [guard]] () ;, data . give ;], ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let data : leased [guard] !perm_1 Data = guard . lease . get [leased [guard]] () ;, data . give ;], ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, guard: Guard[shared [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let data : leased [guard] !perm_1 Data = guard . lease . get [leased [guard]] () ;, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, guard: Guard[shared [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr_as { expr: guard . lease . get [leased [guard]] (), as_ty: leased [guard] !perm_1 Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, guard: Guard[shared [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment had no applicable rules: `sub { a: leased [guard] !perm_1 Data, b: leased [guard] !perm_1 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, guard: Guard[shared [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }`"#]]);
}
