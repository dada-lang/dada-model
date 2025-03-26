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
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: leased [guard] !perm_1 Data, b: !perm_1 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: leased [guard] !perm_1 Data, guard: Guard[shared [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under { perm_a: my, a: leased [guard] !perm_1 Data, perm_b: my, b: !perm_1 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: leased [guard] !perm_1 Data, guard: Guard[shared [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_red_terms { red_term_a: RedTerm { red_perm: RedPerm { perms: [leased [guard], !perm_1] }, red_ty: NamedTy(Data) }, red_term_b: RedTerm { red_perm: RedPerm { perms: [!perm_1] }, red_ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: leased [guard] !perm_1 Data, guard: Guard[shared [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                   judgment `sub_red_perms { a: RedPerm { perms: [leased [guard], !perm_1] }, b: RedPerm { perms: [!perm_1] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: leased [guard] !perm_1 Data, guard: Guard[shared [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "leased-dead" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `sub_dead_leased { place_a: guard, perm_a: RedPerm { perms: [!perm_1] }, b: RedPerm { perms: [!perm_1] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: leased [guard] !perm_1 Data, guard: Guard[shared [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "sub_dead_leased" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `prove_is_lent { a: Guard[shared [lock], !perm_1 Data], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: leased [guard] !perm_1 Data, guard: Guard[shared [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: lent(Guard[shared [lock], !perm_1 Data]), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: leased [guard] !perm_1 Data, guard: Guard[shared [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                   condition evaluted to false: `is_true`
                                     the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `prove_is_owned { a: leased [guard] !perm_1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: leased [guard] !perm_1 Data, guard: Guard[shared [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `prove_predicate { predicate: owned(leased [guard] !perm_1), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: leased [guard] !perm_1 Data, guard: Guard[shared [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                               condition evaluted to false: `is_true`
                                     the rule "my-sub-owned" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `prove_is_owned { a: !perm_1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: leased [guard] !perm_1 Data, guard: Guard[shared [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `prove_predicate { predicate: owned(!perm_1), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: leased [guard] !perm_1 Data, guard: Guard[shared [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                               condition evaluted to false: `is_true`
                                     the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `prove_is_owned { a: leased [guard] !perm_1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: leased [guard] !perm_1 Data, guard: Guard[shared [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `prove_predicate { predicate: owned(leased [guard] !perm_1), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: leased [guard] !perm_1 Data, guard: Guard[shared [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {copy(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                               condition evaluted to false: `is_true`"#]]);
}
