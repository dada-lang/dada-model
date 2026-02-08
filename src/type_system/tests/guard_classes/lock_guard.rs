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
    check_program(&term(&format!(
        "{LOCK_GUARD_PREAMBLE}{suffix}",
        suffix = "
        class Main {
            fn main[perm S, perm L](my self, lock: S Lock[L Data]) -> ()
            where
              shared(S),
              leased(L),
            {
                let guard: Guard[ref[lock], L Data] = lock.ref.lock[ref[lock]]();
                let data: mut[guard] L Data = guard.mut.get[mut[guard]]();
                data.field = 2;
            }
        }
        "
    )))
    .assert_ok();
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
              leased(L),
            {
                let guard: Guard[ref[lock], L Data] = lock.ref.lock[ref[lock]]();
                let data: mut[guard] L Data = guard.mut.get[mut[guard]]();
                data.move;
            }
        }
        "
    )))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { field : Int ; } class Lock [ty] where relative(^ty0_0) { fn lock [perm] (^perm0_0 self) -> Guard[^perm0_0, ^ty1_0] where shared(^perm0_0) ...; } guard class Guard [perm, ty] where relative(^ty0_1) { fn get [perm] (^perm0_0 self) -> ^perm0_0 ^ty1_1 ...; } class Main { fn escape [perm, perm] (my self lock : ^perm0_0 Lock[^perm0_1 Data]) -> ^perm0_1 Data where shared(^perm0_0), leased(^perm0_1) { let guard : Guard[ref [lock], ^perm0_1 Data] = lock . ref . lock [ref [lock]] () ; let data : mut [guard] ^perm0_1 Data = guard . mut . get [mut [guard]] () ; data . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `escape`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let guard : Guard[ref [lock], !perm_1 Data] = lock . ref . lock [ref [lock]] () ; let data : mut [guard] !perm_1 Data = guard . mut . get [mut [guard]] () ; data . move ; }, as_ty: !perm_1 Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), leased(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" at (expressions.rs) failed because
                   judgment `type_expr_as { expr: { let guard : Guard[ref [lock], !perm_1 Data] = lock . ref . lock [ref [lock]] () ; let data : mut [guard] !perm_1 Data = guard . mut . get [mut [guard]] () ; data . move ; }, as_ty: !perm_1 Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), leased(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" at (expressions.rs) failed because
                       judgment `sub { a: mut [guard] !perm_1 Data, b: !perm_1 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), leased(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub-classes" at (subtypes.rs) failed because
                           judgment `sub_perms { perm_a: mut [guard] !perm_1, perm_b: !perm_1, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), leased(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub_red_perms" at (redperms.rs) failed because
                               judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Mtd(guard), Var(!perm_1)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Var(!perm_1)] }} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), leased(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub_red_perms" at (redperms.rs) failed because
                                   judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtd(guard), Var(!perm_1)] }, red_chain_b: RedChain { links: [Var(!perm_1)] }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), leased(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "(mut-dead::P) vs Q ~~> (P) vs Q" at (redperms.rs) failed because
                                       judgment `prove_is_shareable { a: Guard[ref [lock], !perm_1 Data], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), leased(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "is" at (predicates.rs) failed because
                                           judgment `prove_predicate { predicate: share(Guard[ref [lock], !perm_1 Data]), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), leased(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "parameter" at (predicates.rs) failed because
                                               judgment `prove_class_predicate { kind: share, parameter: Guard[ref [lock], !perm_1 Data], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), leased(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "class" at (predicates.rs) failed because
                                                   pattern `true` did not match value `false`
                                     the rule "(our::P) vs (shared::P)" at (redperms.rs) failed because
                                       judgment `prove_is_our { a: mut [guard], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), leased(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "prove" at (predicates.rs) failed because
                                           judgment `prove_is_shared { a: mut [guard], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), leased(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "is" at (predicates.rs) failed because
                                               judgment `prove_predicate { predicate: shared(mut [guard]), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {shared(!perm_0), leased(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "parameter" at (predicates.rs) failed because
                                                   pattern `true` did not match value `false`"#]]);
}
