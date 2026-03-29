//! Tests demonstrating the lock given pattern and how it interacts with various dada features.

use formality_core::test;

const LOCK_GUARD_PREAMBLE: &str = "
        class Data {
          field: Int;
        }
        
        class Lock[ty T]
        where
            T is relative,
        {
          fn lock[perm P](P self) -> Guard[P, T]
          where
            P is copy,
            ...;
        }
        
        given class Guard[perm P, ty T]
        where
            T is relative,
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
              S is copy,
              L is mut,
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
              S is copy,
              L is mut,
            {
                let guard: Guard[ref[lock], L Data] = lock.ref.lock[ref[lock]]();
                let data: mut[guard] L Data = guard.mut.get[mut[guard]]();
                data.give;
            }
        }
        "
    ), expect_test::expect![[r#"
        the rule "share class" at (predicates.rs) failed because
          pattern `true` did not match value `false`

        the rule "keep non-popped link" at (pop_normalize.rs) failed because
          condition evaluated to false: `!link_references_popped(&link, &popped_vars)`
            &link = Mtd(guard)
            &popped_vars = [data, guard]

        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: !perm_1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {!perm_0 is copy, !perm_1 is mut, !perm_0 is relative, !perm_1 is relative, !perm_0 is atomic, !perm_1 is atomic}, fresh: 0 } }

        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: given Main, data: mut [guard] !perm_1 Data, guard: Guard[ref [lock], !perm_1 Data], lock: !perm_0 Lock[!perm_1 Data]}, assumptions: {!perm_0 is copy, !perm_1 is mut, !perm_0 is relative, !perm_1 is relative, !perm_0 is atomic, !perm_1 is atomic}, fresh: 0 } }"#]]);
}

