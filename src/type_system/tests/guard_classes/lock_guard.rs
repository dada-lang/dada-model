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
        the rule "class" at (predicates.rs) failed because
          pattern `true` did not match value `false`

        the rule "parameter" at (predicates.rs) failed because
          pattern `true` did not match value `false`"#]]);
}
