//! Tests demonstrating the lock given pattern and how it interacts with various dada features.

use formality_core::test;

const LOCK_GUARD_PREAMBLE: &str = "
        struct Data {
          field: Int;
        }
        
        struct Lock[ty T]
        where
            T is relative,
        {
          fn lock[perm P](P self) -> Guard[P, T]
          where
            P is shared,
            ...;
        }
        
        class Guard[perm P, ty T]
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
        struct Main {
            fn main[perm S, perm L](given self, lock: S Lock[L Data]) -> ()
            where
              S is shared,
              L is mut,
            {
                let guard: Guard[shared[lock], L Data] = lock.share.lock[shared[lock]]();
                let data: ![guard] L Data = guard!.get[![guard]]();
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
    crate::assert_err!(
        &format!(
            "{LOCK_GUARD_PREAMBLE}{suffix}",
            suffix = "
        struct Main {
            fn escape[perm S, perm L](given self, lock: S Lock[L Data]) -> L Data
            where
              S is shared,
              L is mut,
            {
                let guard: Guard[shared[lock], L Data] = lock.share.lock[shared[lock]]();
                let data: ![guard] L Data = guard!.get[![guard]]();
                data^;
            }
        }
        "
        ),
        expect_test::expect![[r#"
            the rule "struct" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]
    );
}
