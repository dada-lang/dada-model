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
    .assert_err(expect_test::expect!["()"]);
}
