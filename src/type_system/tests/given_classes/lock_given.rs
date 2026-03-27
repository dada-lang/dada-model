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
        the rule "place" at (blocks.rs) failed because
          dangling borrow: chain `RedChain { links: [Mtd(guard), Var(!perm_1)] }` borrows through `guard` which is being popped (type not shareable or tail not mut-based)"#]]);
}

