//! # Independent sharing is owned and duplicable
//!
//! `shared` and `shared[]` denote the same permission: a shared value with no
//! origin dependency. Such a permission satisfies both `shared` and `owned`, and
//! does not satisfy the exclusive/move predicate. These complete programs test
//! the empty-origin spelling through surface lowering and generic calls.

#[test]
fn empty_origins_are_owned_and_duplicable() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn accept[perm P](^self, x: P Data) where P is shared, P is owned {
                ();
            }
            fn test(^self) {
                let x = new Data().share;
                x.give;
                self.give.accept[shared[]](x.give);
            }
        }
    });
}

#[test]
fn empty_origins_do_not_satisfy_exclusivity() {
    crate::assert_err!({
        class Data {}
        class Main {
            fn accept[perm P](^self, x: P Data) where P is move { (); }
            fn test(^self) {
                self.give.accept[shared[]](new Data().share);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { } class Main { fn accept [perm] (^ self x : ^perm0_0 Data) -> () where ^perm0_0 is move { () ; } fn test (^ self) -> () { self . give . accept [shared] (new Data () . share) ; } } }`"]);
}
