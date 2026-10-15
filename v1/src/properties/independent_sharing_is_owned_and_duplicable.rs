//! # Independent sharing is owned and duplicable
//!
//! `shared` and `shared[]` denote the same permission: a shared value with no
//! origin dependency. Such a permission satisfies both `shared` and `owned`, and
//! does not satisfy the exclusive/unique predicate. These complete programs test
//! the empty-origin spelling through surface lowering and generic calls. Bare
//! places and explicit `.share` retain their origin; giving then sharing creates
//! independent shared ownership.

#[test]
fn empty_origins_are_owned_and_duplicable() {
    crate::assert_ok!(
        r#"
        struct Data {}
        struct Main {
            fn accept[perm P](given self, x: P Data) where P is shared, P is owned {
                ();
            }
            fn test(given self) {
                let x = new Data().share;
                x→;
                self→.accept[shared[]](x→);
            }
        }
    "#
    );
}

#[test]
fn empty_origins_do_not_satisfy_exclusivity() {
    crate::assert_err!(r#"
        struct Data {}
        struct Main {
            fn accept[perm P](given self, x: P Data) where P is unique { (); }
            fn test(given self) {
                self→.accept[shared[]](new Data().share);
            }
        }
    "#, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn accept [perm] (given self x : ^perm0_0 Data) → () where ^perm0_0 is unique { () ; } fn test (given self) → () { self → . accept [shared] (new Data () . share) ; } } }`"]);
}

#[test]
fn bare_and_explicit_place_shares_keep_the_origin() {
    crate::assert_ok!(
        r#"
        struct Data { value: Int; }
        struct Main {
            fn test(given self) {
                let source = new Data(22);
                let bare: shared[source] Data = source;
                let explicit: shared[source] Data = source.share;
                bare.value;
                explicit.value;
                source→;
                ();
            }
        }
    "#
    );
}

#[test]
fn giving_then_sharing_produces_independent_ownership() {
    crate::assert_ok!(
        r#"
        struct Data {}
        struct Main {
            fn accept[perm P](given self, x: P Data) where P is shared, P is owned { (); }
            fn test(given self) {
                let source = new Data();
                let value: shared[] Data = source→.share;
                self→.accept[shared[]](value→);
            }
        }
    "#
    );
}
