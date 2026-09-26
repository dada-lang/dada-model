//! ## Moves preserve dependencies
//!
//! Moving a value to a new place preserves dependencies on that value. Existing
//! shared borrows remain associated with the transferred value and continue to
//! restrict conflicting accesses at its new location. These restrictions follow
//! subsequent transfers too, and cease when the dependent borrows are no longer live.
//!
//! ### Candidate lemma: place relocation preserves typing
//!
//! For a supported ownership transfer from place `p` to a fresh place `q`,
//! consistently substitute `q` for the prefix `p` in dependent types and the
//! relevant typing context. Thus `p.field` becomes `q.field`, while unrelated
//! places are unchanged. The candidate preservation claim is that dependent
//! values remain well-typed, with corresponding access restrictions at `q`.
//!
//! ### Scope and assumptions
//!
//! This is a candidate formulation, not a proved theorem. It assumes a permitted
//! move of an initialized value and removal of access to the transferred source.
//! Liveness and dependent places must be interpreted in the updated context.
//! Assignment to an existing destination additionally requires that replacing
//! its previous value is permitted; freshness alone does not cover that case.
//!
//! The tests below check static dependency tracking for shared borrows, including
//! whole-value and field transfers. They do not establish that runtime mutable
//! reference pointers survive relocation, or cover every partially moved aggregate.
//!
//! ### Evidence
//!
//! The five tests check that a borrow remains usable after transfer, a dead borrow
//! releases restrictions, discarding a needed referent is rejected, a second
//! transfer retargets the dependency, and overwriting its final destination is
//! rejected while the borrow remains live. Error snapshots record the current
//! diagnostics; the property concerns acceptance and rejection for these reasons.

use formality_core::test;

/// Check that we can give something which is shared and then go on
/// using the shared thing.
#[test]
fn give_while_shared_then_use() {
    crate::assert_ok!({
        class Data {}

        class Foo {
            i: Data;
        }

        class Main {
            fn main(given self) -> () {
                let foo = new Foo(new Data());
                let s = foo.i.ref;
                let bar = foo.give; // rewrites type of `s` to `shared(bar) Foo`
                bar.i.ref;
                s.give;
                ();
            }
        }
    })
}

/// Check that we can give something which is shared and then go on
/// using the shared thing.
#[test]
fn give_while_shared_then_drop() {
    crate::assert_ok!({
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn main(given self) -> () {
                let foo = new Foo(new Data());
                let s = foo.i.ref;
                let bar = foo.give; // rewrites type of `s` to `shared(bar) Foo`
                bar.i.give;
                ();
            }
        }
    })
}

/// Check that if we give while shared we can't then move out of the new name.
#[test]
fn give_while_shared_then_move_while_shared() {
    crate::assert_err!({
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn main(given self) -> () {
                let foo = new Foo(new Data());
                let s = foo.i.ref;

                // rewrites type of `s` to `shared(bar.i) Int`
                let bar = foo.give;

                // now we get an error here..
                bar.i.give;

                // ...because `s` is used again
                s.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = @ fresh(0)
            shared_place = @ fresh(0)"#]])
}

/// Check that if we give while shared we can't then move out of the new name.
#[test]
fn give_while_shared_then_assign_while_shared() {
    crate::assert_ok!({
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn main(given self) -> () {
                let foo = new Foo(new Data());
                let s = foo.i.ref;

                // rewrites type of `s` to `shared(bar.i) Int`
                let bar = foo.give;

                // we can still assign `bar.i` to `d`...
                let d = new Data();
                d = bar.i.give;

                // ...even though `s` is used again;
                // the type of `s` becomes `shared(d)`
                s.give;
                ();
            }
        }
    })
}

/// Check that if we give while shared we can't then move out of the new name.
#[test]
fn give_while_shared_then_assign_while_shared_then_mutate_new_place() {
    crate::assert_err!({
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn main(given self) -> () {
                let foo = new Foo(new Data());
                let s = foo.i.ref;

                // rewrites type of `s` to `shared(bar.i) Int`
                let bar = foo.give;

                // we can still assign `bar.i` to `d`...
                let d = new Data();
                d = bar.i.give;

                // ...even though `s` is used again;
                // the type of `s` becomes `shared(d)`
                s.give;

                // but now we can't reassign `d`
                d = new Data();

                // when `s` is used again
                s.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = d
            shared_place = d"#]])
}
