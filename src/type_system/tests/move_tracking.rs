use formality_core::test;

/// Check that we can give something which is shared and then go on
/// using the shared thing.
#[test]
fn give_while_shared_then_use() {
    crate::assert_ok!("
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
    ")
}

/// Check that we can give something which is shared and then go on
/// using the shared thing.
#[test]
fn give_while_shared_then_drop() {
    crate::assert_ok!("
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
    ")
}

/// Check that if we give while shared we can't then move out of the new name.
#[test]
fn give_while_shared_then_move_while_shared() {
    crate::assert_err!("
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
    ", expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
            &accessed_place = @ fresh(0)
            &shared_place = @ fresh(0)"#]])
}

/// Check that if we give while shared we can't then move out of the new name.
#[test]
fn give_while_shared_then_assign_while_shared() {
    crate::assert_ok!("
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
    ")
}

/// Check that if we give while shared we can't then move out of the new name.
#[test]
fn give_while_shared_then_assign_while_shared_then_mutate_new_place() {
    crate::assert_err!("
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
    ", expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
            &accessed_place = d
            &shared_place = d"#]])
}
