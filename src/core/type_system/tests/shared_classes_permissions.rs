use formality_core::test;

#[test]
fn give_int_value_twice() {
    crate::assert_ok!({
        class Foo {
            i: Int;
        }

        class Main {
            fn main(^ self, foo: ^ Foo) {
                foo.i^;
                foo.i^;
                ();
            }
        }
    })
}

#[test]
fn give_point_value_twice() {
    crate::assert_ok!({
        shared class Point {
            x: Int;
            y: Int;
        }

        class Main {
            fn main(^ self) {
                let p: Point = new Point(22, 44);
                let q: Point = p^;
                let r: Point = p^;
                ();
            }
        }
    })
}

#[test]
fn move_our_class_of_our_class_twice() {
    // `Pair[Elem]` is an `shared` type because both `Pair` and `Elem` are declared as `shared`.
    // Moving `p` twice is ok.
    crate::assert_ok!({
        shared class Elem { }

        shared class Pair[ty T] {
            a: T;
            b: T;
        }

        class Main {
            fn main(^ self) {
                let p: Pair[Elem] = new Pair[Elem](new Elem(), new Elem());
                let q = p^;
                let r = p^;
                ();
            }
        }
    });
}

#[test]
fn move_our_class_of_regular_class_twice() {
    // `Pair[Elem]` is not an `shared` type even though `Pair` is declared as `shared`
    // because `Elem` is not. So moving `p` twice yields an error.
    crate::assert_err!({
                class Elem { }

                shared class Pair[ty T] {
                    a: T;
                    b: T;
                }

                class Main {
                    fn main(^ self) {
                        let p: Pair[Elem] = new Pair[Elem](new Elem(), new Elem());
                        let q = p^;
                        let r = p^;
                        ();
                    }
                }
            }, expect_test::expect![[r#"
                the rule "give" at (expressions.rs) failed because
                  condition evaluted to false: `!live_after.is_live(place)`
                    live_after = LivePlaces { accessed: {p}, traversed: {} }
                    place = p"#]])
}

#[test]
fn mutate_field_of_our_class_applied_to_our() {
    // Because `Pair` is declared as an `shared` type, its fields cannot be individually
    // mutated when it is used with a non-shared type like `Elem`.
    crate::assert_err!({
                shared class Elem { }

                shared class Pair[ty T] {
                    a: T;
                    b: T;
                }

                class Main {
                    fn main(^ self) {
                        let p: Pair[Elem] = new Pair[Elem](new Elem(), new Elem());
                        p.a = new Elem();
                        ();
                    }
                }
            }, expect_test::expect![[r#"
                the rule "class move" at (predicates.rs) failed because
                  pattern `false` did not match value `true`

                the rule "class move" at (predicates.rs) failed because
                  pattern `false` did not match value `true`

                the rule "shared-class move" at (predicates.rs) failed because
                  expression evaluated to an empty collection: `parameters`"#]])
}

#[test]
fn mutate_field_of_our_class_applied_to_share() {
    // Even though `Pair` is declared as an `shared` type, its fields can be individually
    // mutated when it is used with a non-shared type like `Elem`.
    //
    // FIXME: Is this good? Unclear, but it seems consistent with the idea that an `shared` class is
    // `shared` iff its generics are `shared`.
    crate::assert_ok!({
        class Elem { }

        shared class Pair[ty T] {
            a: T;
            b: T;
        }

        class Main {
            fn main(^ self) {
                let p: Pair[Elem] = new Pair[Elem](new Elem(), new Elem());
                p.a = new Elem();
                ();
            }
        }
    })
}
