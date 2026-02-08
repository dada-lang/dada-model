use formality_core::test;

#[test]
fn give_int_value_twice() {
    crate::assert_ok!("
                class Foo {
                    i: Int;
                }

                class Main {
                    fn main(given self, foo: given Foo) {
                        foo.i.move;
                        foo.i.move;
                        ();
                    }
                }
            ")
}

#[test]
fn give_point_value_twice() {
    crate::assert_ok!("
                our class Point {
                    x: Int;
                    y: Int;
                }

                class Main {
                    fn main(given self) {
                        let p: Point = new Point(22, 44);
                        let q: Point = p.move;
                        let r: Point = p.move;
                        ();
                    }
                }
            ")
}

#[test]
fn move_our_class_of_our_class_twice() {
    // `Pair[Elem]` is an `our` type because both `Pair` and `Elem` are declared as `our`.
    // Moving `p` twice is ok.
    crate::assert_ok!("
                our class Elem { }

                our class Pair[ty T] {
                    a: T;
                    b: T;
                }

                class Main {
                    fn main(given self) {
                        let p: Pair[Elem] = new Pair[Elem](new Elem(), new Elem());
                        let q = p.move;
                        let r = p.move;
                        ();
                    }
                }
            ");
}

#[test]
fn move_our_class_of_regular_class_twice() {
    // `Pair[Elem]` is not an `our` type even though `Pair` is declared as `our`
    // because `Elem` is not. So moving `p` twice yields an error.
    crate::assert_err!("
                class Elem { }

                our class Pair[ty T] {
                    a: T;
                    b: T;
                }

                class Main {
                    fn main(given self) {
                        let p: Pair[Elem] = new Pair[Elem](new Elem(), new Elem());
                        let q = p.move;
                        let r = p.move;
                        ();
                    }
                }
            ", expect_test::expect![[r#"
                the rule "parameter" at (predicates.rs) failed because
                  pattern `true` did not match value `false`

                the rule "move" at (expressions.rs) failed because
                  condition evaluted to false: `!live_after.is_live(&place)`
                    live_after = LivePlaces { accessed: {p}, traversed: {} }
                    &place = p"#]])
}

#[test]
fn mutate_field_of_our_class_applied_to_our() {
    // Because `Pair` is declared as an `our` type, its fields cannot be individually
    // mutated when it is used with a non-our type like `Elem`.
    crate::assert_err!("
                our class Elem { }

                our class Pair[ty T] {
                    a: T;
                    b: T;
                }

                class Main {
                    fn main(given self) {
                        let p: Pair[Elem] = new Pair[Elem](new Elem(), new Elem());
                        p.a = new Elem();
                        ();
                    }
                }
            ", expect_test::expect![[r#"
                the rule "parameter" at (predicates.rs) failed because
                  pattern `true` did not match value `false`

                the rule "parameter" at (predicates.rs) failed because
                  pattern `true` did not match value `false`"#]])
}

#[test]
fn mutate_field_of_our_class_applied_to_share() {
    // Even though `Pair` is declared as an `our` type, its fields can be individually
    // mutated when it is used with a non-our type like `Elem`.
    //
    // FIXME: Is this good? Unclear, but it seems consistent with the idea that an `our` class is
    // `our` iff its generics are `our`.
    crate::assert_ok!("
                class Elem { }

                our class Pair[ty T] {
                    a: T;
                    b: T;
                }

                class Main {
                    fn main(given self) {
                        let p: Pair[Elem] = new Pair[Elem](new Elem(), new Elem());
                        p.a = new Elem();
                        ();
                    }
                }
            ")
}
