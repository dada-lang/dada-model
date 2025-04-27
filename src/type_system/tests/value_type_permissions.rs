use formality_core::test;
use formality_core::test_util::ResultTestExt;

use crate::{dada_lang::term, type_system::check_program};

#[test]
fn give_int_value_twice() {
    check_program(&term(
        "
                class Foo {
                    i: Int;
                }

                class Main {
                    fn main(my self, foo: my Foo) {
                        foo.i.move;
                        foo.i.move;
                        ();
                    }
                }
            ",
    ))
    .assert_ok(expect_test::expect![["()"]])
}

#[test]
fn give_point_value_twice() {
    check_program(&term(
        "
                our class Point {
                    x: Int;
                    y: Int;
                }

                class Main {
                    fn main(my self) {
                        let p: Point = new Point(22, 44);
                        let q: Point = p.move;
                        let r: Point = p.move;
                        ();
                    }
                }
            ",
    ))
    .assert_ok(expect_test::expect![["()"]])
}

#[test]
fn move_our_class_of_our_class_twice() {
    // `Pair[Elem]` is an `our` type because both `Pair` and `Elem` are declared as `our`.
    // Moving `p` twice is ok.
    check_program(&term(
        "
                our class Elem { }

                our class Pair[ty T] {
                    a: T;
                    b: T;
                }

                class Main {
                    fn main(my self) {
                        let p: Pair[Elem] = new Pair[Elem](new Elem(), new Elem());
                        let q = p.move;
                        let r = p.move;
                        ();
                    }
                }
            ",
    ))
    .assert_ok(expect_test::expect![[r#"()"#]]);
}

#[test]
fn move_our_class_of_regular_class_twice() {
    // `Pair[Elem]` is not an `our` type even though `Pair` is declared as `our`
    // because `Elem` is not. So moving `p` twice yields an error.
    check_program(&term(
        "
                class Elem { }

                our class Pair[ty T] {
                    a: T;
                    b: T;
                }

                class Main {
                    fn main(my self) {
                        let p: Pair[Elem] = new Pair[Elem](new Elem(), new Elem());
                        let q = p.move;
                        let r = p.move;
                        ();
                    }
                }
            ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Elem { } our class Pair [ty] { a : ^ty0_0 ; b : ^ty0_0 ; } class Main { fn main (my self) -> () { let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ; let q = p . move ; let r = p . move ; () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `main`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ; let q = p . move ; let r = p . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ; let q = p . move ; let r = p . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ; let q = p . move ; let r = p . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ; let q = p . move ; let r = p . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ;, let q = p . move ;, let r = p . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let q = p . move ;, let r = p . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Pair[Elem]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let q = p . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Pair[Elem]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr { expr: p . move, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Pair[Elem]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                             the rule "move place" failed at step #2 (src/file.rs:LL:CC) because
                                               judgment `move_place { place: p, ty: Pair[Elem], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Pair[Elem]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "copy" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `prove_is_shared { a: Pair[Elem], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Pair[Elem]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_predicate { predicate: shared(Pair[Elem]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Pair[Elem]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                           pattern `true` did not match value `false`
                                                 the rule "move" failed at step #0 (src/file.rs:LL:CC) because
                                                   condition evaluted to false: `!live_after.is_live(&place)`
                                                     live_after = LivePlaces { accessed: {p}, traversed: {} }
                                                     &place = p"#]])
}

#[test]
fn mutate_field_of_our_class_applied_to_our() {
    // Because `Pair` is declared as an `our` type, its fields cannot be individually
    // mutated when it is used with a non-our type like `Elem`.
    check_program(&term(
        "
                our class Elem { }

                our class Pair[ty T] {
                    a: T;
                    b: T;
                }

                class Main {
                    fn main(my self) {
                        let p: Pair[Elem] = new Pair[Elem](new Elem(), new Elem());
                        p.a = new Elem();
                        ();
                    }
                }
            ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `our class Elem { } our class Pair [ty] { a : ^ty0_0 ; b : ^ty0_0 ; } class Main { fn main (my self) -> () { let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ; p . a = new Elem () ; () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `main`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ; p . a = new Elem () ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ; p . a = new Elem () ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ; p . a = new Elem () ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ; p . a = new Elem () ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let p : Pair[Elem] = new Pair [Elem] (new Elem (), new Elem ()) ;, p . a = new Elem () ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [p . a = new Elem () ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Pair[Elem]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: p . a = new Elem () ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Pair[Elem]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "reassign" failed at step #3 (src/file.rs:LL:CC) because
                                           judgment `prove_is_unique { a: Pair[Elem], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Elem, p: Pair[Elem]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                             the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: unique(Pair[Elem]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Elem, p: Pair[Elem]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                   pattern `true` did not match value `false`"#]])
}

#[test]
fn mutate_field_of_our_class_applied_to_share() {
    // Even though `Pair` is declared as an `our` type, its fields can be individually
    // mutated when it is used with a non-our type like `Elem`.
    //
    // FIXME: Is this good? Unclear, but it seems consistent with the idea that an `our` class is
    // `our` iff its generics are `our`.
    check_program(&term(
        "
                class Elem { }

                our class Pair[ty T] {
                    a: T;
                    b: T;
                }

                class Main {
                    fn main(my self) {
                        let p: Pair[Elem] = new Pair[Elem](new Elem(), new Elem());
                        p.a = new Elem();
                        ();
                    }
                }
            ",
    ))
    .assert_ok(expect_test::expect!["()"])
}
