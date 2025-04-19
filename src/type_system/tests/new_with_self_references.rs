use crate::{dada_lang::term, type_system::check_program};
use formality_core::{test, test_util::ResultTestExt};

#[test]
fn choice_with_self_ref_a() {
    check_program(&term(
        "
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: ref[self.pair] Data;
        }

        class TheClass {
            fn empty_method(my self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1.move, d2.move);
                let r = pair.a.ref;
                let choice = new Choice(pair.move, r.move);
                ();
            }
        }
    ",
    ))
    .assert_ok(expect_test::expect!["()"])
}

#[test]
fn choice_with_self_ref_b() {
    check_program(&term(
        "
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: ref[self.pair] Data;
        }

        class TheClass {
            fn empty_method(my self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1.move, d2.move);
                let r = pair.b.ref;
                let choice = new Choice(pair.move, r.move);
                ();
            }
        }
    ",
    ))
    .assert_ok(expect_test::expect!["()"])
}

#[test]
fn choice_with_non_self_ref() {
    check_program(&term(
        "
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: ref[self.pair] Data;
        }

        class TheClass {
            fn empty_method(my self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let d3 = new Data();
                let pair = new Pair(d1.move, d2.move);
                let r = d3.ref;
                let choice = new Choice(pair.move, r.move);
                ();
            }
        }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { a : Data ; b : Data ; } class Choice { pair : Pair ; data : ref [self . pair] Data ; } class TheClass { fn empty_method (my self) -> () { let d1 = new Data () ; let d2 = new Data () ; let d3 = new Data () ; let pair = new Pair (d1 . move, d2 . move) ; let r = d3 . ref ; let choice = new Choice (pair . move, r . move) ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let d3 = new Data () ; let pair = new Pair (d1 . move, d2 . move) ; let r = d3 . ref ; let choice = new Choice (pair . move, r . move) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let d3 = new Data () ; let pair = new Pair (d1 . move, d2 . move) ; let r = d3 . ref ; let choice = new Choice (pair . move, r . move) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d1 = new Data () ; let d2 = new Data () ; let d3 = new Data () ; let pair = new Pair (d1 . move, d2 . move) ; let r = d3 . ref ; let choice = new Choice (pair . move, r . move) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d1 = new Data () ; let d2 = new Data () ; let d3 = new Data () ; let pair = new Pair (d1 . move, d2 . move) ; let r = d3 . ref ; let choice = new Choice (pair . move, r . move) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d1 = new Data () ;, let d2 = new Data () ;, let d3 = new Data () ;, let pair = new Pair (d1 . move, d2 . move) ;, let r = d3 . ref ;, let choice = new Choice (pair . move, r . move) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let d2 = new Data () ;, let d3 = new Data () ;, let pair = new Pair (d1 . move, d2 . move) ;, let r = d3 . ref ;, let choice = new Choice (pair . move, r . move) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let d3 = new Data () ;, let pair = new Pair (d1 . move, d2 . move) ;, let r = d3 . ref ;, let choice = new Choice (pair . move, r . move) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let pair = new Pair (d1 . move, d2 . move) ;, let r = d3 . ref ;, let choice = new Choice (pair . move, r . move) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let pair = new Pair (d1 . move, d2 . move) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {d3, pair}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: new Pair (d1 . move, d2 . move), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {d3}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "new" failed at step #6 (src/file.rs:LL:CC) because
                                                       judgment `type_field_exprs_as { temp_var: @ fresh(0), exprs: [d1 . move, d2 . move], fields: [a : Data ;, b : Data ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data, d3: Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {d3}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #6 (src/file.rs:LL:CC) because
                                                           judgment `sub { a: Data, b: Data, live_after: LivePlaces { accessed: {d2, d3}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data, d3: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                             the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                               judgment `sub_perms { a: my, b: my, live_after: LivePlaces { accessed: {d2, d3}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data, d3: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                 the rule "apply to shared" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data, d3: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                     the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data, d3: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`"#]])
}

/// Test that we can create a `Choice`,
/// pull out its individual fields (in the correct order, mind)
/// and then reconstruct it.
///
/// In other words, when we move from `choice1.data.move`
/// to `choice1_data`, we correctly track that it has type
/// `shared(choice1.pair) Data`, and then when we
/// move from `choice1.pair` to `choice1_pair`, we can adjust
/// type of `choice1_data` to be `shared(choice1_pair) Data`.
#[test]
fn unpack_and_reconstruct_correct_order() {
    check_program(&term(
        "
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: ref[self.pair] Data;
        }

        class TheClass {
            fn empty_method(my self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1.move, d2.move);
                let r = pair.a.ref;
                let choice1 = new Choice(pair.move, r.move);
                let choice1_data = choice1.data.move;
                let choice1_pair = choice1.pair.move;
                let choice2 = new Choice(choice1_pair.move, choice1_data.move);
                ();
            }
        }
    ",
    ))
    .assert_ok(expect_test::expect!["()"])
}

/// Version of `unpack_and_reconstruct_correct_order` where we pull out the
/// fields in the other order. While in principle this should work,
/// we can't handle it in our type system and we should error. Why?
/// When we move `choice1.pair` first, the type declared for `Choice::data`
/// would have to be adjusteed to reference a local variable, and that
/// doesn't work.
///
/// FIXME: We do currently get an error, but not the one I really expect us to get.
/// I think the ideal is that moving `choice1.pair` should making all of `choice1`
/// be considered moved.
#[test]
fn unpack_and_reconstruct_wrong_order() {
    check_program(&term(
        "
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: ref[self.pair] Data;
        }

        class TheClass {
            fn empty_method(my self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1.move, d2.move);
                let r = pair.a.ref;
                let choice1 = new Choice(pair.move, r.move);
                let choice1_pair = choice1.pair.move; 
                let choice1_data = choice1.data.move;
                let choice2 = new Choice(choice1_pair.move, choice1_data.move);
                ();
            }
        }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { a : Data ; b : Data ; } class Choice { pair : Pair ; data : ref [self . pair] Data ; } class TheClass { fn empty_method (my self) -> () { let d1 = new Data () ; let d2 = new Data () ; let pair = new Pair (d1 . move, d2 . move) ; let r = pair . a . ref ; let choice1 = new Choice (pair . move, r . move) ; let choice1_pair = choice1 . pair . move ; let choice1_data = choice1 . data . move ; let choice2 = new Choice (choice1_pair . move, choice1_data . move) ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let pair = new Pair (d1 . move, d2 . move) ; let r = pair . a . ref ; let choice1 = new Choice (pair . move, r . move) ; let choice1_pair = choice1 . pair . move ; let choice1_data = choice1 . data . move ; let choice2 = new Choice (choice1_pair . move, choice1_data . move) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let pair = new Pair (d1 . move, d2 . move) ; let r = pair . a . ref ; let choice1 = new Choice (pair . move, r . move) ; let choice1_pair = choice1 . pair . move ; let choice1_data = choice1 . data . move ; let choice2 = new Choice (choice1_pair . move, choice1_data . move) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d1 = new Data () ; let d2 = new Data () ; let pair = new Pair (d1 . move, d2 . move) ; let r = pair . a . ref ; let choice1 = new Choice (pair . move, r . move) ; let choice1_pair = choice1 . pair . move ; let choice1_data = choice1 . data . move ; let choice2 = new Choice (choice1_pair . move, choice1_data . move) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d1 = new Data () ; let d2 = new Data () ; let pair = new Pair (d1 . move, d2 . move) ; let r = pair . a . ref ; let choice1 = new Choice (pair . move, r . move) ; let choice1_pair = choice1 . pair . move ; let choice1_data = choice1 . data . move ; let choice2 = new Choice (choice1_pair . move, choice1_data . move) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d1 = new Data () ;, let d2 = new Data () ;, let pair = new Pair (d1 . move, d2 . move) ;, let r = pair . a . ref ;, let choice1 = new Choice (pair . move, r . move) ;, let choice1_pair = choice1 . pair . move ;, let choice1_data = choice1 . data . move ;, let choice2 = new Choice (choice1_pair . move, choice1_data . move) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let d2 = new Data () ;, let pair = new Pair (d1 . move, d2 . move) ;, let r = pair . a . ref ;, let choice1 = new Choice (pair . move, r . move) ;, let choice1_pair = choice1 . pair . move ;, let choice1_data = choice1 . data . move ;, let choice2 = new Choice (choice1_pair . move, choice1_data . move) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let pair = new Pair (d1 . move, d2 . move) ;, let r = pair . a . ref ;, let choice1 = new Choice (pair . move, r . move) ;, let choice1_pair = choice1 . pair . move ;, let choice1_data = choice1 . data . move ;, let choice2 = new Choice (choice1_pair . move, choice1_data . move) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: let pair = new Pair (d1 . move, d2 . move) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {pair, pair . a}, traversed: {} } }` failed at the following rule(s):
                                             the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: new Pair (d1 . move, d2 . move), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "new" failed at step #6 (src/file.rs:LL:CC) because
                                                   judgment `type_field_exprs_as { temp_var: @ fresh(0), exprs: [d1 . move, d2 . move], fields: [a : Data ;, b : Data ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #6 (src/file.rs:LL:CC) because
                                                       judgment `sub { a: Data, b: Data, live_after: LivePlaces { accessed: {d2}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                         the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                           judgment `sub_perms { a: my, b: my, live_after: LivePlaces { accessed: {d2}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                             the rule "apply to shared" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                 the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`"#]])
}

/// Access to the field `choice.pair` but the other field
/// `choice.data` has a lease on `choice.pair`.
#[test]
fn lease_when_internally_leased() {
    check_program(&term(
        "
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: mut[self.pair] Data;
        }

        class TheClass {
            fn empty_method(my self, choice: Choice) -> () {
                let pair = choice.pair.mut;
                let data = choice.data.mut;
                ();
            }
        }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { a : Data ; b : Data ; } class Choice { pair : Pair ; data : mut [self . pair] Data ; } class TheClass { fn empty_method (my self choice : Choice) -> () { let pair = choice . pair . mut ; let data = choice . data . mut ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let pair = choice . pair . mut ; let data = choice . data . mut ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let pair = choice . pair . mut ; let data = choice . data . mut ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let pair = choice . pair . mut ; let data = choice . data . mut ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let pair = choice . pair . mut ; let data = choice . data . mut ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let pair = choice . pair . mut ;, let data = choice . data . mut ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: let pair = choice . pair . mut ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                     the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr { expr: choice . pair . mut, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                         the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `access_permitted { access: mut, place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                             the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `env_permits_access { access: mut, place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "env_permits_access" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `accessed_place_permits_access { place: choice . pair, access: mut, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "live" failed at step #2 (src/file.rs:LL:CC) because
                                                       judgment `accessed_place_prefix_permits_access { place_prefix: choice, place: choice . pair, access: mut, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "live" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `"flat_map"` failed at the following rule(s):
                                                             failed at (src/file.rs:LL:CC) because
                                                               judgment `field_of_accessed_place_prefix_permits_access { place_prefix: choice, field: data : mut [self . pair] Data ;, place: choice . pair, access: mut, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "not accessed place" failed at step #3 (src/file.rs:LL:CC) because
                                                                   judgment `parameter_permits_access { parameter: mut [choice . pair] Data, access: mut, place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `lien_permit_access { lien: mt(choice . pair), access: mut, accessed_place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "leased" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `leased_place_permits_access { leased_place: choice . pair, access: mut, accessed_place: choice . pair }` failed at the following rule(s):
                                                                             the rule "lease-mutation" failed at step #0 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                                                                                 &accessed_place = choice . pair
                                                                                 &leased_place = choice . pair"#]])
}

/// Extract the `pair` from choice and then drop it.
/// Then access data supposedly leased from that pair.
/// This should fail.
#[test]
fn unpack_and_reconstruct_drop_then_access() {
    check_program(&term(
        "
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: ref[self.pair] Data;
        }

        class TheClass {
            fn empty_method(my self, choice: Choice) -> () {
                let choice_pair = choice.pair.move; 
                choice_pair.move;
                let choice_data = choice.data.move;
                ();
            }
        }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { a : Data ; b : Data ; } class Choice { pair : Pair ; data : ref [self . pair] Data ; } class TheClass { fn empty_method (my self choice : Choice) -> () { let choice_pair = choice . pair . move ; choice_pair . move ; let choice_data = choice . data . move ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let choice_pair = choice . pair . move ; choice_pair . move ; let choice_data = choice . data . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let choice_pair = choice . pair . move ; choice_pair . move ; let choice_data = choice . data . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let choice_pair = choice . pair . move ; choice_pair . move ; let choice_data = choice . data . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let choice_pair = choice . pair . move ; choice_pair . move ; let choice_data = choice . data . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let choice_pair = choice . pair . move ;, choice_pair . move ;, let choice_data = choice . data . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: let choice_pair = choice . pair . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data, choice_pair}, traversed: {} } }` failed at the following rule(s):
                                     the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr { expr: choice . pair . move, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                         the rule "give place" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `access_permitted { access: move, place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                             the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `env_permits_access { access: move, place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "env_permits_access" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `accessed_place_permits_access { place: choice . pair, access: move, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "live" failed at step #2 (src/file.rs:LL:CC) because
                                                       judgment `accessed_place_prefix_permits_access { place_prefix: choice, place: choice . pair, access: move, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "live" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `"flat_map"` failed at the following rule(s):
                                                             failed at (src/file.rs:LL:CC) because
                                                               judgment `field_of_accessed_place_prefix_permits_access { place_prefix: choice, field: data : ref [self . pair] Data ;, place: choice . pair, access: move, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "not accessed place" failed at step #3 (src/file.rs:LL:CC) because
                                                                   judgment `parameter_permits_access { parameter: ref [choice . pair] Data, access: drop, place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `lien_permit_access { lien: rf(choice . pair), access: drop, accessed_place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "shared" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `shared_place_permits_access { shared_place: choice . pair, access: drop, accessed_place: choice . pair }` failed at the following rule(s):
                                                                             the rule "share-mutation" failed at step #0 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                                                                                 &accessed_place = choice . pair
                                                                                 &shared_place = choice . pair"#]])
}

/// This should fail because `r` is actually a pointer to `pair`
/// so when `pair` is moved it should be invalidated. Currently it passes (FIXME#12).
#[test]
fn choice_with_leased_self_ref_a() {
    check_program(&term(
        "
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: mut[self.pair] Data;
        }

        class TheClass {
            fn empty_method(my self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1.move, d2.move);
                let r = pair.a.mut;
                let choice = new Choice(pair.move, r.move);
                ();
            }
        }
    ",
    ))
    .assert_ok(expect_test::expect!["()"])
}
