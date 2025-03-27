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
            data: shared[self.pair] Data;
        }

        class TheClass {
            fn empty_method(my self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1.give, d2.give);
                let r = pair.a.share;
                let choice = new Choice(pair.give, r.give);
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
            data: shared[self.pair] Data;
        }

        class TheClass {
            fn empty_method(my self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1.give, d2.give);
                let r = pair.b.share;
                let choice = new Choice(pair.give, r.give);
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
            data: shared[self.pair] Data;
        }

        class TheClass {
            fn empty_method(my self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let d3 = new Data();
                let pair = new Pair(d1.give, d2.give);
                let r = d3.share;
                let choice = new Choice(pair.give, r.give);
                ();
            }
        }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { a : Data ; b : Data ; } class Choice { pair : Pair ; data : shared [self . pair] Data ; } class TheClass { fn empty_method (my self) -> () { let d1 = new Data () ; let d2 = new Data () ; let d3 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = d3 . share ; let choice = new Choice (pair . give, r . give) ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let d3 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = d3 . share ; let choice = new Choice (pair . give, r . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let d3 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = d3 . share ; let choice = new Choice (pair . give, r . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d1 = new Data () ; let d2 = new Data () ; let d3 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = d3 . share ; let choice = new Choice (pair . give, r . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d1 = new Data () ; let d2 = new Data () ; let d3 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = d3 . share ; let choice = new Choice (pair . give, r . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d1 = new Data () ;, let d2 = new Data () ;, let d3 = new Data () ;, let pair = new Pair (d1 . give, d2 . give) ;, let r = d3 . share ;, let choice = new Choice (pair . give, r . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let d2 = new Data () ;, let d3 = new Data () ;, let pair = new Pair (d1 . give, d2 . give) ;, let r = d3 . share ;, let choice = new Choice (pair . give, r . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let d3 = new Data () ;, let pair = new Pair (d1 . give, d2 . give) ;, let r = d3 . share ;, let choice = new Choice (pair . give, r . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let pair = new Pair (d1 . give, d2 . give) ;, let r = d3 . share ;, let choice = new Choice (pair . give, r . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let pair = new Pair (d1 . give, d2 . give) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {d3, pair}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: new Pair (d1 . give, d2 . give), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {d3}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "new" failed at step #6 (src/file.rs:LL:CC) because
                                                       judgment `type_field_exprs_as { temp_var: @ fresh(0), exprs: [d1 . give, d2 . give], fields: [a : Data ;, b : Data ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data, d3: Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {d3}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #3 (src/file.rs:LL:CC) because
                                                           judgment `type_expr { expr: d1 . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data, d3: Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {d2, d3}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "give place" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `access_permitted { access: give, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data, d3: Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {d2, d3}, traversed: {} } }` failed at the following rule(s):
                                                                 the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `env_permits_access { access: give, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data, d3: Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {d2, d3}, traversed: {} } }` failed at the following rule(s):
                                                                     the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `parameters_permit_access { parameters: [Data, Data], access: give, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data, d3: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                         the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `parameter_permits_access { parameter: Data, access: give, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data, d3: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `liens { a: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data, d3: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                 the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `some_lien { a: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data, d3: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                     the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       expression evaluated to an empty collection: `parameters`"#]])
}

/// Test that we can create a `Choice`,
/// pull out its individual fields (in the correct order, mind)
/// and then reconstruct it.
///
/// In other words, when we move from `choice1.data.give`
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
            data: shared[self.pair] Data;
        }

        class TheClass {
            fn empty_method(my self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1.give, d2.give);
                let r = pair.a.share;
                let choice1 = new Choice(pair.give, r.give);
                let choice1_data = choice1.data.give;
                let choice1_pair = choice1.pair.give;
                let choice2 = new Choice(choice1_pair.give, choice1_data.give);
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
            data: shared[self.pair] Data;
        }

        class TheClass {
            fn empty_method(my self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1.give, d2.give);
                let r = pair.a.share;
                let choice1 = new Choice(pair.give, r.give);
                let choice1_pair = choice1.pair.give; 
                let choice1_data = choice1.data.give;
                let choice2 = new Choice(choice1_pair.give, choice1_data.give);
                ();
            }
        }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { a : Data ; b : Data ; } class Choice { pair : Pair ; data : shared [self . pair] Data ; } class TheClass { fn empty_method (my self) -> () { let d1 = new Data () ; let d2 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = pair . a . share ; let choice1 = new Choice (pair . give, r . give) ; let choice1_pair = choice1 . pair . give ; let choice1_data = choice1 . data . give ; let choice2 = new Choice (choice1_pair . give, choice1_data . give) ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = pair . a . share ; let choice1 = new Choice (pair . give, r . give) ; let choice1_pair = choice1 . pair . give ; let choice1_data = choice1 . data . give ; let choice2 = new Choice (choice1_pair . give, choice1_data . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = pair . a . share ; let choice1 = new Choice (pair . give, r . give) ; let choice1_pair = choice1 . pair . give ; let choice1_data = choice1 . data . give ; let choice2 = new Choice (choice1_pair . give, choice1_data . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d1 = new Data () ; let d2 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = pair . a . share ; let choice1 = new Choice (pair . give, r . give) ; let choice1_pair = choice1 . pair . give ; let choice1_data = choice1 . data . give ; let choice2 = new Choice (choice1_pair . give, choice1_data . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d1 = new Data () ; let d2 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = pair . a . share ; let choice1 = new Choice (pair . give, r . give) ; let choice1_pair = choice1 . pair . give ; let choice1_data = choice1 . data . give ; let choice2 = new Choice (choice1_pair . give, choice1_data . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d1 = new Data () ;, let d2 = new Data () ;, let pair = new Pair (d1 . give, d2 . give) ;, let r = pair . a . share ;, let choice1 = new Choice (pair . give, r . give) ;, let choice1_pair = choice1 . pair . give ;, let choice1_data = choice1 . data . give ;, let choice2 = new Choice (choice1_pair . give, choice1_data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let d2 = new Data () ;, let pair = new Pair (d1 . give, d2 . give) ;, let r = pair . a . share ;, let choice1 = new Choice (pair . give, r . give) ;, let choice1_pair = choice1 . pair . give ;, let choice1_data = choice1 . data . give ;, let choice2 = new Choice (choice1_pair . give, choice1_data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let pair = new Pair (d1 . give, d2 . give) ;, let r = pair . a . share ;, let choice1 = new Choice (pair . give, r . give) ;, let choice1_pair = choice1 . pair . give ;, let choice1_data = choice1 . data . give ;, let choice2 = new Choice (choice1_pair . give, choice1_data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: let pair = new Pair (d1 . give, d2 . give) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {pair, pair . a}, traversed: {} } }` failed at the following rule(s):
                                             the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: new Pair (d1 . give, d2 . give), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "new" failed at step #6 (src/file.rs:LL:CC) because
                                                   judgment `type_field_exprs_as { temp_var: @ fresh(0), exprs: [d1 . give, d2 . give], fields: [a : Data ;, b : Data ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #3 (src/file.rs:LL:CC) because
                                                       judgment `type_expr { expr: d1 . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {d2}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "give place" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `access_permitted { access: give, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {d2}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `env_permits_access { access: give, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {d2}, traversed: {} } }` failed at the following rule(s):
                                                                 the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `parameters_permit_access { parameters: [Data], access: give, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                     the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `parameter_permits_access { parameter: Data, access: give, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `liens { a: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                             the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `some_lien { a: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Pair, d1: Data, d2: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                 the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   expression evaluated to an empty collection: `parameters`"#]])
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
            data: leased[self.pair] Data;
        }

        class TheClass {
            fn empty_method(my self, choice: Choice) -> () {
                let pair = choice.pair.lease;
                let data = choice.data.lease;
                ();
            }
        }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { a : Data ; b : Data ; } class Choice { pair : Pair ; data : leased [self . pair] Data ; } class TheClass { fn empty_method (my self choice : Choice) -> () { let pair = choice . pair . lease ; let data = choice . data . lease ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let pair = choice . pair . lease ; let data = choice . data . lease ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let pair = choice . pair . lease ; let data = choice . data . lease ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let pair = choice . pair . lease ; let data = choice . data . lease ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let pair = choice . pair . lease ; let data = choice . data . lease ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let pair = choice . pair . lease ;, let data = choice . data . lease ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: let pair = choice . pair . lease ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                     the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr { expr: choice . pair . lease, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                         the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `access_permitted { access: lease, place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                             the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `env_permits_access { access: lease, place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `parameters_permit_access { parameters: [Choice], access: lease, place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `parameter_permits_access { parameter: Choice, access: lease, place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `liens { a: Choice, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `some_lien { a: Choice, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                   expression evaluated to an empty collection: `parameters`"#]])
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
            data: shared[self.pair] Data;
        }

        class TheClass {
            fn empty_method(my self, choice: Choice) -> () {
                let choice_pair = choice.pair.give; 
                choice_pair.give;
                let choice_data = choice.data.give;
                ();
            }
        }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { a : Data ; b : Data ; } class Choice { pair : Pair ; data : shared [self . pair] Data ; } class TheClass { fn empty_method (my self choice : Choice) -> () { let choice_pair = choice . pair . give ; choice_pair . give ; let choice_data = choice . data . give ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let choice_pair = choice . pair . give ; choice_pair . give ; let choice_data = choice . data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let choice_pair = choice . pair . give ; choice_pair . give ; let choice_data = choice . data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let choice_pair = choice . pair . give ; choice_pair . give ; let choice_data = choice . data . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let choice_pair = choice . pair . give ; choice_pair . give ; let choice_data = choice . data . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let choice_pair = choice . pair . give ;, choice_pair . give ;, let choice_data = choice . data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: let choice_pair = choice . pair . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data, choice_pair}, traversed: {} } }` failed at the following rule(s):
                                     the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr { expr: choice . pair . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                         the rule "give place" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `access_permitted { access: give, place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                             the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `env_permits_access { access: give, place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `parameters_permit_access { parameters: [Choice], access: give, place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `parameter_permits_access { parameter: Choice, access: give, place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `liens { a: Choice, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `some_lien { a: Choice, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                   expression evaluated to an empty collection: `parameters`"#]])
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
            data: leased[self.pair] Data;
        }

        class TheClass {
            fn empty_method(my self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1.give, d2.give);
                let r = pair.a.lease;
                let choice = new Choice(pair.give, r.give);
                ();
            }
        }
    ",
    ))
    .assert_ok(expect_test::expect!["()"])
}
