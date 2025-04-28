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
                                             the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                               judgment `type_statements_with_final_ty { statements: [let r = d3 . ref ;, let choice = new Choice (pair . move, r . move) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `type_statements_with_final_ty { statements: [let choice = new Choice (pair . move, r . move) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `type_statement { statement: let choice = new Choice (pair . move, r . move) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `type_expr { expr: new Choice (pair . move, r . move), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "new" failed at step #6 (src/file.rs:LL:CC) because
                                                               judgment `type_field_exprs_as { temp_var: @ fresh(0), exprs: [pair . move, r . move], fields: [pair : Pair ;, data : ref [self . pair] Data ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                 the rule "cons" failed at step #7 (src/file.rs:LL:CC) because
                                                                   judgment `type_field_exprs_as { temp_var: @ fresh(0), exprs: [r . move], fields: [data : ref [self . pair] Data ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                     the rule "cons" failed at step #6 (src/file.rs:LL:CC) because
                                                                       judgment `sub { a: ref [d3] Data, b: ref [@ fresh(0) . pair] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                         the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                                           judgment `sub_perms { perm_a: ref [d3], perm_b: ref [@ fresh(0) . pair], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                             the rule "sub_red_perms" failed at step #2 (src/file.rs:LL:CC) because
                                                                               judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Rfd(d3)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Rfd(@ fresh(0) . pair)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                 the rule "sub_red_perms" failed at step #1 (src/file.rs:LL:CC) because
                                                                                   judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Rfd(d3)] }, red_chain_b: RedChain { links: [Rfd(@ fresh(0) . pair)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                     the rule "(our::P) vs (shared::P)" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       judgment `prove_is_our { a: ref [d3], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                         the rule "prove" failed at step #1 (src/file.rs:LL:CC) because
                                                                                           judgment `prove_is_owned { a: ref [d3], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                             the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               judgment `prove_predicate { predicate: owned(ref [d3]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                                   pattern `true` did not match value `false`
                                                                                     the rule "(ref-dead::P) vs Q ~~> (our::P) vs Q" failed at step #2 (src/file.rs:LL:CC) because
                                                                                       judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                         the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               pattern `true` did not match value `false`
                                                                                     the rule "(ref::P) vs (ref::P)" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                                                                         place_b = @ fresh(0) . pair
                                                                                         &place_a = d3"#]])
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
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let r = pair . a . ref ;, let choice1 = new Choice (pair . move, r . move) ;, let choice1_pair = choice1 . pair . move ;, let choice1_data = choice1 . data . move ;, let choice2 = new Choice (choice1_pair . move, choice1_data . move) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                               judgment `type_statements_with_final_ty { statements: [let choice1 = new Choice (pair . move, r . move) ;, let choice1_pair = choice1 . pair . move ;, let choice1_data = choice1 . data . move ;, let choice2 = new Choice (choice1_pair . move, choice1_data . move) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, pair: Pair, r: ref [pair . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `type_statements_with_final_ty { statements: [let choice1_pair = choice1 . pair . move ;, let choice1_data = choice1 . data . move ;, let choice2 = new Choice (choice1_pair . move, choice1_data . move) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice1: Choice, d1: Data, d2: Data, pair: Pair, r: ref [choice1 . pair . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `type_statement { statement: let choice1_pair = choice1 . pair . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice1: Choice, d1: Data, d2: Data, pair: Pair, r: ref [choice1 . pair . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice1 . data, choice1_pair}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `type_expr { expr: choice1 . pair . move, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice1: Choice, d1: Data, d2: Data, pair: Pair, r: ref [choice1 . pair . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice1 . data}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "move place" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `access_permitted { access: move, place: choice1 . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice1: Choice, d1: Data, d2: Data, pair: Pair, r: ref [choice1 . pair . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice1 . data}, traversed: {} } }` failed at the following rule(s):
                                                                 the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `env_permits_access { access: move, place: choice1 . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice1: Choice, d1: Data, d2: Data, pair: Pair, r: ref [choice1 . pair . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice1 . data}, traversed: {} } }` failed at the following rule(s):
                                                                     the rule "env_permits_access" failed at step #2 (src/file.rs:LL:CC) because
                                                                       judgment `accessed_place_permits_access { place: choice1 . pair, access: move, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice1: Choice, d1: Data, d2: Data, pair: Pair, r: ref [choice1 . pair . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice1 . data}, traversed: {} } }` failed at the following rule(s):
                                                                         the rule "live" failed at step #2 (src/file.rs:LL:CC) because
                                                                           judgment `accessed_place_prefix_permits_access { place_prefix: choice1, place: choice1 . pair, access: move, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice1: Choice, d1: Data, d2: Data, pair: Pair, r: ref [choice1 . pair . a] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "live" failed at step #1 (src/file.rs:LL:CC) because
                                                                               judgment `"flat_map"` failed at the following rule(s):
                                                                                 failed at (src/file.rs:LL:CC) because
                                                                                   judgment `field_of_accessed_place_prefix_permits_access { place_prefix: choice1, field: data : ref [self . pair] Data ;, place: choice1 . pair, access: move, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice1: Choice, d1: Data, d2: Data, pair: Pair, r: ref [choice1 . pair . a] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "not accessed place" failed at step #3 (src/file.rs:LL:CC) because
                                                                                       judgment `parameter_permits_access { parameter: ref [choice1 . pair] Data, access: drop, place: choice1 . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice1: Choice, d1: Data, d2: Data, pair: Pair, r: ref [choice1 . pair . a] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                         the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                                           judgment `lien_permit_access { lien: rf(choice1 . pair), access: drop, accessed_place: choice1 . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice1: Choice, d1: Data, d2: Data, pair: Pair, r: ref [choice1 . pair . a] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                             the rule "ref'd" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               judgment `ref_place_permits_access { shared_place: choice1 . pair, access: drop, accessed_place: choice1 . pair }` failed at the following rule(s):
                                                                                                 the rule "share-mutation" failed at step #0 (src/file.rs:LL:CC) because
                                                                                                   condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                                                                                                     &accessed_place = choice1 . pair
                                                                                                     &shared_place = choice1 . pair"#]])
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
                                         the rule "ref|mut place" failed at step #0 (src/file.rs:LL:CC) because
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
                                                                         the rule "mut'd" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `mut_place_permits_access { leased_place: choice . pair, access: mut, accessed_place: choice . pair }` failed at the following rule(s):
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
                                         the rule "move place" failed at step #0 (src/file.rs:LL:CC) because
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
                                                                         the rule "ref'd" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `ref_place_permits_access { shared_place: choice . pair, access: drop, accessed_place: choice . pair }` failed at the following rule(s):
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
