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
                                             the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                               judgment `type_statements_with_final_ty { statements: [let r = d3 . share ;, let choice = new Choice (pair . give, r . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `type_statements_with_final_ty { statements: [let choice = new Choice (pair . give, r . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `type_statement { statement: let choice = new Choice (pair . give, r . give) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `type_expr { expr: new Choice (pair . give, r . give), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "new" failed at step #6 (src/file.rs:LL:CC) because
                                                               judgment `type_field_exprs_as { temp_var: @ fresh(0), exprs: [pair . give, r . give], fields: [pair : Pair ;, data : shared [self . pair] Data ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                 the rule "cons" failed at step #7 (src/file.rs:LL:CC) because
                                                                   judgment `type_field_exprs_as { temp_var: @ fresh(0), exprs: [r . give], fields: [data : shared [self . pair] Data ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                     the rule "cons" failed at step #6 (src/file.rs:LL:CC) because
                                                                       judgment `sub { a: shared [d3] Data, b: shared [@ fresh(0) . pair] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                         the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                                           judgment `sub_perms { a: shared [d3], b: shared [@ fresh(0) . pair], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                             the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_is_move { a: shared [d3], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                 the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `prove_predicate { predicate: move(shared [d3]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       pattern `true` did not match value `false`
                                                                             the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_is_move { a: shared [d3], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                 the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `prove_predicate { predicate: move(shared [d3]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       pattern `true` did not match value `false`
                                                                             the rule "our-sub-copy" failed at step #1 (src/file.rs:LL:CC) because
                                                                               judgment `prove_is_owned { a: shared [d3], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                 the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `prove_predicate { predicate: owned(shared [d3]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       pattern `true` did not match value `false`
                                                                             the rule "simplify-lhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `simplify_perm { perm: LeafPerms { leaves: [shared [d3]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                                 the rule "dead_copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `"flat_map"` failed at the following rule(s):
                                                                                     failed at (src/file.rs:LL:CC) because
                                                                                       judgment `prove_is_copy { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           judgment `prove_predicate { predicate: copy(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               pattern `true` did not match value `false`
                                                                                 the rule "dead_shared-up" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `"flat_map"` failed at the following rule(s):
                                                                                     failed at (src/file.rs:LL:CC) because
                                                                                       judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                         the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               pattern `true` did not match value `false`
                                                                             the rule "simplify-rhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `simplify_perm { perm: LeafPerms { leaves: [shared [@ fresh(0) . pair]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                                 the rule "dead_copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `"flat_map"` failed at the following rule(s):
                                                                                     failed at (src/file.rs:LL:CC) because
                                                                                       judgment `prove_is_copy { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           judgment `prove_predicate { predicate: copy(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               pattern `true` did not match value `false`
                                                                                 the rule "dead_shared-up" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `"flat_map"` failed at the following rule(s):
                                                                                     failed at (src/file.rs:LL:CC) because
                                                                                       judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                         the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               pattern `true` did not match value `false`
                                                                             the rule "sub_perms_relative" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `sub_perm_heads { a: LeafPerms { leaves: [shared [d3]] }, b: LeafPerms { leaves: [shared [@ fresh(0) . pair]] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                 the rule "shared-shared" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `sub_place_perms { places_a: {d3}, tail_a: my, places_b: {@ fresh(0) . pair}, tail_b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                     the rule "places-places" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       condition evaluted to false: `all_prefix_of_any(&places_a, &places_b)`
                                                                                         &places_a = {d3}
                                                                                         &places_b = {@ fresh(0) . pair}
                                                                                 the rule "simplify-lhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `simplify_perm { perm: LeafPerms { leaves: [shared [d3]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                                     the rule "dead_copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       judgment `"flat_map"` failed at the following rule(s):
                                                                                         failed at (src/file.rs:LL:CC) because
                                                                                           judgment `prove_is_copy { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                             the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               judgment `prove_predicate { predicate: copy(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                                   pattern `true` did not match value `false`
                                                                                     the rule "dead_shared-up" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       judgment `"flat_map"` failed at the following rule(s):
                                                                                         failed at (src/file.rs:LL:CC) because
                                                                                           judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                             the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                                   pattern `true` did not match value `false`
                                                                                 the rule "simplify-rhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `simplify_perm { perm: LeafPerms { leaves: [shared [@ fresh(0) . pair]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                                     the rule "dead_copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       judgment `"flat_map"` failed at the following rule(s):
                                                                                         failed at (src/file.rs:LL:CC) because
                                                                                           judgment `prove_is_copy { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                             the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               judgment `prove_predicate { predicate: copy(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                                   pattern `true` did not match value `false`
                                                                                     the rule "dead_shared-up" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       judgment `"flat_map"` failed at the following rule(s):
                                                                                         failed at (src/file.rs:LL:CC) because
                                                                                           judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                             the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                                   pattern `true` did not match value `false`"#]])
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
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let r = pair . a . share ;, let choice1 = new Choice (pair . give, r . give) ;, let choice1_pair = choice1 . pair . give ;, let choice1_data = choice1 . data . give ;, let choice2 = new Choice (choice1_pair . give, choice1_data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                               judgment `type_statements_with_final_ty { statements: [let choice1 = new Choice (pair . give, r . give) ;, let choice1_pair = choice1 . pair . give ;, let choice1_data = choice1 . data . give ;, let choice2 = new Choice (choice1_pair . give, choice1_data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, pair: Pair, r: shared [pair . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `type_statements_with_final_ty { statements: [let choice1_pair = choice1 . pair . give ;, let choice1_data = choice1 . data . give ;, let choice2 = new Choice (choice1_pair . give, choice1_data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice1: Choice, d1: Data, d2: Data, pair: Pair, r: shared [choice1 . pair . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                                       judgment `type_statements_with_final_ty { statements: [let choice1_data = choice1 . data . give ;, let choice2 = new Choice (choice1_pair . give, choice1_data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice1: Choice, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [choice1_pair . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                                           judgment `type_statements_with_final_ty { statements: [let choice2 = new Choice (choice1_pair . give, choice1_data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [choice1_pair . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `type_statement { statement: let choice2 = new Choice (choice1_pair . give, choice1_data . give) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [choice1_pair . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `type_expr { expr: new Choice (choice1_pair . give, choice1_data . give), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [choice1_pair . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                     the rule "new" failed at step #6 (src/file.rs:LL:CC) because
                                                                       judgment `type_field_exprs_as { temp_var: @ fresh(0), exprs: [choice1_pair . give, choice1_data . give], fields: [pair : Pair ;, data : shared [self . pair] Data ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [choice1_pair . a] Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                         the rule "cons" failed at step #7 (src/file.rs:LL:CC) because
                                                                           judgment `type_field_exprs_as { temp_var: @ fresh(0), exprs: [choice1_data . give], fields: [data : shared [self . pair] Data ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                             the rule "cons" failed at step #6 (src/file.rs:LL:CC) because
                                                                               judgment `sub { a: shared [choice1 . pair] Data, b: shared [@ fresh(0) . pair] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                 the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                                                   judgment `sub_perms { a: shared [choice1 . pair], b: shared [@ fresh(0) . pair], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                     the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       judgment `prove_is_move { a: shared [choice1 . pair], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                         the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           judgment `prove_predicate { predicate: move(shared [choice1 . pair]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               pattern `true` did not match value `false`
                                                                                     the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       judgment `prove_is_move { a: shared [choice1 . pair], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                         the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           judgment `prove_predicate { predicate: move(shared [choice1 . pair]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               pattern `true` did not match value `false`
                                                                                     the rule "our-sub-copy" failed at step #1 (src/file.rs:LL:CC) because
                                                                                       judgment `prove_is_owned { a: shared [choice1 . pair], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                         the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           judgment `prove_predicate { predicate: owned(shared [choice1 . pair]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               pattern `true` did not match value `false`
                                                                                     the rule "simplify-lhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       judgment `simplify_perm { perm: LeafPerms { leaves: [shared [choice1 . pair]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                                         the rule "dead_copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           judgment `"flat_map"` failed at the following rule(s):
                                                                                             failed at (src/file.rs:LL:CC) because
                                                                                               judgment `prove_is_copy { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                 the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                                   judgment `prove_predicate { predicate: copy(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                                       pattern `true` did not match value `false`
                                                                                         the rule "dead_shared-up" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           judgment `"flat_map"` failed at the following rule(s):
                                                                                             failed at (src/file.rs:LL:CC) because
                                                                                               judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                 the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                                                   judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                                       pattern `true` did not match value `false`
                                                                                     the rule "simplify-rhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       judgment `simplify_perm { perm: LeafPerms { leaves: [shared [@ fresh(0) . pair]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                                         the rule "dead_copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           judgment `"flat_map"` failed at the following rule(s):
                                                                                             failed at (src/file.rs:LL:CC) because
                                                                                               judgment `prove_is_copy { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                 the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                                   judgment `prove_predicate { predicate: copy(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                                       pattern `true` did not match value `false`
                                                                                         the rule "dead_shared-up" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           judgment `"flat_map"` failed at the following rule(s):
                                                                                             failed at (src/file.rs:LL:CC) because
                                                                                               judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                 the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                                                   judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                                       pattern `true` did not match value `false`
                                                                                     the rule "sub_perms_relative" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       judgment `sub_perm_heads { a: LeafPerms { leaves: [shared [choice1 . pair]] }, b: LeafPerms { leaves: [shared [@ fresh(0) . pair]] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                         the rule "shared-shared" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           judgment `sub_place_perms { places_a: {choice1 . pair}, tail_a: my, places_b: {@ fresh(0) . pair}, tail_b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                             the rule "places-places" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               condition evaluted to false: `all_prefix_of_any(&places_a, &places_b)`
                                                                                                 &places_a = {choice1 . pair}
                                                                                                 &places_b = {@ fresh(0) . pair}
                                                                                         the rule "simplify-lhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           judgment `simplify_perm { perm: LeafPerms { leaves: [shared [choice1 . pair]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                                             the rule "dead_copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               judgment `"flat_map"` failed at the following rule(s):
                                                                                                 failed at (src/file.rs:LL:CC) because
                                                                                                   judgment `prove_is_copy { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                     the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                                       judgment `prove_predicate { predicate: copy(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                                           pattern `true` did not match value `false`
                                                                                             the rule "dead_shared-up" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               judgment `"flat_map"` failed at the following rule(s):
                                                                                                 failed at (src/file.rs:LL:CC) because
                                                                                                   judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                     the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                                                       judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                                           pattern `true` did not match value `false`
                                                                                         the rule "simplify-rhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           judgment `simplify_perm { perm: LeafPerms { leaves: [shared [@ fresh(0) . pair]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                                             the rule "dead_copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               judgment `"flat_map"` failed at the following rule(s):
                                                                                                 failed at (src/file.rs:LL:CC) because
                                                                                                   judgment `prove_is_copy { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                     the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                                       judgment `prove_predicate { predicate: copy(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                                           pattern `true` did not match value `false`
                                                                                             the rule "dead_shared-up" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               judgment `"flat_map"` failed at the following rule(s):
                                                                                                 failed at (src/file.rs:LL:CC) because
                                                                                                   judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                     the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                                                       judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): Choice, choice1: Choice, choice1_data: shared [choice1 . pair] Data, choice1_pair: Pair, d1: Data, d2: Data, pair: Pair, r: shared [@ fresh(0) . pair . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                                           pattern `true` did not match value `false`"#]])
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
