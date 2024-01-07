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
            data: shared(self.pair) Data;
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
            data: shared(self.pair) Data;
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
            data: shared(self.pair) Data;
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
        check program `class Data { } class Pair { a : Data ; b : Data ; } class Choice { pair : Pair ; data : shared (self . pair) Data ; } class TheClass { fn empty_method (Some(my self)) -> () { let d1 = new Data () ; let d2 = new Data () ; let d3 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = d3 . share ; let choice = new Choice (pair . give, r . give) ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let d3 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = d3 . share ; let choice = new Choice (pair . give, r . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let d3 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = d3 . share ; let choice = new Choice (pair . give, r . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d1 = new Data () ; let d2 = new Data () ; let d3 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = d3 . share ; let choice = new Choice (pair . give, r . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d1 = new Data () ; let d2 = new Data () ; let d3 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = d3 . share ; let choice = new Choice (pair . give, r . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d1 = new Data () ;, let d2 = new Data () ;, let d3 = new Data () ;, let pair = new Pair (d1 . give, d2 . give) ;, let r = d3 . share ;, let choice = new Choice (pair . give, r . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let d2 = new Data () ;, let d3 = new Data () ;, let pair = new Pair (d1 . give, d2 . give) ;, let r = d3 . share ;, let choice = new Choice (pair . give, r . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let d3 = new Data () ;, let pair = new Pair (d1 . give, d2 . give) ;, let r = d3 . share ;, let choice = new Choice (pair . give, r . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let pair = new Pair (d1 . give, d2 . give) ;, let r = d3 . share ;, let choice = new Choice (pair . give, r . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                               judgment `type_statements_with_final_ty { statements: [let r = d3 . share ;, let choice = new Choice (pair . give, r . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {d1, d2} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `type_statements_with_final_ty { statements: [let choice = new Choice (pair . give, r . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared (d3) Data}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {d1, d2} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `type_statement { statement: let choice = new Choice (pair . give, r . give) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared (d3) Data}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {d1, d2} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `type_expr { expr: new Choice (pair . give, r . give), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared (d3) Data}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {d1, d2} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                             the rule "new" failed at step #3 (src/file.rs:LL:CC) because
                                                               judgment `type_field_exprs_as { exprs: [pair . give, r . give], fields: [pair : Pair ;, data : shared (self . pair) Data ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared (d3) Data}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {d1, d2} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                                 the rule "cons" failed at step #6 (src/file.rs:LL:CC) because
                                                                   judgment `type_field_exprs_as { exprs: [r . give], fields: [data : shared (self . pair) Data ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared (d3) Data}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {d1, d2, pair} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                                     the rule "cons" failed at step #5 (src/file.rs:LL:CC) because
                                                                       judgment `sub { a: shared (d3) Data, b: shared (@ temp(0) . pair) Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared (d3) Data}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {d1, d2, pair, r} } }` failed at the following rule(s):
                                                                         the rule "apply-perms" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `sub { a: shared (d3), b: shared (@ temp(0) . pair), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared (d3) Data}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {d1, d2, pair, r} } }` failed at the following rule(s):
                                                                             the rule "shared perms" failed at step #0 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `all_places_covered_by_one_of(&places_a, &places_b)`
                                                                                 &places_a = {d3}
                                                                                 &places_b = {@ temp(0) . pair}
                                                                     the rule "cons" failed at step #5 (src/file.rs:LL:CC) because
                                                                       judgment `sub { a: shared (d3) Data, b: shared (@ temp(0) . pair) Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared (d3) Data}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {d1, d2, pair} } }` failed at the following rule(s):
                                                                         the rule "apply-perms" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `sub { a: shared (d3), b: shared (@ temp(0) . pair), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, d1: Data, d2: Data, d3: Data, pair: Pair, r: shared (d3) Data}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {d1, d2, pair} } }` failed at the following rule(s):
                                                                             the rule "shared perms" failed at step #0 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `all_places_covered_by_one_of(&places_a, &places_b)`
                                                                                 &places_a = {d3}
                                                                                 &places_b = {@ temp(0) . pair}"#]])
}
