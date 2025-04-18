use crate::{dada_lang::term, type_system::check_program};
use formality_core::{test, test_util::ResultTestExt};

#[test]
#[allow(non_snake_case)]
fn shared_dead_leased_to_our_leased() {
    check_program(&term(
        "
        class Data {
            fn read[perm P](P self) where shared(P) {
                ();
            }
        }
        class Main {
            fn test(my self) {
                let d = new Data();
                let p: mut[d] Data = d.mut;
                let q: ref[p] Data = p.ref;
                let r: our mut[d] Data = q.move;
                r.move.read[our mut[d]]();
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect![["()"]]);
}

#[test]
#[allow(non_snake_case)]
fn shared_live_leased_to_our_leased() {
    // Cannot coerce from `ref[p] mut[d]` to `our mut[d]`
    // because `p` is not dead.
    check_program(&term(
        "
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test(my self) {
                let d = new Data();
                let p: mut[d] Data = d.mut;
                let q: ref[p] Data = p.ref;
                let r: our mut[d] Data = q.move;
                p.move.read[mut[d]]();
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { fn read [perm] (^perm0_0 self) -> () { () ; } } class Main { fn test (my self) -> () { let d = new Data () ; let p : mut [d] Data = d . mut ; let q : ref [p] Data = p . ref ; let r : our mut [d] Data = q . move ; p . move . read [mut [d]] () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d = new Data () ; let p : mut [d] Data = d . mut ; let q : ref [p] Data = p . ref ; let r : our mut [d] Data = q . move ; p . move . read [mut [d]] () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d = new Data () ; let p : mut [d] Data = d . mut ; let q : ref [p] Data = p . ref ; let r : our mut [d] Data = q . move ; p . move . read [mut [d]] () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d = new Data () ; let p : mut [d] Data = d . mut ; let q : ref [p] Data = p . ref ; let r : our mut [d] Data = q . move ; p . move . read [mut [d]] () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d = new Data () ; let p : mut [d] Data = d . mut ; let q : ref [p] Data = p . ref ; let r : our mut [d] Data = q . move ; p . move . read [mut [d]] () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d = new Data () ;, let p : mut [d] Data = d . mut ;, let q : ref [p] Data = p . ref ;, let r : our mut [d] Data = q . move ;, p . move . read [mut [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : mut [d] Data = d . mut ;, let q : ref [p] Data = p . ref ;, let r : our mut [d] Data = q . move ;, p . move . read [mut [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let q : ref [p] Data = p . ref ;, let r : our mut [d] Data = q . move ;, p . move . read [mut [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let r : our mut [d] Data = q . move ;, p . move . read [mut [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let r : our mut [d] Data = q . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr_as { expr: q . move, as_ty: our mut [d] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `sub { a: ref [p] Data, b: our mut [d] Data, live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                           judgment `sub_perms { a: ref [p], b: our mut [d], live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_unique { a: ref [p], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: unique(ref [p]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`
                                                             the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_unique { a: ref [p], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: unique(ref [p]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`
                                                             the rule "our-sub-copy" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_owned { a: ref [p], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: owned(ref [p]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`
                                                             the rule "sub_perms_relative" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `sub_perm_heads { a: LeafPerms { leaves: [ref [p]] }, b: LeafPerms { leaves: [our, mut [d]] }, live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "shared-our_leased" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `sub_place_perms { places_a: {p}, tail_a: my, places_b: {d}, tail_b: my, live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "places-places" failed at step #0 (src/file.rs:LL:CC) because
                                                                       condition evaluted to false: `all_prefix_of_any(&places_a, &places_b)`
                                                                         &places_a = {p}
                                                                         &places_b = {d}
                                                                 the rule "simplify-lhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `simplify_perm { perm: LeafPerms { leaves: [ref [p]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                                     the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `"flat_map"` failed at the following rule(s):
                                                                         failed at (src/file.rs:LL:CC) because
                                                                           judgment `prove_is_share { a: mut [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_predicate { predicate: shared(mut [d]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   pattern `true` did not match value `false`
                                                                 the rule "simplify-rhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `simplify_perm { perm: LeafPerms { leaves: [our, mut [d]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                                     the rule "apply-to-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_share { a: mut [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: shared(mut [d]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn leased_dead_leased_to_leased() {
    // Can coerce from `mut[p] mut[d]` to `mut[d]`
    // because `p` is dead.
    check_program(&term(
        "
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test(my self) {
                let d = new Data();
                let p: mut[d] Data = d.mut;
                let q: mut[p] Data = p.mut;
                let r: mut[d] Data = q.move;
                r.move.read[mut[d]]();
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect![["()"]]);
}

#[test]
#[allow(non_snake_case)]
fn leased_live_leased_to_leased() {
    // Cannot coerce from `mut[p] mut[d]` to `mut[d]`
    // because `p` is not dead.
    check_program(&term(
        "
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test(my self) {
                let d = new Data();
                let p: mut[d] Data = d.mut;
                let q: mut[p] Data = p.mut;
                let r: mut[d] Data = q.move;
                p.move.read[mut[d]]();
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { fn read [perm] (^perm0_0 self) -> () { () ; } } class Main { fn test (my self) -> () { let d = new Data () ; let p : mut [d] Data = d . mut ; let q : mut [p] Data = p . mut ; let r : mut [d] Data = q . move ; p . move . read [mut [d]] () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d = new Data () ; let p : mut [d] Data = d . mut ; let q : mut [p] Data = p . mut ; let r : mut [d] Data = q . move ; p . move . read [mut [d]] () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d = new Data () ; let p : mut [d] Data = d . mut ; let q : mut [p] Data = p . mut ; let r : mut [d] Data = q . move ; p . move . read [mut [d]] () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d = new Data () ; let p : mut [d] Data = d . mut ; let q : mut [p] Data = p . mut ; let r : mut [d] Data = q . move ; p . move . read [mut [d]] () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d = new Data () ; let p : mut [d] Data = d . mut ; let q : mut [p] Data = p . mut ; let r : mut [d] Data = q . move ; p . move . read [mut [d]] () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d = new Data () ;, let p : mut [d] Data = d . mut ;, let q : mut [p] Data = p . mut ;, let r : mut [d] Data = q . move ;, p . move . read [mut [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : mut [d] Data = d . mut ;, let q : mut [p] Data = p . mut ;, let r : mut [d] Data = q . move ;, p . move . read [mut [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let q : mut [p] Data = p . mut ;, let r : mut [d] Data = q . move ;, p . move . read [mut [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let r : mut [d] Data = q . move ;, p . move . read [mut [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let r : mut [d] Data = q . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr_as { expr: q . move, as_ty: mut [d] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `sub { a: mut [p] Data, b: mut [d] Data, live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                           judgment `sub_perms { a: mut [p], b: mut [d], live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "my-sub-copy" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_owned { a: mut [p], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: owned(mut [p]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`
                                                             the rule "my-sub-owned" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_owned { a: mut [p], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: owned(mut [p]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`
                                                             the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_share { a: mut [p], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: shared(mut [p]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`
                                                             the rule "sub_perms_relative" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `sub_perm_heads { a: LeafPerms { leaves: [mut [p]] }, b: LeafPerms { leaves: [mut [d]] }, live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "leased-leased" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `sub_place_perms { places_a: {p}, tail_a: my, places_b: {d}, tail_b: my, live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "places-places" failed at step #0 (src/file.rs:LL:CC) because
                                                                       condition evaluted to false: `all_prefix_of_any(&places_a, &places_b)`
                                                                         &places_a = {p}
                                                                         &places_b = {d}
                                                                 the rule "simplify-lhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `simplify_perm { perm: LeafPerms { leaves: [mut [p]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                                     the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `"flat_map"` failed at the following rule(s):
                                                                         failed at (src/file.rs:LL:CC) because
                                                                           judgment `prove_is_share { a: mut [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_predicate { predicate: shared(mut [d]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   pattern `true` did not match value `false`
                                                                 the rule "simplify-rhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `simplify_perm { perm: LeafPerms { leaves: [mut [d]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                                     the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `"flat_map"` failed at the following rule(s):
                                                                         failed at (src/file.rs:LL:CC) because
                                                                           judgment `prove_is_share { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   pattern `true` did not match value `false`
                                                                     the rule "dead_leased-up" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `"flat_map"` failed at the following rule(s):
                                                                         failed at (src/file.rs:LL:CC) because
                                                                           judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn return_leased_dead_leased_to_leased() {
    // Equivalent of `fn test(my self, d: leased Data) -> mut[d] Data
    check_program(&term(
        "
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test[perm P](my self, d: P Data) -> mut[d] Data
            where
                unique(P),
                lent(P),
            {
                let p: mut[d] Data = d.mut;
                let q: mut[p] Data = p.mut;
                q.move;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect![["()"]]);
}

#[test]
#[allow(non_snake_case)]
fn return_leased_dead_leased_to_leased_and_use_while_leased() {
    // Equivalent of `fn test(my self, d: leased Data) -> mut[d] Data
    check_program(&term(
        "
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test[perm P](my self, d: P Data) -> mut[d] Data
            where
                unique(P),
                lent(P),
            {
                let p: mut[d] Data = d.mut;
                let q: mut[p] Data = p.mut;
                p.ref.read[ref[p] Data]();
                q.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { fn read [perm] (^perm0_0 self) -> () { () ; } } class Main { fn test [perm] (my self d : ^perm0_0 Data) -> mut [d] Data where unique(^perm0_0), lent(^perm0_0) { let p : mut [d] Data = d . mut ; let q : mut [p] Data = p . mut ; p . ref . read [ref [p] Data] () ; q . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let p : mut [d] Data = d . mut ; let q : mut [p] Data = p . mut ; p . ref . read [ref [p] Data] () ; q . move ; }, as_ty: mut [d] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let p : mut [d] Data = d . mut ; let q : mut [p] Data = p . mut ; p . ref . read [ref [p] Data] () ; q . move ; }, as_ty: mut [d] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let p : mut [d] Data = d . mut ; let q : mut [p] Data = p . mut ; p . ref . read [ref [p] Data] () ; q . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let p : mut [d] Data = d . mut ; let q : mut [p] Data = p . mut ; p . ref . read [ref [p] Data] () ; q . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let p : mut [d] Data = d . mut ;, let q : mut [p] Data = p . mut ;, p . ref . read [ref [p] Data] () ;, q . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let q : mut [p] Data = p . mut ;, p . ref . read [ref [p] Data] () ;, q . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data, p: mut [d] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [p . ref . read [ref [p] Data] () ;, q . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: p . ref . read [ref [p] Data] () ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {q}, traversed: {} } }` failed at the following rule(s):
                                             the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: p . ref . read [ref [p] Data] (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {q}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "call" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: p . ref, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {q}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: ref, place: p, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {q}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `env_permits_access { access: ref, place: p, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {q}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `parameters_permit_access { parameters: [mut [p] Data], access: ref, place: p, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `parameter_permits_access { parameter: mut [p] Data, access: ref, place: p, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `"flat_map"` failed at the following rule(s):
                                                                         failed at (src/file.rs:LL:CC) because
                                                                           judgment `lien_permit_access { lien: mt(p), access: ref, accessed_place: p, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "leased" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `leased_place_permits_access { leased_place: p, access: ref, accessed_place: p }` failed at the following rule(s):
                                                                                 the rule "lease-mutation" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                                                                                     &accessed_place = p
                                                                                     &leased_place = p"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_leased_P_leased_P_data_to_P_data() {
    check_program(&term(
        "
        class Data {
        }
        class Main {
            fn test[perm P](my self, data: P Data) -> P Data
            where
                unique(P),
                lent(P),
            {
                let p: mut[data] Data = data.mut;
                p.move;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn forall_leased_P_shared_P_data_to_our_P_data() {
    check_program(&term(
        "
        class Data {
        }
        class Main {
            fn test[perm P](my self, data: P Data) -> our P Data
            where
                unique(P),
                lent(P),
            {
                let p: ref[data] Data = data.ref;
                p.move;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn forall_shared_P_shared_P_data_to_our_P_data() {
    check_program(&term(
        "
        class Data {
        }
        class Main {
            fn test[perm P](my self, data: P Data) -> our P Data
            where
                shared(P),
            {
                let p: ref[data] Data = data.ref;
                p.move;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}
