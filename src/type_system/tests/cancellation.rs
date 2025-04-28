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
                                                           judgment `sub_perms_both_ways { a: ref [p], b: our mut [d], live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `sub_red_perms { perm_a: ref [p], perm_b: our mut [d], live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "sub_red_perms" failed at step #2 (src/file.rs:LL:CC) because
                                                                   judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Rfl(p), Mtd(d)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Our, Mtd(d)] }} }, live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "sub_red_perms" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Rfl(p), Mtd(d)] }, red_chain_b: RedChain { links: [Our, Mtd(d)] }, live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "our vs shared" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_is_our { a: ref [p], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "prove" failed at step #1 (src/file.rs:LL:CC) because
                                                                               judgment `prove_is_owned { a: ref [p], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `prove_predicate { predicate: owned(ref [p]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       pattern `true` did not match value `false`
                                                                         the rule "ref vs our mut" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                                                             place_b = d
                                                                             &place_a = p"#]]);
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
                                                           judgment `sub_perms_both_ways { a: mut [p], b: mut [d], live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `sub_red_perms { perm_a: mut [p], perm_b: mut [d], live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "sub_red_perms" failed at step #2 (src/file.rs:LL:CC) because
                                                                   judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Mtl(p), Mtd(d)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Mtd(d)] }} }, live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "sub_red_perms" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtl(p), Mtd(d)] }, red_chain_b: RedChain { links: [Mtd(d)] }, live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "mut vs mut" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                                                             place_b = d
                                                                             &place_a = p
                                                                         the rule "our vs shared" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_is_our { a: mut [p], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "prove" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_is_shared { a: mut [p], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `prove_predicate { predicate: shared(mut [p]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
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
                                                     the rule "ref|mut place" failed at step #0 (src/file.rs:LL:CC) because
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
                                                                             the rule "mut'd" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `mut_place_permits_access { leased_place: p, access: ref, accessed_place: p }` failed at the following rule(s):
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
fn forall_shared_P_ref_P_data_to_our_P_data() {
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

#[test]
#[allow(non_snake_case)]
fn foo_bar_baz() {
    // Can coerce from `mut[p] mut[d]` to `mut[d]`
    // because `p` is dead.
    check_program(&term(
        "
        class Pair[ty A, ty B] {
            a: A;
            b: B;
        }
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test[perm Q, perm R](
              my self, 
              pair: Pair[Q Data, R Data],
              data: mut[pair] Q Data,
            )
            where
                unique(Q), lent(Q),
                unique(R), lent(R),
            {
                let data2: Q Data = data.move;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect![["()"]]);
}
