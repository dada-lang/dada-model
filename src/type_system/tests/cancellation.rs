use crate::{dada_lang::term, type_system::check_program};
use formality_core::{test, test_util::ResultTestExt};

#[test]
#[allow(non_snake_case)]
fn shared_dead_leased_to_our_leased() {
    check_program(&term(
        "
        class Data {
            fn read[perm P](P self) where copy(P) {
                ();
            }
        }
        class Main {
            fn test(my self) {
                let d = new Data();
                let p: leased[d] Data = d.lease;
                let q: shared[p] Data = p.share;
                let r: our leased[d] Data = q.give;
                r.give.read[our leased[d]]();
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect![["()"]]);
}

#[test]
#[allow(non_snake_case)]
fn shared_live_leased_to_our_leased() {
    // Cannot coerce from `shared[p] leased[d]` to `our leased[d]`
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
                let p: leased[d] Data = d.lease;
                let q: shared[p] Data = p.share;
                let r: our leased[d] Data = q.give;
                p.give.read[leased[d]]();
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { fn read [perm] (^perm0_0 self) -> () { () ; } } class Main { fn test (my self) -> () { let d = new Data () ; let p : leased [d] Data = d . lease ; let q : shared [p] Data = p . share ; let r : our leased [d] Data = q . give ; p . give . read [leased [d]] () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d = new Data () ; let p : leased [d] Data = d . lease ; let q : shared [p] Data = p . share ; let r : our leased [d] Data = q . give ; p . give . read [leased [d]] () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d = new Data () ; let p : leased [d] Data = d . lease ; let q : shared [p] Data = p . share ; let r : our leased [d] Data = q . give ; p . give . read [leased [d]] () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d = new Data () ; let p : leased [d] Data = d . lease ; let q : shared [p] Data = p . share ; let r : our leased [d] Data = q . give ; p . give . read [leased [d]] () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d = new Data () ; let p : leased [d] Data = d . lease ; let q : shared [p] Data = p . share ; let r : our leased [d] Data = q . give ; p . give . read [leased [d]] () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d = new Data () ;, let p : leased [d] Data = d . lease ;, let q : shared [p] Data = p . share ;, let r : our leased [d] Data = q . give ;, p . give . read [leased [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : leased [d] Data = d . lease ;, let q : shared [p] Data = p . share ;, let r : our leased [d] Data = q . give ;, p . give . read [leased [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let q : shared [p] Data = p . share ;, let r : our leased [d] Data = q . give ;, p . give . read [leased [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let r : our leased [d] Data = q . give ;, p . give . read [leased [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data, q: shared [p] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let r : our leased [d] Data = q . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data, q: shared [p] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr_as { expr: q . give, as_ty: our leased [d] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data, q: shared [p] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `sub { a: shared [p] Data, b: our leased [d] Data, live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data, q: shared [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: shared [p] Data, chain_b: Chain { liens: [] }, b: our leased [d] Data, live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data, q: shared [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                               judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Shared(p), Leased(d)] }, ty: NamedTy(Data) }, ty_chains_b: {TyChain { chain: Chain { liens: [Our, Leased(d)] }, ty: NamedTy(Data) }}, live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data, q: shared [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Shared(p), Leased(d)] }, ty: NamedTy(Data) }, ty_chain_b: TyChain { chain: Chain { liens: [Our, Leased(d)] }, ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data, q: shared [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                                                       judgment `sub_chains { chain_a: Chain { liens: [Shared(p), Leased(d)] }, chain_b: Chain { liens: [Our, Leased(d)] }, live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data, q: shared [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                                                             chain_a = Chain { liens: [Shared(p), Leased(d)] }
                                                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data, q: shared [p] Data}, assumptions: {}, fresh: 0 }
                                                                         the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                                                             chain_a = Chain { liens: [Shared(p), Leased(d)] }
                                                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data, q: shared [p] Data}, assumptions: {}, fresh: 0 }
                                                                         the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                                                             chain_a = Chain { liens: [Shared(p), Leased(d)] }
                                                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data, q: shared [p] Data}, assumptions: {}, fresh: 0 }
                                                                         the rule "shared-dead" failed at step #2 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `!live_after.is_live(&place_a)`
                                                                             live_after = LivePlaces { accessed: {p}, traversed: {} }
                                                                             &place_a = p
                                                                         the rule "shared-vs-our-leased" failed at step #2 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                                                             place_b = d
                                                                             &place_a = p"#]]);
}

#[test]
#[allow(non_snake_case)]
fn leased_dead_leased_to_leased() {
    // Can coerce from `leased[p] leased[d]` to `leased[d]`
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
                let p: leased[d] Data = d.lease;
                let q: leased[p] Data = p.lease;
                let r: leased[d] Data = q.give;
                r.give.read[leased[d]]();
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect![["()"]]);
}

#[test]
#[allow(non_snake_case)]
fn leased_live_leased_to_leased() {
    // Cannot coerce from `leased[p] leased[d]` to `leased[d]`
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
                let p: leased[d] Data = d.lease;
                let q: leased[p] Data = p.lease;
                let r: leased[d] Data = q.give;
                p.give.read[leased[d]]();
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { fn read [perm] (^perm0_0 self) -> () { () ; } } class Main { fn test (my self) -> () { let d = new Data () ; let p : leased [d] Data = d . lease ; let q : leased [p] Data = p . lease ; let r : leased [d] Data = q . give ; p . give . read [leased [d]] () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d = new Data () ; let p : leased [d] Data = d . lease ; let q : leased [p] Data = p . lease ; let r : leased [d] Data = q . give ; p . give . read [leased [d]] () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d = new Data () ; let p : leased [d] Data = d . lease ; let q : leased [p] Data = p . lease ; let r : leased [d] Data = q . give ; p . give . read [leased [d]] () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d = new Data () ; let p : leased [d] Data = d . lease ; let q : leased [p] Data = p . lease ; let r : leased [d] Data = q . give ; p . give . read [leased [d]] () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d = new Data () ; let p : leased [d] Data = d . lease ; let q : leased [p] Data = p . lease ; let r : leased [d] Data = q . give ; p . give . read [leased [d]] () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d = new Data () ;, let p : leased [d] Data = d . lease ;, let q : leased [p] Data = p . lease ;, let r : leased [d] Data = q . give ;, p . give . read [leased [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : leased [d] Data = d . lease ;, let q : leased [p] Data = p . lease ;, let r : leased [d] Data = q . give ;, p . give . read [leased [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let q : leased [p] Data = p . lease ;, let r : leased [d] Data = q . give ;, p . give . read [leased [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let r : leased [d] Data = q . give ;, p . give . read [leased [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data, q: leased [p] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let r : leased [d] Data = q . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data, q: leased [p] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr_as { expr: q . give, as_ty: leased [d] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data, q: leased [p] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `sub { a: leased [p] Data, b: leased [d] Data, live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data, q: leased [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: leased [p] Data, chain_b: Chain { liens: [] }, b: leased [d] Data, live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data, q: leased [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                               judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Leased(p), Leased(d)] }, ty: NamedTy(Data) }, ty_chains_b: {TyChain { chain: Chain { liens: [Leased(d)] }, ty: NamedTy(Data) }}, live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data, q: leased [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Leased(p), Leased(d)] }, ty: NamedTy(Data) }, ty_chain_b: TyChain { chain: Chain { liens: [Leased(d)] }, ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data, q: leased [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                                                       judgment `sub_chains { chain_a: Chain { liens: [Leased(p), Leased(d)] }, chain_b: Chain { liens: [Leased(d)] }, live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data, q: leased [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "leased-dead" failed at step #2 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `!live_after.is_live(&place_a)`
                                                                             live_after = LivePlaces { accessed: {p}, traversed: {} }
                                                                             &place_a = p
                                                                         the rule "leased-vs-leased" failed at step #2 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                                                             place_b = d
                                                                             &place_a = p
                                                                         the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                                                             chain_a = Chain { liens: [Leased(p), Leased(d)] }
                                                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data, q: leased [p] Data}, assumptions: {}, fresh: 0 }
                                                                         the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                                                             chain_a = Chain { liens: [Leased(p), Leased(d)] }
                                                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data, q: leased [p] Data}, assumptions: {}, fresh: 0 }
                                                                         the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                                                             chain_a = Chain { liens: [Leased(p), Leased(d)] }
                                                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, p: leased [d] Data, q: leased [p] Data}, assumptions: {}, fresh: 0 }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn return_leased_dead_leased_to_leased() {
    // Equivalent of `fn test(my self, d: leased Data) -> leased[d] Data
    check_program(&term(
        "
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test[perm P](my self, d: P Data) -> leased[d] Data
            where
                move(P),
                lent(P),
            {
                let p: leased[d] Data = d.lease;
                let q: leased[p] Data = p.lease;
                q.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect![["()"]]);
}

#[test]
#[allow(non_snake_case)]
fn return_leased_dead_leased_to_leased_and_use_while_leased() {
    // Equivalent of `fn test(my self, d: leased Data) -> leased[d] Data
    check_program(&term(
        "
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test[perm P](my self, d: P Data) -> leased[d] Data
            where
                move(P),
                lent(P),
            {
                let p: leased[d] Data = d.lease;
                let q: leased[p] Data = p.lease;
                p.share.read[shared[p] Data]();
                q.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { fn read [perm] (^perm0_0 self) -> () { () ; } } class Main { fn test [perm] (my self d : ^perm0_0 Data) -> leased [d] Data where move(^perm0_0), lent(^perm0_0) { let p : leased [d] Data = d . lease ; let q : leased [p] Data = p . lease ; p . share . read [shared [p] Data] () ; q . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let p : leased [d] Data = d . lease ; let q : leased [p] Data = p . lease ; p . share . read [shared [p] Data] () ; q . give ; }, as_ty: leased [d] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let p : leased [d] Data = d . lease ; let q : leased [p] Data = p . lease ; p . share . read [shared [p] Data] () ; q . give ; }, as_ty: leased [d] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let p : leased [d] Data = d . lease ; let q : leased [p] Data = p . lease ; p . share . read [shared [p] Data] () ; q . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let p : leased [d] Data = d . lease ; let q : leased [p] Data = p . lease ; p . share . read [shared [p] Data] () ; q . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let p : leased [d] Data = d . lease ;, let q : leased [p] Data = p . lease ;, p . share . read [shared [p] Data] () ;, q . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let q : leased [p] Data = p . lease ;, p . share . read [shared [p] Data] () ;, q . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data, p: leased [d] Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [p . share . read [shared [p] Data] () ;, q . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data, p: leased [d] Data, q: leased [p] Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: p . share . read [shared [p] Data] () ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data, p: leased [d] Data, q: leased [p] Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {q}, traversed: {} } }` failed at the following rule(s):
                                             the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: p . share . read [shared [p] Data] (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data, p: leased [d] Data, q: leased [p] Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {q}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "call" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: p . share, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data, p: leased [d] Data, q: leased [p] Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {q}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: share, place: p, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data, p: leased [d] Data, q: leased [p] Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {q}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `env_permits_access { access: share, place: p, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data, p: leased [d] Data, q: leased [p] Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {q}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `parameters_permit_access { parameters: [leased [p] Data], access: share, place: p, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data, p: leased [d] Data, q: leased [p] Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `parameter_permits_access { parameter: leased [p] Data, access: share, place: p, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data, p: leased [d] Data, q: leased [p] Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `"flat_map"` failed at the following rule(s):
                                                                         failed at (src/file.rs:LL:CC) because
                                                                           judgment `lien_permit_access { lien: Leased(p), access: share, accessed_place: p, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: !perm_0 Data, p: leased [d] Data, q: leased [p] Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "leased" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `leased_place_permits_access { leased_place: p, access: share, accessed_place: p }` failed at the following rule(s):
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
                move(P),
                lent(P),
            {
                let p: leased[data] Data = data.lease;
                p.give;
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
                move(P),
                lent(P),
            {
                let p: shared[data] Data = data.share;
                p.give;
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
                copy(P),
            {
                let p: shared[data] Data = data.share;
                p.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}
