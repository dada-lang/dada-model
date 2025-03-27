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
            0: check class named `Data`
            1: check method named `read`
            2: check function body
            3: judgment `can_type_expr_as { expr: { () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [() ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: () ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "expr" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `parameter_permits_access { parameter: (), access: drop, place: @ fresh(0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data, @ fresh(0): ()}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `liens { a: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data, @ fresh(0): ()}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                             the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `some_lien { a: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data, @ fresh(0): ()}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                                 the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                   expression evaluated to an empty collection: `parameters`"#]]);
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
            0: check class named `Data`
            1: check method named `read`
            2: check function body
            3: judgment `can_type_expr_as { expr: { () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [() ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: () ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "expr" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `parameter_permits_access { parameter: (), access: drop, place: @ fresh(0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data, @ fresh(0): ()}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `liens { a: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data, @ fresh(0): ()}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                             the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `some_lien { a: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data, @ fresh(0): ()}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                                 the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                   expression evaluated to an empty collection: `parameters`"#]]);
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
            0: check class named `Data`
            1: check method named `read`
            2: check function body
            3: judgment `can_type_expr_as { expr: { () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [() ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: () ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "expr" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `parameter_permits_access { parameter: (), access: drop, place: @ fresh(0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data, @ fresh(0): ()}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `liens { a: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data, @ fresh(0): ()}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                             the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `some_lien { a: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data, @ fresh(0): ()}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                                 the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                   expression evaluated to an empty collection: `parameters`"#]]);
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
