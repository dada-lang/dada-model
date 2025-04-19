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
            0: check class named `Data`
            1: check method named `read`
            2: check function body
            3: judgment `can_type_expr_as { expr: { () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: (), b: (), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                           judgment `sub_perms { a: my, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "apply to shared" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
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
            0: check class named `Data`
            1: check method named `read`
            2: check function body
            3: judgment `can_type_expr_as { expr: { () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: (), b: (), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                           judgment `sub_perms { a: my, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "apply to shared" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
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
            0: check class named `Data`
            1: check method named `read`
            2: check function body
            3: judgment `can_type_expr_as { expr: { () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: (), b: (), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                           judgment `sub_perms { a: my, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "apply to shared" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                       pattern `true` did not match value `false`"#]]);
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
