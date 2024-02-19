use crate::{dada_lang::term, type_system::check_program};
use formality_core::{test, test_util::ResultTestExt};

#[test]
#[allow(non_snake_case)]
fn create_PairSh_with_non_shared_type() {
    check_program(&term(
        "
        class Data {}
        class PairSh[ty T]
        where
            shared(T),
        {
        }
        class Main {
            fn test(my self) {
                new PairSh[Data]();
                ();
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class PairSh [ty] where shared(^ty0_0) { } class Main { fn test (my self) -> () { new PairSh [Data] () ; () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { new PairSh [Data] () ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { new PairSh [Data] () ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { new PairSh [Data] () ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { new PairSh [Data] () ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [new PairSh [Data] () ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: new PairSh [Data] () ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr { expr: new PairSh [Data] (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "new" failed at step #4 (src/file.rs:LL:CC) because
                                           judgment `prove_predicates { predicate: [shared(Data)], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "prove_predicates" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: shared(Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "shared" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `is_shared { a: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "is_shared" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment had no applicable rules: `lien_chain_is_shared { chain: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn take_PairSh_with_non_shared_type() {
    check_program(&term(
        "
        class Data {}
        class PairSh[ty T]
        where
            shared(T),
        {
        }
        class Main {
            fn test(my self, input: PairSh[Data]) {
                ();
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class PairSh [ty] where shared(^ty0_0) { } class Main { fn test (my self input : PairSh[Data]) -> () { () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check type `PairSh[Data]`
            3: judgment `prove_predicate { predicate: shared(Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, input: PairSh[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                 the rule "shared" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `is_shared { a: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, input: PairSh[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                     the rule "is_shared" failed at step #1 (src/file.rs:LL:CC) because
                       judgment had no applicable rules: `lien_chain_is_shared { chain: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, input: PairSh[Data]}, assumptions: {}, fresh: 0 } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn take_PairSh_with_shared_type() {
    check_program(&term(
        "
        class Data {}
        class PairSh[ty T]
        where
            shared(T),
        {
        }
        class Main {
            fn test(my self, input: PairSh[our Data]) {
                ();
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect![["()"]]);
}
