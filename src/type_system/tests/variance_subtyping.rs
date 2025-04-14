use crate::{dada_lang::term, type_system::check_program};
use formality_core::{test, test_util::ResultTestExt};

#[test]
#[allow(non_snake_case)]
fn Cell_T_our_Cell_Data_to_our_Cell_our_Data() {
    check_program(&term(
        "
        class Data {}
        class Cell[ty T]
        {
            f: T;
        }
        class Main {
            fn test(my self, d1: our Cell[Data]) -> our Cell[our Data] {
                d1.move;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect![["()"]]);
}

#[test]
#[allow(non_snake_case)]
fn Cell_atomic_T_our_Cell_Data_to_our_Cell_our_Data() {
    // Since T is atomic(T), we can't convert `our Cell[Data]` to `our Cell[our Data]`.
    check_program(&term(
        "
        class Data {}
        class Cell[ty T]
        where
            atomic(T),
        {
            atomic f: T;
        }
        class Main {
            fn test(my self, d1: our Cell[Data]) -> our Cell[our Data] {
                d1.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Cell [ty] where atomic(^ty0_0) { atomic f : ^ty0_0 ; } class Main { fn test (my self d1 : our Cell[Data]) -> our Cell[our Data] { d1 . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d1 . move ; }, as_ty: our Cell[our Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . move ; }, as_ty: our Cell[our Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: our Cell[Data], b: our Cell[our Data], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub-classes" failed at step #7 (src/file.rs:LL:CC) because
                           judgment `sub_generic_parameter { perm_a: our, a: Data, perm_b: our, b: our Data, variances: [atomic], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "invariant" failed at step #1 (src/file.rs:LL:CC) because
                               judgment `sub { a: our Data, b: Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                   judgment `sub_perms { a: our, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `prove_is_move { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `prove_predicate { predicate: move(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                               pattern `true` did not match value `false`
                                     the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `prove_is_move { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `prove_predicate { predicate: move(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                               pattern `true` did not match value `false`
                                     the rule "our-sub-copy" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `prove_is_copy { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `prove_predicate { predicate: copy(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                               pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn Cell_rel_T_our_Cell_Data_to_our_Cell_our_Data() {
    // Since T is relative(T), we can't convert `our Cell[Data]` to `our Cell[our Data]`.
    check_program(&term(
        "
        class Data {}
        class Cell[ty T]
        where
            relative(T),
        {
        }
        class Main {
            fn test(my self, d1: our Cell[Data]) -> our Cell[our Data] {
                d1.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Cell [ty] where relative(^ty0_0) { } class Main { fn test (my self d1 : our Cell[Data]) -> our Cell[our Data] { d1 . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d1 . move ; }, as_ty: our Cell[our Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . move ; }, as_ty: our Cell[our Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: our Cell[Data], b: our Cell[our Data], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub-classes" failed at step #7 (src/file.rs:LL:CC) because
                           judgment `sub_generic_parameter { perm_a: our, a: Data, perm_b: our, b: our Data, variances: [relative], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "invariant" failed at step #1 (src/file.rs:LL:CC) because
                               judgment `sub { a: our Data, b: Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                   judgment `sub_perms { a: our, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `prove_is_move { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `prove_predicate { predicate: move(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                               pattern `true` did not match value `false`
                                     the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `prove_is_move { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `prove_predicate { predicate: move(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                               pattern `true` did not match value `false`
                                     the rule "our-sub-copy" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `prove_is_copy { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `prove_predicate { predicate: copy(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                               pattern `true` did not match value `false`"#]]);
}
