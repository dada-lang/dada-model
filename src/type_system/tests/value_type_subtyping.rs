use crate::{dada_lang::term, type_system::check_program};
use formality_core::{test, test_util::ResultTestExt};

#[test]
#[allow(non_snake_case)]
fn pair_my_Data_my_Data_to_pair_my_Data_my_Data() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self, d1: (my Data, my Data)) -> (my Data, my Data) {
                d1.move;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn pair_our_Data_our_Data_to_pair_my_Data_my_Data() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self, d1: (our Data, our Data)) -> (my Data, my Data) {
                d1.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self d1 : (our Data, our Data)) -> (my Data, my Data) { d1 . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d1 . move ; }, as_ty: (my Data, my Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . move ; }, as_ty: (my Data, my Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: (our Data, our Data), b: (my Data, my Data), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub-classes" failed at step #7 (src/file.rs:LL:CC) because
                           judgment `sub_generic_parameter { perm_a: my, a: our Data, perm_b: my, b: my Data, variances: [], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "covariant-copy" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                       pattern `true` did not match value `false`
                             the rule "covariant-owned" failed at step #1 (src/file.rs:LL:CC) because
                               judgment `sub { a: my our Data, b: my my Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                   judgment `sub_perms_both_ways { a: my our, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `sub_red_perms { perm_a: my our, perm_b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "sub_red_perms" failed at step #3 (src/file.rs:LL:CC) because
                                           judgment `sub_some_perm { a: our, bs: {my}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "apply to shared, left" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `sub_perms { a: our, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "our left" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                           pattern `true` did not match value `false`
                                                 the rule "our left" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                           pattern `true` did not match value `false`
                             the rule "invariant" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `sub { a: our Data, b: my Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                   judgment `sub_perms_both_ways { a: our, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `sub_red_perms { perm_a: our, perm_b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "sub_red_perms" failed at step #3 (src/file.rs:LL:CC) because
                                           judgment `sub_some_perm { a: our, bs: {my}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "apply to shared, left" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `sub_perms { a: our, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "our left" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                           pattern `true` did not match value `false`
                                                 the rule "our left" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                           pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn our_pair_Data_Data_to_pair_Data_Data() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self, d1: our (Data, Data)) -> (Data, Data) {
                d1.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self d1 : our (Data, Data)) -> (Data, Data) { d1 . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d1 . move ; }, as_ty: (Data, Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . move ; }, as_ty: (Data, Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: our (Data, Data), b: (Data, Data), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                           judgment `sub_perms_both_ways { a: our, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `sub_red_perms { perm_a: our, perm_b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub_red_perms" failed at step #3 (src/file.rs:LL:CC) because
                                   judgment `sub_some_perm { a: our, bs: {my}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "apply to shared, left" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `sub_perms { a: our, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "our left" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                   pattern `true` did not match value `false`
                                         the rule "our left" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                   pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn our_pair_Data_Data_to_my_pair_Data_Data() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self, d1: our (Data, Data)) -> my (Data, Data) {
                d1.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self d1 : our (Data, Data)) -> my (Data, Data) { d1 . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d1 . move ; }, as_ty: my (Data, Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . move ; }, as_ty: my (Data, Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: our (Data, Data), b: my (Data, Data), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                           judgment `sub_perms_both_ways { a: our, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `sub_red_perms { perm_a: our, perm_b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub_red_perms" failed at step #3 (src/file.rs:LL:CC) because
                                   judgment `sub_some_perm { a: our, bs: {my}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "apply to shared, left" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `sub_perms { a: our, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "our left" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                   pattern `true` did not match value `false`
                                         the rule "our left" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                   pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn my_pair_Data_Data_share_to_our_pair_Data_Data() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self, d1: my (Data, Data)) -> our (Data, Data) {
                d1.share;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}
