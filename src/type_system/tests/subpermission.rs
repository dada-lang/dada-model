//! Tests for subpermissions.
//!
//! Perm P is a *subpermission* of perm Q when `P T` is a subtype of `Q T` for all types `T`.

use crate::{dada_lang::term, type_system::check_program};
use formality_core::{test, test_util::ResultTestExt};

#[test]
#[allow(non_snake_case)]
fn PermDataMy_is_subtype_of_PermDataMy() {
    check_program(&term(
        "
        class Data { }

        class PermData[perm P] {
            data: P Data;
        }

        class Main {
            fn test(my self, data: PermData[my]) {
                let m: PermData[my] = data.move;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn PermDataMy_not_subtype_of_PermDataOur() {
    check_program(&term(
        "
        class Data { }

        class PermData[perm P] {
            data: P Data;
        }

        class Main {
            fn test(my self, data: PermData[my]) {
                let m: PermData[our] = data.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class PermData [perm] { data : ^perm0_0 Data ; } class Main { fn test (my self data : PermData[my]) -> () { let m : PermData[our] = data . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : PermData[our] = data . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : PermData[our] = data . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : PermData[our] = data . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : PermData[our] = data . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : PermData[our] = data . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: let m : PermData[our] = data . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr_as { expr: data . move, as_ty: PermData[our], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `sub { a: PermData[my], b: PermData[our], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub-classes" failed at step #7 (src/file.rs:LL:CC) because
                                               judgment `sub_generic_parameter { perm_a: my, a: my, perm_b: my, b: our, variances: [], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "covariant-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                           pattern `true` did not match value `false`
                                                 the rule "covariant-owned" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `sub { a: my my, b: my our, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `sub_perms_both_ways { a: my my, b: my our, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `sub_perms { a: my my, b: my our, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "match heads" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `sub_perms { a: my, b: our, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "my left" failed at step #2 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_unique { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: unique(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                 the rule "invariant" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `sub { a: my, b: our, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `sub_perms_both_ways { a: my, b: our, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `sub_perms { a: my, b: our, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "my left" failed at step #2 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_unique { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: unique(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn PermDataMy_is_not_subtype_of_PermDataLeased() {
    check_program(&term(
        "
        class Data { }

        class PermData[perm P] {
            data: P Data;
        }

        class Main {
            fn test(my self, data: PermData[my]) {
                let d = new Data();
                let m: PermData[mut[d]] = data.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class PermData [perm] { data : ^perm0_0 Data ; } class Main { fn test (my self data : PermData[my]) -> () { let d = new Data () ; let m : PermData[mut [d]] = data . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d = new Data () ; let m : PermData[mut [d]] = data . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d = new Data () ; let m : PermData[mut [d]] = data . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d = new Data () ; let m : PermData[mut [d]] = data . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d = new Data () ; let m : PermData[mut [d]] = data . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d = new Data () ;, let m : PermData[mut [d]] = data . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let m : PermData[mut [d]] = data . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let m : PermData[mut [d]] = data . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr_as { expr: data . move, as_ty: PermData[mut [d]], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `sub { a: PermData[my], b: PermData[mut [d]], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub-classes" failed at step #7 (src/file.rs:LL:CC) because
                                                   judgment `sub_generic_parameter { perm_a: my, a: my, perm_b: my, b: mut [d], variances: [], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "covariant-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                               pattern `true` did not match value `false`
                                                     the rule "covariant-owned" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `sub { a: my my, b: my mut [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `sub_perms_both_ways { a: my my, b: my mut [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `sub_perms { a: my my, b: my mut [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "apply to shared, right" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_shared { a: mut [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: shared(mut [d]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                                 the rule "match heads" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `sub_perms { a: my, b: mut [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "expand right" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `sub_perms { a: my, b: mut [d] my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "my left" failed at step #3 (src/file.rs:LL:CC) because
                                                                           judgment `prove_is_owned { a: mut [d] my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_predicate { predicate: owned(mut [d] my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   pattern `true` did not match value `false`
                                                                     the rule "my left" failed at step #3 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_owned { a: mut [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: owned(mut [d]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`
                                                     the rule "invariant" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `sub { a: my, b: mut [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `sub_perms_both_ways { a: my, b: mut [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `sub_perms { a: my, b: mut [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "expand right" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `sub_perms { a: my, b: mut [d] my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "my left" failed at step #3 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_owned { a: mut [d] my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: owned(mut [d] my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`
                                                                 the rule "my left" failed at step #3 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_owned { a: mut [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: owned(mut [d]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn PermDataMy_is_not_subtype_of_PermDataShared() {
    check_program(&term(
        "
        class Data { }

        class PermData[perm P] {
            data: P Data;
        }

        class Main {
            fn test(my self, data: PermData[my]) {
                let d = new Data();
                let m: PermData[ref[d]] = data.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class PermData [perm] { data : ^perm0_0 Data ; } class Main { fn test (my self data : PermData[my]) -> () { let d = new Data () ; let m : PermData[ref [d]] = data . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d = new Data () ; let m : PermData[ref [d]] = data . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d = new Data () ; let m : PermData[ref [d]] = data . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d = new Data () ; let m : PermData[ref [d]] = data . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d = new Data () ; let m : PermData[ref [d]] = data . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d = new Data () ;, let m : PermData[ref [d]] = data . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let m : PermData[ref [d]] = data . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let m : PermData[ref [d]] = data . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr_as { expr: data . move, as_ty: PermData[ref [d]], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `sub { a: PermData[my], b: PermData[ref [d]], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub-classes" failed at step #7 (src/file.rs:LL:CC) because
                                                   judgment `sub_generic_parameter { perm_a: my, a: my, perm_b: my, b: ref [d], variances: [], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "covariant-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                               pattern `true` did not match value `false`
                                                     the rule "covariant-owned" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `sub { a: my my, b: my ref [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `sub_perms_both_ways { a: my my, b: my ref [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `sub_perms { a: my my, b: my ref [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "match heads" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `sub_perms { a: my, b: ref [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "expand right" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `sub_perms { a: my, b: ref [d] my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "my left" failed at step #2 (src/file.rs:LL:CC) because
                                                                           judgment `prove_is_unique { a: ref [d] my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_predicate { predicate: unique(ref [d] my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   pattern `true` did not match value `false`
                                                                     the rule "my left" failed at step #2 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_unique { a: ref [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: unique(ref [d]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`
                                                     the rule "invariant" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `sub { a: my, b: ref [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `sub_perms_both_ways { a: my, b: ref [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `sub_perms { a: my, b: ref [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "expand right" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `sub_perms { a: my, b: ref [d] my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "my left" failed at step #2 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_unique { a: ref [d] my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: unique(ref [d] my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`
                                                                 the rule "my left" failed at step #2 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_unique { a: ref [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: unique(ref [d]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn unsound_upgrade() {
    check_program(&term(
        "
        class Data {
            fn mutate[perm P](P self)
            where
                unique(P), lent(P),
            { }
        }

        class Query {
            data: our Data;
        }

        class Main {
            fn test(my self, q1: Query, q2: Query) {
                let a: mut[q1.data] Data = q1.data.mut;
                let b: mut[q1] Data = a.move;
                b.mut.mutate[mut[q1]]();
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { fn mutate [perm] (^perm0_0 self) -> () where unique(^perm0_0), lent(^perm0_0) { } } class Query { data : our Data ; } class Main { fn test (my self q1 : Query, q2 : Query) -> () { let a : mut [q1 . data] Data = q1 . data . mut ; let b : mut [q1] Data = a . move ; b . mut . mutate [mut [q1]] () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let a : mut [q1 . data] Data = q1 . data . mut ; let b : mut [q1] Data = a . move ; b . mut . mutate [mut [q1]] () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let a : mut [q1 . data] Data = q1 . data . mut ; let b : mut [q1] Data = a . move ; b . mut . mutate [mut [q1]] () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let a : mut [q1 . data] Data = q1 . data . mut ; let b : mut [q1] Data = a . move ; b . mut . mutate [mut [q1]] () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let a : mut [q1 . data] Data = q1 . data . mut ; let b : mut [q1] Data = a . move ; b . mut . mutate [mut [q1]] () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let a : mut [q1 . data] Data = q1 . data . mut ;, let b : mut [q1] Data = a . move ;, b . mut . mutate [mut [q1]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let b : mut [q1] Data = a . move ;, b . mut . mutate [mut [q1]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let b : mut [q1] Data = a . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {b}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr_as { expr: a . move, as_ty: mut [q1] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `sub { a: mut [q1 . data] Data, b: mut [q1] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                   judgment `sub_perms_both_ways { a: mut [q1 . data], b: mut [q1], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `sub_perms { a: mut [q1 . data], b: mut [q1], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "dead left" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `dead_perm { acc: mt, place: q1 . data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "dead mut" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_lent { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: lent(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`
                                                         the rule "expand left" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `sub_perms { a: mut [q1 . data] our, b: mut [q1], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "apply to shared, left" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `sub_perms { a: our, b: mut [q1], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "expand right" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `sub_perms { a: our, b: mut [q1] my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "our left" failed at step #2 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_shared { a: mut [q1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: shared(mut [q1]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`
                                                                     the rule "our left" failed at step #2 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_shared { a: mut [q1] my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: shared(mut [q1] my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`
                                                                 the rule "our left" failed at step #2 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_shared { a: mut [q1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: shared(mut [q1]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                                 the rule "our left" failed at step #2 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_shared { a: mut [q1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: shared(mut [q1]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                             the rule "dead left" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `dead_perm { acc: mt, place: q1 . data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "dead mut" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_lent { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: lent(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                             the rule "expand right" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `sub_perms { a: mut [q1 . data] our, b: mut [q1] my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "apply to shared, left" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `sub_perms { a: our, b: mut [q1] my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "our left" failed at step #2 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_shared { a: mut [q1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: shared(mut [q1]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`
                                                                     the rule "our left" failed at step #2 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_shared { a: mut [q1] my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: shared(mut [q1] my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`
                                                                 the rule "dead left" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `dead_perm { acc: mt, place: q1 . data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "dead mut" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_lent { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: lent(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`
                                                                 the rule "our left" failed at step #2 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_shared { a: mut [q1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: shared(mut [q1]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                                 the rule "pop field" failed at step #3 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_unique { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: unique(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                             the rule "our left" failed at step #2 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_shared { a: mut [q1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: shared(mut [q1]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`
                                                             the rule "pop field" failed at step #3 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_unique { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: unique(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`
                                                         the rule "expand right" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `sub_perms { a: mut [q1 . data], b: mut [q1] my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "dead left" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `dead_perm { acc: mt, place: q1 . data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "dead mut" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_lent { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: lent(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                             the rule "expand left" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `sub_perms { a: mut [q1 . data] our, b: mut [q1] my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "apply to shared, left" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `sub_perms { a: our, b: mut [q1] my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "our left" failed at step #2 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_shared { a: mut [q1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: shared(mut [q1]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`
                                                                     the rule "our left" failed at step #2 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_shared { a: mut [q1] my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: shared(mut [q1] my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`
                                                                 the rule "dead left" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `dead_perm { acc: mt, place: q1 . data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "dead mut" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_lent { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: lent(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`
                                                                 the rule "our left" failed at step #2 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_shared { a: mut [q1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: shared(mut [q1]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                                 the rule "pop field" failed at step #3 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_unique { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: unique(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                             the rule "our left" failed at step #2 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_shared { a: mut [q1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: shared(mut [q1]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`
                                                             the rule "pop field" failed at step #3 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_unique { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: unique(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`
                                                         the rule "our left" failed at step #2 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_shared { a: mut [q1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: shared(mut [q1]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`
                                                         the rule "pop field" failed at step #3 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_unique { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: unique(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_exists() {
    check_program(&term(
        "
        class Query {
        }

        class Main {
            fn test(my self, q1: Query, q2: Query) {
                let a: ref[q1] Query = q1.ref;
                let b: ref[q2] Query = q2.ref;
                let c: ref[a] ref[q1] Query = a.ref;
                let d: ref[b] ref[q2] Query = b.ref;
                let x: ref[a, b] Query = c.move;
                let y: ref[a, b] Query = d.move;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}
