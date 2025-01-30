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
                let m: PermData[my] = data.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn PermDataMy_is_subtype_of_PermDataOur() {
    check_program(&term(
        "
        class Data { }

        class PermData[perm P] {
            data: P Data;
        }

        class Main {
            fn test(my self, data: PermData[my]) {
                let m: PermData[our] = data.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
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
                let m: PermData[leased[d]] = data.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class PermData [perm] { data : ^perm0_0 Data ; } class Main { fn test (my self data : PermData[my]) -> () { let d = new Data () ; let m : PermData[leased [d]] = data . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d = new Data () ; let m : PermData[leased [d]] = data . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d = new Data () ; let m : PermData[leased [d]] = data . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d = new Data () ; let m : PermData[leased [d]] = data . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d = new Data () ; let m : PermData[leased [d]] = data . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d = new Data () ;, let m : PermData[leased [d]] = data . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let m : PermData[leased [d]] = data . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let m : PermData[leased [d]] = data . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr_as { expr: data . give, as_ty: PermData[leased [d]], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `sub { a: PermData[my], b: PermData[leased [d]], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `sub_under { cx_a: {}, a: PermData[my], cx_b: {}, b: PermData[leased [d]], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                       judgment `sub_some { lien_data_a: LienData { liens: {}, data: NamedTy(PermData[my]) }, lien_datas_b: {LienData { liens: {}, data: NamedTy(PermData[leased [d]]) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `sub_lien_data { lien_data_a: LienData { liens: {}, data: NamedTy(PermData[my]) }, lien_data_b: LienData { liens: {}, data: NamedTy(PermData[leased [d]]) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub-named" failed at step #7 (src/file.rs:LL:CC) because
                                                               judgment `sub_generic_parameter { variances: [], a: my, b: leased [d], liens_a: {}, liens_b: {}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "covariant-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `lien_set_is_copy { liens: {}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "some" failed at step #0 (src/file.rs:LL:CC) because
                                                                       expression evaluated to an empty collection: `&liens`
                                                                 the rule "covariant-owned" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `sub_under { cx_a: {}, a: my, cx_b: {}, b: leased [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                                       judgment `sub_some { lien_data_a: LienData { liens: {}, data: None }, lien_datas_b: {LienData { liens: {Lent, Leased(d)}, data: None }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                                           judgment `sub_lien_data { lien_data_a: LienData { liens: {}, data: None }, lien_data_b: LienData { liens: {Lent, Leased(d)}, data: None }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "sub-no-data" failed at step #2 (src/file.rs:LL:CC) because
                                                                               judgment `sub_lien_sets { liens_a: {}, liens_b: {Lent, Leased(d)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                                                   judgment `layout_compatible { liens_a: {}, liens_b: {Lent, Leased(d)}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "by value" failed at step #1 (src/file.rs:LL:CC) because
                                                                                       condition evaluted to false: `liens_b.is_copy(&env) || liens_b.is_owned(&env)`
                                                                                     the rule "leased" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       condition evaluted to false: `liens_a.is_leased(&env)`
                                                                                         liens_a = {}
                                                                                         &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 }
                                                                 the rule "invariant" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `sub { a: my, b: leased [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `sub_under { cx_a: {}, a: my, cx_b: {}, b: leased [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                                           judgment `sub_some { lien_data_a: LienData { liens: {}, data: None }, lien_datas_b: {LienData { liens: {Lent, Leased(d)}, data: None }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                                               judgment `sub_lien_data { lien_data_a: LienData { liens: {}, data: None }, lien_data_b: LienData { liens: {Lent, Leased(d)}, data: None }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "sub-no-data" failed at step #2 (src/file.rs:LL:CC) because
                                                                                   judgment `sub_lien_sets { liens_a: {}, liens_b: {Lent, Leased(d)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                                                       judgment `layout_compatible { liens_a: {}, liens_b: {Lent, Leased(d)}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                         the rule "by value" failed at step #1 (src/file.rs:LL:CC) because
                                                                                           condition evaluted to false: `liens_b.is_copy(&env) || liens_b.is_owned(&env)`
                                                                                         the rule "leased" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           condition evaluted to false: `liens_a.is_leased(&env)`
                                                                                             liens_a = {}
                                                                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 }"#]]);
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
                let m: PermData[shared[d]] = data.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}
