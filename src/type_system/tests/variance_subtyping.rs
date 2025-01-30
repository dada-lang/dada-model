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
                d1.give;
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
                d1.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Cell [ty] where atomic(^ty0_0) { atomic f : ^ty0_0 ; } class Main { fn test (my self d1 : our Cell[Data]) -> our Cell[our Data] { d1 . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d1 . give ; }, as_ty: our Cell[our Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . give ; }, as_ty: our Cell[our Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: our Cell[Data], b: our Cell[our Data], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under { cx_a: {}, a: our Cell[Data], cx_b: {}, b: our Cell[our Data], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_some { lien_data_a: LienData { liens: {Copy}, data: NamedTy(Cell[Data]) }, lien_datas_b: {LienData { liens: {Copy}, data: NamedTy(Cell[our Data]) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_lien_data { lien_data_a: LienData { liens: {Copy}, data: NamedTy(Cell[Data]) }, lien_data_b: LienData { liens: {Copy}, data: NamedTy(Cell[our Data]) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #7 (src/file.rs:LL:CC) because
                                       judgment `sub_generic_parameter { variances: [atomic], a: Data, b: our Data, liens_a: {Copy}, liens_b: {Copy}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "invariant" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `sub { a: our Data, b: Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `sub_under { cx_a: {}, a: our Data, cx_b: {}, b: Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `sub_some { lien_data_a: LienData { liens: {Copy}, data: NamedTy(Data) }, lien_datas_b: {LienData { liens: {}, data: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `sub_lien_data { lien_data_a: LienData { liens: {Copy}, data: NamedTy(Data) }, lien_data_b: LienData { liens: {}, data: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                                           judgment `sub_lien_sets { liens_a: {Copy}, liens_b: {}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `sub_some_lien { lien_a: Copy, liens_b: {}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                                                   expression evaluated to an empty collection: `&liens_b`"#]]);
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
                d1.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Cell [ty] where relative(^ty0_0) { } class Main { fn test (my self d1 : our Cell[Data]) -> our Cell[our Data] { d1 . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d1 . give ; }, as_ty: our Cell[our Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . give ; }, as_ty: our Cell[our Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: our Cell[Data], b: our Cell[our Data], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under { cx_a: {}, a: our Cell[Data], cx_b: {}, b: our Cell[our Data], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_some { lien_data_a: LienData { liens: {Copy}, data: NamedTy(Cell[Data]) }, lien_datas_b: {LienData { liens: {Copy}, data: NamedTy(Cell[our Data]) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_lien_data { lien_data_a: LienData { liens: {Copy}, data: NamedTy(Cell[Data]) }, lien_data_b: LienData { liens: {Copy}, data: NamedTy(Cell[our Data]) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #7 (src/file.rs:LL:CC) because
                                       judgment `sub_generic_parameter { variances: [relative], a: Data, b: our Data, liens_a: {Copy}, liens_b: {Copy}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "invariant" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `sub { a: our Data, b: Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `sub_under { cx_a: {}, a: our Data, cx_b: {}, b: Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `sub_some { lien_data_a: LienData { liens: {Copy}, data: NamedTy(Data) }, lien_datas_b: {LienData { liens: {}, data: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `sub_lien_data { lien_data_a: LienData { liens: {Copy}, data: NamedTy(Data) }, lien_data_b: LienData { liens: {}, data: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                                           judgment `sub_lien_sets { liens_a: {Copy}, liens_b: {}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `sub_some_lien { lien_a: Copy, liens_b: {}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Cell[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                                                   expression evaluated to an empty collection: `&liens_b`"#]]);
}
