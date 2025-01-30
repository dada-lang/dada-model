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
                d1.give;
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
                d1.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self d1 : (our Data, our Data)) -> (my Data, my Data) { d1 . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d1 . give ; }, as_ty: (my Data, my Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . give ; }, as_ty: (my Data, my Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: (our Data, our Data), b: (my Data, my Data), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under { cx_a: {}, a: (our Data, our Data), cx_b: {}, b: (my Data, my Data), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_some { lien_data_a: LienData { liens: {}, data: NamedTy((our Data, our Data)) }, lien_datas_b: {LienData { liens: {}, data: NamedTy((my Data, my Data)) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_lien_data { lien_data_a: LienData { liens: {}, data: NamedTy((our Data, our Data)) }, lien_data_b: LienData { liens: {}, data: NamedTy((my Data, my Data)) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #7 (src/file.rs:LL:CC) because
                                       judgment `sub_generic_parameter { variances: [], a: our Data, b: my Data, liens_a: {}, liens_b: {}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "covariant-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `lien_set_is_copy { liens: {}, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "some" failed at step #0 (src/file.rs:LL:CC) because
                                               expression evaluated to an empty collection: `&liens`
                                         the rule "covariant-owned" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `sub_under { cx_a: {}, a: our Data, cx_b: {}, b: my Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                               judgment `sub_some { lien_data_a: LienData { liens: {Copy}, data: NamedTy(Data) }, lien_datas_b: {LienData { liens: {}, data: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `sub_lien_data { lien_data_a: LienData { liens: {Copy}, data: NamedTy(Data) }, lien_data_b: LienData { liens: {}, data: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                                       judgment `sub_lien_sets { liens_a: {Copy}, liens_b: {}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `sub_some_lien { lien_a: Copy, liens_b: {}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                                               expression evaluated to an empty collection: `&liens_b`
                                         the rule "invariant" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `sub { a: our Data, b: my Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `sub_under { cx_a: {}, a: our Data, cx_b: {}, b: my Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `sub_some { lien_data_a: LienData { liens: {Copy}, data: NamedTy(Data) }, lien_datas_b: {LienData { liens: {}, data: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `sub_lien_data { lien_data_a: LienData { liens: {Copy}, data: NamedTy(Data) }, lien_data_b: LienData { liens: {}, data: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                                           judgment `sub_lien_sets { liens_a: {Copy}, liens_b: {}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `sub_some_lien { lien_a: Copy, liens_b: {}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: (our Data, our Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                                                   expression evaluated to an empty collection: `&liens_b`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn our_pair_Data_Data_to_pair_Data_Data() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self, d1: our (Data, Data)) -> (Data, Data) {
                d1.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self d1 : our (Data, Data)) -> (Data, Data) { d1 . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d1 . give ; }, as_ty: (Data, Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . give ; }, as_ty: (Data, Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: our (Data, Data), b: (Data, Data), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under { cx_a: {}, a: our (Data, Data), cx_b: {}, b: (Data, Data), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_some { lien_data_a: LienData { liens: {Copy}, data: NamedTy((Data, Data)) }, lien_datas_b: {LienData { liens: {}, data: NamedTy((Data, Data)) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_lien_data { lien_data_a: LienData { liens: {Copy}, data: NamedTy((Data, Data)) }, lien_data_b: LienData { liens: {}, data: NamedTy((Data, Data)) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_lien_sets { liens_a: {Copy}, liens_b: {}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `sub_some_lien { lien_a: Copy, liens_b: {}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                               expression evaluated to an empty collection: `&liens_b`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn our_pair_Data_Data_to_my_pair_Data_Data() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self, d1: our (Data, Data)) -> my (Data, Data) {
                d1.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self d1 : our (Data, Data)) -> my (Data, Data) { d1 . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d1 . give ; }, as_ty: my (Data, Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . give ; }, as_ty: my (Data, Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: our (Data, Data), b: my (Data, Data), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under { cx_a: {}, a: our (Data, Data), cx_b: {}, b: my (Data, Data), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_some { lien_data_a: LienData { liens: {Copy}, data: NamedTy((Data, Data)) }, lien_datas_b: {LienData { liens: {}, data: NamedTy((Data, Data)) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_lien_data { lien_data_a: LienData { liens: {Copy}, data: NamedTy((Data, Data)) }, lien_data_b: LienData { liens: {}, data: NamedTy((Data, Data)) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_lien_sets { liens_a: {Copy}, liens_b: {}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `sub_some_lien { lien_a: Copy, liens_b: {}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: our (Data, Data)}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                               expression evaluated to an empty collection: `&liens_b`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn my_pair_Data_Data_to_our_pair_Data_Data() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self, d1: my (Data, Data)) -> our (Data, Data) {
                d1.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}
