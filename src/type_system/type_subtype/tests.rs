use std::sync::Arc;

use formality_core::{test, ProvenSet};

use crate::{
    dada_lang::term,
    grammar::{Kind, Program, Ty},
    test::test_eq,
    type_system::{env::Env, flow::Flow, type_subtype::sub},
};

#[test]
fn string_sub_string() {
    let program: Arc<Program> = term("");
    let env: Env = Env::new(program);
    let flow = Flow::default();
    let a: Ty = term("String");
    let b: Ty = term("String");

    assert_eq!(
        ProvenSet::singleton((env.clone(), flow.clone())),
        sub(&env, &flow, &a, &b)
    );
}

#[test]
fn owned_sub_shared() {
    let program: Arc<Program> = term("");
    let env: Env = Env::new(program);
    let flow = Flow::default();
    let a: Ty = term("String");
    let b: Ty = term("shared() String");

    assert_eq!(
        ProvenSet::singleton((env.clone(), flow.clone())),
        sub(&env, &flow, &a, &b)
    );
}

#[test]
fn shared_sub_shared_x() {
    let program: Arc<Program> = term("");
    let env: Env = Env::new(program);
    let flow = Flow::default();
    let a: Ty = term("shared() String");
    let b: Ty = term("shared(x) String");

    assert_eq!(
        ProvenSet::singleton((env.clone(), flow.clone())),
        sub(&env, &flow, &a, &b)
    );
}

#[test]
fn shared_x_y_sub_shared_x() {
    let program: Arc<Program> = term("");
    let env: Env = Env::new(program);
    let flow = Flow::default();
    let a: Ty = term("shared(x.y) String");
    let b: Ty = term("shared(x) String");

    assert_eq!(
        ProvenSet::singleton((env.clone(), flow.clone())),
        sub(&env, &flow, &a, &b)
    );
}

#[test]
fn shared_x_not_sub_shared_x_y() {
    let program: Arc<Program> = term("");
    let env: Env = Env::new(program);
    let flow = Flow::default();
    let a: Ty = term("shared(x) String");
    let b: Ty = term("shared(x.y) String");

    assert!(!sub(&env, &flow, &a, &b).is_proven());
}

#[test]
fn shared_x_sub_q0() {
    let program: Arc<Program> = term("");
    let mut env: Env = Env::new(program);
    let flow = Flow::default();
    let q0 = env.push_next_existential_var(Kind::Ty);
    let a: Ty = term("shared(x) String");
    test_eq(
        sub(&env, &flow, &a, &q0),
        expect_test::expect!["{(Env { program: , universe: universe(0), in_scope_vars: [?ty_0], local_variables: [], existentials: [existential(universe(0), ty, {shared (x) String}, {}, None)], assumptions: {} }, Flow { moved_places: {} })}"],
    );
}

#[test]
fn shared_x_y_sub_q0_sub_shared_x() {
    let program: Arc<Program> = term("");
    let mut env: Env = Env::new(program);
    let flow = Flow::default();
    let q0 = env.push_next_existential_var(Kind::Ty);
    let shared_x_y: Ty = term("shared(x, y) String");
    let shared_x: Ty = term("shared(x) String");

    // These are incompatible constraints on `q0` -- it would require that
    // `shared(x, y) <: shared(x)`.
    test_eq(
        sub(&env, &flow, &shared_x_y, &q0).flat_map(|(env, flow)| sub(&env, &flow, &q0, &shared_x)),
        expect_test::expect![[r#"FailedJudgment { judgment: "\"flat_map\"", failed_rules: {FailedRule { rule_name_index: None, file: "src/type_system/type_subtype/tests.rs", line: 104, column: 44, cause: FailedJudgment(FailedJudgment { judgment: "sub { a: ?ty_0, b: shared (x) String, env: Env { program: , universe: universe(0), in_scope_vars: [?ty_0], local_variables: [], existentials: [existential(universe(0), ty, {shared (x, y) String}, {}, None)], assumptions: {} }, flow: Flow { moved_places: {} } }", failed_rules: {FailedRule { rule_name_index: Some(("existential, new upper-bound", 3)), file: "src/type_system/type_subtype.rs", line: 142, column: 14, cause: FailedJudgment(FailedJudgment { judgment: "sub { a: shared (x, y) String, b: shared (x) String, env: Env { program: , universe: universe(0), in_scope_vars: [?ty_0], local_variables: [], existentials: [existential(universe(0), ty, {shared (x, y) String}, {shared (x) String}, None)], assumptions: {} }, flow: Flow { moved_places: {} } }", failed_rules: {FailedRule { rule_name_index: Some(("apply-perms", 0)), file: "src/type_system/type_subtype.rs", line: 58, column: 14, cause: FailedJudgment(FailedJudgment { judgment: "sub { a: shared (x, y), b: shared (x), env: Env { program: , universe: universe(0), in_scope_vars: [?ty_0], local_variables: [], existentials: [existential(universe(0), ty, {shared (x, y) String}, {shared (x) String}, None)], assumptions: {} }, flow: Flow { moved_places: {} } }", failed_rules: {FailedRule { rule_name_index: Some(("shared perms", 0)), file: "src/type_system/type_subtype.rs", line: 80, column: 17, cause: IfFalse { expr: "all_places_covered_by_one_of(&places_a, &places_b)" } }} }) }} }) }} }) }} }"#]],
    );
}

#[test]
fn shared_x_sub_q0_sub_shared_x_y() {
    let program: Arc<Program> = term("");
    let mut env: Env = Env::new(program);
    let flow = Flow::default();
    let q0 = env.push_next_existential_var(Kind::Ty);
    let shared_x_y: Ty = term("shared(x, y) String");
    let shared_x: Ty = term("shared(x) String");

    // These are compatible constraints on `q0`.
    test_eq(
        sub(&env, &flow, &shared_x, &q0).flat_map(|(env, flow)| sub(&env, &flow, &q0, &shared_x_y)),
        expect_test::expect!["{(Env { program: , universe: universe(0), in_scope_vars: [?ty_0], local_variables: [], existentials: [existential(universe(0), ty, {shared (x) String}, {shared (x, y) String}, None)], assumptions: {} }, Flow { moved_places: {} })}"],
    );
}

#[test]
fn shared_x_y_shared_x_sub_q0_sub_shared_x() {
    let program: Arc<Program> = term("");
    let mut env: Env = Env::new(program);
    let flow = Flow::default();
    let q0 = env.push_next_existential_var(Kind::Ty);
    let shared_x_y_shared_x: Ty = term("shared(x, y) shared(x) String");
    let shared_x: Ty = term("shared(x) String");

    // These are compatible constraints on `q0`,
    // but only because we can simplify `shared(x, y) shared(x)` to `shared(x)`.
    //
    // What we see are two options:
    // either we simply *before* we relate to `q0`
    // or after.
    //
    // Plausibly we can avoid this by adding some kind of
    // filter on what we will relate to existentials
    // so they must be "canonical".
    test_eq(
        sub(&env, &flow, &shared_x_y_shared_x, &q0)
            .flat_map(|(env, flow)| sub(&env, &flow, &q0, &shared_x)),
        expect_test::expect!["{(Env { program: , universe: universe(0), in_scope_vars: [?ty_0], local_variables: [], existentials: [existential(universe(0), ty, {shared (x) String}, {shared (x) String}, None)], assumptions: {} }, Flow { moved_places: {} }), (Env { program: , universe: universe(0), in_scope_vars: [?ty_0], local_variables: [], existentials: [existential(universe(0), ty, {shared (x, y) shared (x) String}, {shared (x) String}, None)], assumptions: {} }, Flow { moved_places: {} })}"],
    );
}
