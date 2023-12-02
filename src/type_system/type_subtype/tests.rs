use std::sync::Arc;

use formality_core::{set, test};

use crate::{
    dada_lang::term,
    grammar::{Kind, Program, Ty},
    type_system::{env::Env, quantifiers::seq, type_subtype::sub},
};

#[test]
fn string_sub_string() {
    let program: Arc<Program> = term("");
    let env: Env = Env::new(program);
    let a: Ty = term("String");
    let b: Ty = term("String");

    assert_eq!(set![env.clone()], sub(&env, &a, &b));
}

#[test]
fn owned_sub_shared() {
    let program: Arc<Program> = term("");
    let env: Env = Env::new(program);
    let a: Ty = term("String");
    let b: Ty = term("shared() String");

    assert_eq!(set![env.clone()], sub(&env, &a, &b));
}

#[test]
fn shared_sub_shared_x() {
    let program: Arc<Program> = term("");
    let env: Env = Env::new(program);
    let a: Ty = term("String");
    let b: Ty = term("shared(x) String");

    assert_eq!(set![env.clone()], sub(&env, &a, &b));
}

#[test]
fn shared_x_y_sub_shared_x() {
    let program: Arc<Program> = term("");
    let env: Env = Env::new(program);
    let a: Ty = term("shared(x.y) String");
    let b: Ty = term("shared(x) String");

    assert_eq!(set![env.clone()], sub(&env, &a, &b));
}

#[test]
fn shared_x_not_sub_shared_x_y() {
    let program: Arc<Program> = term("");
    let env: Env = Env::new(program);
    let a: Ty = term("shared(x) String");
    let b: Ty = term("shared(x.y) String");

    assert_eq!(set![], sub(&env, &a, &b));
}

#[test]
fn shared_x_sub_q0() {
    let program: Arc<Program> = term("");
    let mut env: Env = Env::new(program);
    let q0 = env.push_next_existential_var(Kind::Ty);
    let a: Ty = term("shared(x) String");
    expect_test::expect![[r#"
        {
            Env {
                program: Program {
                    decls: [],
                },
                universe: Universe(
                    0,
                ),
                in_scope_vars: [
                    ?ty_0,
                ],
                local_variables: [],
                existentials: [
                    Existential {
                        universe: Universe(
                            0,
                        ),
                        kind: Ty,
                        lower_bounds: {
                            Ty(
                                ApplyPerm(
                                    Shared(
                                        {
                                            Place {
                                                var: x,
                                                projections: [],
                                            },
                                        },
                                    ),
                                    ClassTy(
                                        ClassTy {
                                            name: Id(
                                                String,
                                            ),
                                            parameters: [],
                                        },
                                    ),
                                ),
                            ),
                        },
                        upper_bounds: {},
                        perm_bound: None,
                    },
                ],
                assumptions: {},
            },
        }
    "#]]
    .assert_debug_eq(&sub(&env, &a, &q0));
}

#[test]
fn shared_x_y_sub_q0_sub_shared_x() {
    let program: Arc<Program> = term("");
    let mut env: Env = Env::new(program);
    let q0 = env.push_next_existential_var(Kind::Ty);
    let shared_x_y: Ty = term("shared(x, y) String");
    let shared_x: Ty = term("shared(x) String");

    // These are incompatible constraints on `q0` -- it would require that
    // `shared(x, y) <: shared(x)`.
    expect_test::expect![[r#"
        {}
    "#]]
    .assert_debug_eq(&seq(sub(&env, &shared_x_y, &q0), |env| {
        sub(&env, &q0, &shared_x)
    }));
}

#[test]
fn shared_x_sub_q0_sub_shared_x_y() {
    let program: Arc<Program> = term("");
    let mut env: Env = Env::new(program);
    let q0 = env.push_next_existential_var(Kind::Ty);
    let shared_x_y: Ty = term("shared(x, y) String");
    let shared_x: Ty = term("shared(x) String");

    // These are compatible constraints on `q0`.
    expect_test::expect![[r#"
        {
            Env {
                program: Program {
                    decls: [],
                },
                universe: Universe(
                    0,
                ),
                in_scope_vars: [
                    ?ty_0,
                ],
                local_variables: [],
                existentials: [
                    Existential {
                        universe: Universe(
                            0,
                        ),
                        kind: Ty,
                        lower_bounds: {
                            Ty(
                                ApplyPerm(
                                    Shared(
                                        {
                                            Place {
                                                var: x,
                                                projections: [],
                                            },
                                        },
                                    ),
                                    ClassTy(
                                        ClassTy {
                                            name: Id(
                                                String,
                                            ),
                                            parameters: [],
                                        },
                                    ),
                                ),
                            ),
                        },
                        upper_bounds: {
                            Ty(
                                ApplyPerm(
                                    Shared(
                                        {
                                            Place {
                                                var: x,
                                                projections: [],
                                            },
                                            Place {
                                                var: y,
                                                projections: [],
                                            },
                                        },
                                    ),
                                    ClassTy(
                                        ClassTy {
                                            name: Id(
                                                String,
                                            ),
                                            parameters: [],
                                        },
                                    ),
                                ),
                            ),
                        },
                        perm_bound: None,
                    },
                ],
                assumptions: {},
            },
        }
    "#]]
    .assert_debug_eq(&seq(sub(&env, &shared_x, &q0), |env| {
        sub(&env, &q0, &shared_x_y)
    }));
}

#[test]
fn shared_x_y_shared_x_sub_q0_sub_shared_x() {
    let program: Arc<Program> = term("");
    let mut env: Env = Env::new(program);
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
    expect_test::expect![[r#"
        {
            Env {
                program: Program {
                    decls: [],
                },
                universe: Universe(
                    0,
                ),
                in_scope_vars: [
                    ?ty_0,
                ],
                local_variables: [],
                existentials: [
                    Existential {
                        universe: Universe(
                            0,
                        ),
                        kind: Ty,
                        lower_bounds: {g
                            Ty(
                                ApplyPerm(
                                    Shared(
                                        {
                                            Place {
                                                var: x,
                                                projections: [],
                                            },
                                        },
                                    ),
                                    ClassTy(
                                        ClassTy {
                                            name: Id(
                                                String,
                                            ),
                                            parameters: [],
                                        },
                                    ),
                                ),
                            ),
                        },
                        upper_bounds: {
                            Ty(
                                ApplyPerm(
                                    Shared(
                                        {
                                            Place {
                                                var: x,
                                                projections: [],
                                            },
                                        },
                                    ),
                                    ClassTy(
                                        ClassTy {
                                            name: Id(
                                                String,
                                            ),
                                            parameters: [],
                                        },
                                    ),
                                ),
                            ),
                        },
                        perm_bound: None,
                    },
                ],
                assumptions: {},
            },
            Env {
                program: Program {
                    decls: [],
                },
                universe: Universe(
                    0,
                ),
                in_scope_vars: [
                    ?ty_0,
                ],
                local_variables: [],
                existentials: [
                    Existential {
                        universe: Universe(
                            0,
                        ),
                        kind: Ty,
                        lower_bounds: {
                            Ty(
                                ApplyPerm(
                                    Shared(
                                        {
                                            Place {
                                                var: x,
                                                projections: [],
                                            },
                                            Place {
                                                var: y,
                                                projections: [],
                                            },
                                        },
                                    ),
                                    ApplyPerm(
                                        Shared(
                                            {
                                                Place {
                                                    var: x,
                                                    projections: [],
                                                },
                                            },
                                        ),
                                        ClassTy(
                                            ClassTy {
                                                name: Id(
                                                    String,
                                                ),
                                                parameters: [],
                                            },
                                        ),
                                    ),
                                ),
                            ),
                        },
                        upper_bounds: {
                            Ty(
                                ApplyPerm(
                                    Shared(
                                        {
                                            Place {
                                                var: x,
                                                projections: [],
                                            },
                                        },
                                    ),
                                    ClassTy(
                                        ClassTy {
                                            name: Id(
                                                String,
                                            ),
                                            parameters: [],
                                        },
                                    ),
                                ),
                            ),
                        },
                        perm_bound: None,
                    },
                ],
                assumptions: {},
            },
        }
    "#]]
    .assert_debug_eq(&seq(sub(&env, &shared_x_y_shared_x, &q0), |env| {
        sub(&env, &q0, &shared_x)
    }));
}
