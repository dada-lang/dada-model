use std::sync::Arc;

use formality_core::{set, test};

use crate::{
    dada_lang::term,
    grammar::{Program, Ty},
    type_system::{env::Env, type_subtype::sub},
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
