use std::sync::Arc;

use formality_core::{test, ProvenSet};

use crate::{
    dada_lang::term,
    grammar::{Program, Ty},
    type_system::{env::Env, subtypes::sub},
};

#[test]
fn string_sub_string() {
    let program: Arc<Program> = term("");
    let env: Env = Env::new(program);
    let a: Ty = term("String");
    let b: Ty = term("String");

    assert_eq!(ProvenSet::singleton(env.clone()), sub(&env, &a, &b));
}

#[test]
fn owned_sub_shared() {
    let program: Arc<Program> = term("");
    let env: Env = Env::new(program);
    let a: Ty = term("String");
    let b: Ty = term("our String");

    assert_eq!(ProvenSet::singleton(env.clone()), sub(&env, &a, &b));
}
