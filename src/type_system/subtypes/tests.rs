use std::sync::Arc;

use formality_core::{test, ProvenSet};

use crate::{
    dada_lang::term,
    grammar::{Program, Ty},
    type_system::{env::Env, flow::Flow, subtypes::sub},
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
    let b: Ty = term("our String");

    assert_eq!(
        ProvenSet::singleton((env.clone(), flow.clone())),
        sub(&env, &flow, &a, &b)
    );
}
