use std::sync::Arc;

use formality_core::{test, ProvenSet};

use crate::{
    dada_lang::term,
    grammar::{Program, Ty},
    type_system::{env::Env, liveness::LivePlaces, subtypes::sub},
};

#[test]
fn string_sub_string() {
    let program: Arc<Program> = term("");
    let env: Env = Env::new(program);
    let a: Ty = term("String");
    let b: Ty = term("String");
    let live_after = LivePlaces::default();

    assert_eq!(
        ProvenSet::singleton(env.clone()),
        sub(&env, &live_after, &a, &b)
    );
}

#[test]
fn owned_sub_shared() {
    let program: Arc<Program> = term("");
    let env: Env = Env::new(program);
    let a: Ty = term("String");
    let b: Ty = term("our String");
    let live_after = LivePlaces::default();

    assert_eq!(
        ProvenSet::singleton(env.clone()),
        sub(&env, &live_after, &a, &b)
    );
}
