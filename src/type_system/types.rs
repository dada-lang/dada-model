use anyhow::bail;
use fn_error_context::context;
use formality_core::{judgment::ProofTree, Fallible};

use crate::{
    dada_lang::grammar::{Binder, BoundVar},
    grammar::{
        Kind, NamedTy, Parameter, Perm, Place, Predicate, Program, Ty, TypeName, VarianceKind,
    },
};

use super::{env::Env, predicates::prove_predicate};

pub fn check_parameter(env: &Env, parameter: &Parameter) -> Fallible<ProofTree> {
    match parameter {
        Parameter::Ty(ty) => check_type(env, ty),
        Parameter::Perm(perm) => check_perm(env, perm),
    }
}

#[context("check type `{:?}`", ty)]
pub fn check_type(env: &Env, ty: &Ty) -> Fallible<ProofTree> {
    let mut proof_tree = ProofTree::new(format!("check_type({ty:?})"), None, vec![]);
    match ty {
        Ty::NamedTy(NamedTy { name, parameters }) => {
            let predicates = check_class_name(env.program(), name)?;
            if parameters.len() != predicates.len() {
                bail!(
                    "class `{:?}` expects {} parameters, but found {}",
                    name,
                    predicates.len(),
                    parameters.len(),
                )
            }

            let predicates = predicates.instantiate_with(&parameters)?;

            for predicate in predicates {
                let ((), child) = prove_predicate(env, predicate).into_singleton()?;
                proof_tree.children.push(child);
            }

            for parameter in parameters {
                proof_tree.children.push(check_parameter(env, parameter)?);
            }
        }

        Ty::Var(v) => {
            assert!(env.var_in_scope(*v));
        }

        Ty::ApplyPerm(perm, ty1) => {
            proof_tree.children.push(check_perm(env, perm)?);
            proof_tree.children.push(check_type(env, ty1)?);
            let ((), child) =
                prove_predicate(env, VarianceKind::Relative.apply(&**ty1)).into_singleton()?;
            proof_tree.children.push(child);
        }
    }
    Ok(proof_tree)
}

#[context("check_perm({:?}", perm)]
fn check_perm(env: &Env, perm: &Perm) -> Fallible<ProofTree> {
    let mut proof_tree = ProofTree::new(format!("check_perm({perm:?})"), None, vec![]);
    match perm {
        Perm::My | Perm::Our => {}

        Perm::Rf(places) => {
            for place in places {
                proof_tree.children.push(check_place(env, place)?);
            }
        }

        Perm::Mv(places) | Perm::Mt(places) => {
            if places.len() == 0 {
                bail!("permision requires at lease one place");
            }

            for place in places {
                proof_tree.children.push(check_place(env, place)?);
            }
        }

        Perm::Var(v) => {
            assert!(env.var_in_scope(*v));
        }

        Perm::Apply(l, r) => {
            proof_tree.children.push(check_perm(env, l)?);
            proof_tree.children.push(check_perm(env, r)?);
            let ((), child) =
                prove_predicate(env, VarianceKind::Relative.apply(&**r)).into_singleton()?;
            proof_tree.children.push(child);
        }
    }
    Ok(proof_tree)
}

#[context("check class name `{:?}`", name)]
fn check_class_name(program: &Program, name: &TypeName) -> Fallible<Binder<Vec<Predicate>>> {
    match name {
        TypeName::Tuple(n) => {
            let parameters: Vec<_> = (0..*n).map(|_| BoundVar::fresh(Kind::Ty)).collect();
            Ok(Binder::new(parameters, vec![]))
        }
        TypeName::Int => Ok(Binder::dummy(vec![])),
        TypeName::Id(id) => {
            let decl = program.class_named(id)?;
            Ok(decl.binder.map(|b| b.predicates.clone()))
        }
    }
}

#[context("check place `{:?}`", place)]
fn check_place(env: &Env, place: &Place) -> Fallible<ProofTree> {
    let _ty = env.place_ty(place)?;
    Ok(ProofTree::leaf(format!("check_place({place:?})")))
}
