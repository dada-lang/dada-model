use std::sync::Arc;

use fn_error_context::context;
use formality_core::{judgment::ProofTree, Fallible};

use crate::grammar::{
    Atomic, ClassDecl, ClassDeclBoundData, ClassPredicate, FieldDecl, Kind, NamedTy, Predicate,
    Program, UniversalVar, Var, VarianceKind,
};

use super::{
    env::Env,
    methods::check_method,
    predicates::{check_predicate, prove_predicate},
    types::check_type,
};

#[context("check class named `{:?}`", decl.name)]
pub fn check_class(program: &Arc<Program>, decl: &ClassDecl) -> Fallible<ProofTree> {
    let mut env = Env::new(program);
    let mut proof_tree = ProofTree::new(format!("check_class({:?})", decl.name), None, vec![]);

    let ClassDecl {
        class_predicate,
        name,
        binder,
    } = decl;
    let (
        substitution,
        ClassDeclBoundData {
            predicates,
            fields,
            methods,
        },
    ) = env.open_universally(binder);

    let class_ty = NamedTy::new(name, &substitution);

    env.add_assumptions(&predicates);

    for predicate in predicates {
        proof_tree.children.push(check_predicate(&env, &predicate)?);
    }

    for field in fields {
        proof_tree.children.push(check_field(
            &class_ty,
            &env,
            &substitution,
            *class_predicate,
            &field,
        )?);
    }

    for method in methods {
        let ((), child) = check_method(&class_ty, &env, &method).into_singleton()?;
        proof_tree.children.push(child);
    }

    Ok(proof_tree)
}

#[context("check field named `{:?}`", decl.name)]
fn check_field(
    class_ty: &NamedTy,
    env: &Env,
    class_substitution: &[UniversalVar],
    class_predicate: ClassPredicate,
    decl: &FieldDecl,
) -> Fallible<ProofTree> {
    let env = &mut env.clone();
    let mut proof_tree = ProofTree::new(format!("check_field({:?})", decl.name), None, vec![]);

    let FieldDecl {
        atomic,
        name: _,
        ty,
    } = decl;

    env.push_local_variable(Var::This, class_ty)?;

    proof_tree.children.push(check_type(&*env, ty)?);

    // Prove the class predicate holds for all types in the class
    // assuming that it holds for any type parameters.
    {
        let mut class_predicate_env = env.clone();
        class_predicate_env.add_assumptions(
            class_substitution
                .iter()
                .filter(|v| match v.kind {
                    Kind::Ty => true,
                    Kind::Perm => false,
                })
                .map(|v| class_predicate.apply(v))
                .collect::<Vec<_>>(),
        );
        let ((), child) = prove_predicate(
            class_predicate_env,
            Predicate::class(class_predicate, ty),
        )
        .into_singleton()?;
        proof_tree.children.push(child);
    }
    match atomic {
        Atomic::No => {}

        Atomic::Yes => {
            let ((), child) =
                prove_predicate(&*env, VarianceKind::Atomic.apply(ty)).into_singleton()?;
            proof_tree.children.push(child);
        }
    }

    Ok(proof_tree)
}

impl ClassDecl {
    /// Compute, for each generic parameter of this class,
    /// the relevant variance declarations.
    pub fn variances(&self) -> Vec<Vec<VarianceKind>> {
        let (
            bound_vars,
            ClassDeclBoundData {
                predicates,
                fields: _,
                methods: _,
            },
        ) = self.binder.open();

        bound_vars
            .iter()
            .map(|v| {
                // Find the variance predicates
                // applied to the generic parameter `v`
                predicates
                    .iter()
                    .filter_map(|p| match p {
                        Predicate::Variance(kind, parameter) if parameter.is_var(&v) => Some(*kind),
                        _ => None,
                    })
                    .collect()
            })
            .collect()
    }
}
