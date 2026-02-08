use std::sync::Arc;

use fn_error_context::context;
use formality_core::Fallible;

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
pub fn check_class(program: &Arc<Program>, decl: &ClassDecl) -> Fallible<()> {
    let mut env = Env::new(program);

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
        check_predicate(&env, &predicate)?;
    }

    for field in fields {
        check_field(&class_ty, &env, &substitution, *class_predicate, &field)?;
    }

    for method in methods {
        check_method(&class_ty, &env, &method)?;
    }

    Ok(())
}

#[context("check field named `{:?}`", decl.name)]
fn check_field(
    class_ty: &NamedTy,
    env: &Env,
    class_substitution: &[UniversalVar],
    class_predicate: ClassPredicate,
    decl: &FieldDecl,
) -> Fallible<()> {
    let env = &mut env.clone();

    let FieldDecl {
        atomic,
        name: _,
        ty,
    } = decl;

    env.push_local_variable(Var::This, class_ty)?;

    check_type(&*env, ty)?;

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
        let _ = prove_predicate(class_predicate_env, Predicate::class(class_predicate, ty))
            .check_proven()?;
    }
    match atomic {
        Atomic::No => {}

        Atomic::Yes => {
            let _ = prove_predicate(&*env, VarianceKind::Atomic.apply(ty)).check_proven()?;
        }
    }

    Ok(())
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
