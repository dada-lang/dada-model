use std::sync::Arc;

use formality_core::judgment_fn;

use crate::grammar::{
    Atomic, ClassDecl, ClassDeclBoundData, ClassPredicate, FieldDecl, Kind, NamedTy, Predicate,
    Program, UniversalVar, Var, VarianceKind,
};

use super::{
    env::Env,
    methods::check_method,
    predicates::{check_predicates, prove_predicate},
    types::check_type,
};

// ANCHOR: check_class
judgment_fn! {
    pub fn check_class(
        program: Arc<Program>,
        decl: ClassDecl,
    ) => () {
        debug(decl, program)

        (
            (let ClassDecl { class_predicate, name, binder } = decl)
            (let env = Env::new(&program))

            (let (env, substitution, ClassDeclBoundData { predicates, fields, methods }) =
                env.open_universally(&binder))

            (let class_ty = NamedTy::new(&name, &substitution))

            (let env = env.add_assumptions(&predicates))

            (check_predicates(&env, &predicates) => ())

            (let () = {
                for field in &fields {
                    let ((), _) = check_field(&class_ty, &env, &substitution, class_predicate, field).into_singleton()?;
                }
                Ok::<_, anyhow::Error>(())
            }?)

            (let () = {
                for method in &methods {
                    let ((), _) = check_method(&class_ty, &env, method).into_singleton()?;
                }
                Ok::<_, anyhow::Error>(())
            }?)

            ----------------------------------- ("check_class")
            (check_class(program, decl) => ())
        )
    }
}
// ANCHOR_END: check_class

// ANCHOR: check_field
judgment_fn! {
    fn check_field(
        class_ty: NamedTy,
        env: Env,
        class_substitution: Vec<UniversalVar>,
        class_predicate: ClassPredicate,
        decl: FieldDecl,
    ) => () {
        debug(decl, class_ty, class_predicate, env)

        (
            (let FieldDecl { atomic, name: _, ty } = &decl)

            (let env = env.push_local_variable(Var::This, &class_ty)?)

            (check_type(&env, ty) => ())

            // Prove the class predicate holds for all types in the class
            // assuming that it holds for any type parameters.
            (let env = env.add_assumptions(
                class_substitution
                    .iter()
                    .filter(|v| match v.kind {
                        Kind::Ty => true,
                        Kind::Perm => false,
                    })
                    .map(|v| class_predicate.apply(v))
                    .collect::<Vec<_>>(),
            ))

            (prove_predicate(&env, Predicate::class(class_predicate, ty)) => ())

            (let () = match atomic {
                Atomic::No => Ok::<_, anyhow::Error>(()),
                Atomic::Yes => {
                    let ((), _) = prove_predicate(&env, VarianceKind::Atomic.apply(ty)).into_singleton()?;
                    Ok(())
                }
            }?)

            ----------------------------------- ("check_field")
            (check_field(class_ty, env, class_substitution, class_predicate, decl) => ())
        )
    }
}
// ANCHOR_END: check_field

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
