use std::sync::Arc;

use formality_core::{judgment_fn, Upcast};

use crate::{
    dada_lang::grammar::Variable,
    grammar::{
        Atomic, ClassDecl, ClassDeclBoundData, ClassPredicate, DropBody, FieldDecl, Kind, NamedTy,
        Perm, Predicate, Program, Ty, UniversalVar, Var, VarianceKind,
    },
};

use super::{
    env::Env,
    expressions::can_type_expr_as,
    liveness::LivePlaces,
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
            (let env = Env::new(program))

            (let (env, substitution, ClassDeclBoundData { predicates, fields, methods, drop_body }) =
                env.open_universally(binder))

            (let class_ty = NamedTy::new(name, substitution))

            (let env = env.add_assumptions(predicates))

            (check_predicates(env, predicates) => ())

            (for_all(field in fields)
                (check_field(class_ty, env, substitution, class_predicate, field) => ()))

            (for_all(method in methods)
                (check_method(class_ty, env, method) => ()))

            (check_drop_body(class_ty, class_predicate, env, drop_body) => ())

            ----------------------------------- ("check_class")
            (check_class(program, decl) => ())
        )
    }
}
// ANCHOR_END: check_class

judgment_fn! {
    fn check_drop_body(
        class_ty: NamedTy,
        class_predicate: ClassPredicate,
        env: Env,
        drop_body: DropBody,
    ) => () {
        debug(drop_body, class_ty, class_predicate, env)

        // Empty drop body — nothing to check.
        (
            (if drop_body.block.statements.is_empty())
            ----------------------------------- ("empty_drop")
            (check_drop_body(_class_ty, _class_predicate, _env, drop_body) => ())
        )

        // Given class: self has type `given Class[...]`.
        (
            (if *class_predicate == ClassPredicate::Given)
            (let self_ty: Ty = Ty::apply_perm(Perm::Given, class_ty))
            (let env = env.push_local_variable(Var::This, self_ty)?)
            (let live_after = LivePlaces::default())
            (can_type_expr_as(env, live_after, drop_body.block.clone(), Ty::unit()) => ())
            ----------------------------------- ("given_class_drop")
            (check_drop_body(class_ty, class_predicate, env, drop_body) => ())
        )

        // Share or Shared class: introduce a universal perm variable P with `P is ref` assumed,
        // then type-check with `self: P Class[...]`.
        (
            (if *class_predicate != ClassPredicate::Given)
            (let (env, perm_var) = env.open_universal_perm_var())
            (let env = env.add_assumptions(vec![Predicate::parameter(
                crate::grammar::ParameterPredicate::Copy, perm_var
            )]))
            (let perm_variable: Variable = UniversalVar::clone(perm_var).upcast())
            (let self_ty: Ty = Ty::apply_perm(Perm::Var(perm_variable.clone()), class_ty))
            (let env = env.push_local_variable(Var::This, self_ty)?)
            (let live_after = LivePlaces::default())
            (can_type_expr_as(env, live_after, drop_body.block.clone(), Ty::unit()) => ())
            ----------------------------------- ("share_class_drop")
            (check_drop_body(class_ty, class_predicate, env, drop_body) => ())
        )
    }
}

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

            (let env = env.push_local_variable(Var::This, class_ty)?)

            (check_type(env, ty) => ())

            // Prove the class predicate holds for all types in the class
            // assuming that it holds for any type parameters.
            (let env = env.add_assumptions(
                class_predicate.parameter_predicates()
                    .into_iter()
                    .flat_map(|pp| {
                        class_substitution
                            .iter()
                            .filter(|v| match v.kind {
                                Kind::Ty => true,
                                Kind::Perm => false,
                            })
                            .map(move |v| Predicate::parameter(pp, v))
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>(),
            ))

            (let () = {
                for pp in class_predicate.parameter_predicates() {
                    let ((), _) = prove_predicate(env, Predicate::parameter(pp, ty)).into_singleton()?;
                }
                Ok::<_, anyhow::Error>(())
            }?)

            (let () = match atomic {
                Atomic::No => Ok::<_, anyhow::Error>(()),
                Atomic::Yes => {
                    let ((), _) = prove_predicate(env, VarianceKind::Atomic.apply(ty)).into_singleton()?;
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
                drop_body: _,
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
                        Predicate::Variance(kind, parameter) if parameter.is_var(v) => Some(*kind),
                        _ => None,
                    })
                    .collect()
            })
            .collect()
    }
}
