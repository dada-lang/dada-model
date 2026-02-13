use fn_error_context::context;
use formality_core::{judgment_fn, Fallible};

use crate::{
    dada_lang::grammar::{Binder, BoundVar},
    grammar::{
        Kind, NamedTy, Parameter, Perm, Place, Predicate, Program, Ty, TypeName, VarianceKind,
    },
};

use super::{env::Env, predicates::prove_predicate, quantifiers::for_all};

judgment_fn! {
    pub fn check_parameter(
        env: Env,
        parameter: Parameter,
    ) => () {
        debug(parameter, env)

        (
            (check_type(&env, &ty) => ())
            ----------------------- ("ty")
            (check_parameter(env, Parameter::Ty(ty)) => ())
        )

        (
            (check_perm(&env, &perm) => ())
            ----------------------- ("perm")
            (check_parameter(env, Parameter::Perm(perm)) => ())
        )
    }
}

judgment_fn! {
    pub fn check_type(
        env: Env,
        ty: Ty,
    ) => () {
        debug(ty, env)

        (
            (let binder = check_class_name(env.program(), &name)?)
            (if parameters.len() == binder.len())
            (let predicates = binder.instantiate_with(&parameters)?)
            (for_all(predicates, &|predicate| prove_predicate(&env, predicate)) => ())
            (for_all(parameters, &|parameter| check_parameter(&env, parameter)) => ())
            ----------------------- ("named")
            (check_type(env, NamedTy { name, parameters }) => ())
        )

        (
            (if env.var_in_scope(v))
            ----------------------- ("var")
            (check_type(env, Ty::Var(v)) => ())
        )

        (
            (check_perm(&env, &perm) => ())
            (check_type(&env, &*ty1) => ())
            (prove_predicate(&env, VarianceKind::Relative.apply(&*ty1)) => ())
            ----------------------- ("apply_perm")
            (check_type(env, Ty::ApplyPerm(perm, ty1)) => ())
        )
    }
}

judgment_fn! {
    fn check_perm(
        env: Env,
        perm: Perm,
    ) => () {
        debug(perm, env)

        (
            ----------------------- ("given")
            (check_perm(_env, Perm::Given) => ())
        )

        (
            ----------------------- ("shared")
            (check_perm(_env, Perm::Shared) => ())
        )

        (
            (for_all(places, &|place| check_place(&env, place)) => ())
            ----------------------- ("ref")
            (check_perm(env, Perm::Rf(places)) => ())
        )

        (
            (if !places.is_empty())
            (for_all(places, &|place| check_place(&env, place)) => ())
            ----------------------- ("given_from")
            (check_perm(env, Perm::Mv(places)) => ())
        )

        (
            (if !places.is_empty())
            (for_all(places, &|place| check_place(&env, place)) => ())
            ----------------------- ("mut")
            (check_perm(env, Perm::Mt(places)) => ())
        )

        (
            (if env.var_in_scope(v))
            ----------------------- ("var")
            (check_perm(env, Perm::Var(v)) => ())
        )

        (
            (check_perm(&env, &*l) => ())
            (check_perm(&env, &*r) => ())
            (prove_predicate(&env, VarianceKind::Relative.apply(&*r)) => ())
            ----------------------- ("apply")
            (check_perm(env, Perm::Apply(l, r)) => ())
        )
    }
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

judgment_fn! {
    fn check_place(
        env: Env,
        place: Place,
    ) => () {
        debug(place, env)

        (
            (let _ = env.place_ty(&place)?)
            ----------------------- ("check_place")
            (check_place(env, place) => ())
        )
    }
}
