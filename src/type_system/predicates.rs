use super::{env::Env, types::check_parameter};
use crate::{
    dada_lang::grammar::UniversalVar,
    grammar::{
        ClassPredicate, NamedTy, Parameter, ParameterPredicate, Perm, Place, Predicate, Ty,
        Variable, VarianceKind,
    },
};
use formality_core::{
    judgment::ProofTree, judgment_fn, Downcast, Fallible, ProvenSet, Set, Upcast,
};

judgment_fn! {
    pub fn check_predicates(
        env: Env,
        predicates: Vec<Predicate>,
    ) => () {
        debug(predicates, env)

        (
            (for_all(predicate in &predicates)
                (check_predicate(&env, predicate) => ()))
            ----------------------- ("check_predicates")
            (check_predicates(env, predicates) => ())
        )
    }
}

judgment_fn! {
    pub fn check_predicate(
        env: Env,
        predicate: Predicate,
    ) => () {
        debug(predicate, env)

        (
            (check_predicate_parameter(&env, &parameter) => ())
            ----------------------- ("parameter")
            (check_predicate(env, Predicate::Parameter(_kind, parameter)) => ())
        )

        (
            (check_predicate_parameter(&env, &parameter) => ())
            ----------------------- ("variance")
            (check_predicate(env, Predicate::Variance(_kind, parameter)) => ())
        )
    }
}

judgment_fn! {
    pub fn check_predicate_parameter(
        env: Env,
        parameter: Parameter,
    ) => () {
        debug(parameter, env)

        (
            (check_parameter(&env, &parameter) => ())
            (if let Some(_) = parameter.downcast::<UniversalVar>())
            ----------------------- ("check_predicate_parameter")
            (check_predicate_parameter(env, parameter) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_predicates(
        env: Env,
        predicate: Vec<Predicate>,
    ) => () {
        debug(predicate, env)

        (
            (for_all(predicate in &predicates)
                (prove_predicate(&env, predicate) => ()))
            ----------------------- ("prove_predicates")
            (prove_predicates(env, predicates) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_is_copy(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_predicate(env, Predicate::copy(a)) => ())
            ---------------------------- ("is")
            (prove_is_copy(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_is_shareable(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_predicate(env, Predicate::share(a)) => ())
            ---------------------------- ("is")
            (prove_is_shareable(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_isnt_known_to_be_copy(
        env: Env,
        p: Parameter,
    ) => () {
        debug(p, env)

        (
            (if let false = is_known_copy(&env, &p)?)
            ---------------------------- ("isnt known to be copy")
            (prove_isnt_known_to_be_copy(env, p) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_is_move(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_predicate(env, Predicate::move_(a)) => ())
            ---------------------------- ("is-moved")
            (prove_is_move(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_is_mut(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_predicate(env, Predicate::mut_(a)) => ())
            ---------------------------- ("is-mut")
            (prove_is_mut(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_is_owned(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_predicate(env, Predicate::owned(a)) => ())
            ---------------------------- ("is-owned")
            (prove_is_owned(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_is_given(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_is_move(&env, &a) => ())
            (prove_is_owned(&env, &a) => ())
            ---------------------------- ("prove")
            (prove_is_given(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_is_copy_owned(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_is_copy(&env, &a) => ())
            (prove_is_owned(&env, &a) => ())
            ---------------------------- ("prove")
            (prove_is_copy_owned(env, a) => ())
        )
    }
}

pub fn prove_is_move_if_some(
    env: impl Upcast<Env>,
    a: impl Upcast<Option<(Place, Parameter)>>,
) -> ProvenSet<()> {
    let a: Option<(Place, Parameter)> = a.upcast();
    match a {
        Some((_, a)) => prove_is_move(env, a),
        None => ProvenSet::singleton(((), ProofTree::leaf("prove_is_move_if_some: None"))),
    }
}

// FIXME: Why does the judgment function below not work but the function above does?
// judgment_fn! {
//     pub fn prove_is_move_if_some(
//         env: Env,
//         a: Option<Parameter>,
//     ) => () {
//         debug(a, env)

//         (
//             (prove_predicate(env, Predicate::move_(a)) => ())
//             ---------------------------- ("is-move-some")
//             (prove_is_move_if_some(env, Some::<Parameter>(a)) => ()) // annoying type hint that doesn't seem like it should be needed
//         )

//         (
//             ---------------------------- ("is-move-none")
//             (prove_is_move_if_some(_env, Option::<Parameter>::None) => ())
//         )
//     }
// }

judgment_fn! {
    pub fn prove_predicate(
        env: Env,
        predicate: Predicate,
    ) => () {
        debug(predicate, env)

        (
            (assumption in env.assumptions())
            (if *assumption == predicate)!
            ---------------------------- ("assumption")
            (prove_predicate(env, predicate) => ())
        )

        (
            (prove_copy_predicate(&env, &p) => ())
            ---------------------------- ("copy")
            (prove_predicate(env, Predicate::Parameter(ParameterPredicate::Copy, p)) => ())
        )

        (
            (prove_move_predicate(&env, &p) => ())
            ---------------------------- ("move")
            (prove_predicate(env, Predicate::Parameter(ParameterPredicate::Move, p)) => ())
        )

        (
            (prove_owned_predicate(&env, &p) => ())
            ---------------------------- ("owned")
            (prove_predicate(env, Predicate::Parameter(ParameterPredicate::Owned, p)) => ())
        )

        (
            (prove_mut_predicate(&env, &p) => ())
            ---------------------------- ("mut")
            (prove_predicate(env, Predicate::Parameter(ParameterPredicate::Mut, p)) => ())
        )

        (
            (prove_given_predicate(&env, &p) => ())
            ---------------------------- ("given")
            (prove_predicate(env, Predicate::Parameter(ParameterPredicate::Given, p)) => ())
        )

        (
            (prove_shared_predicate(&env, &p) => ())
            ---------------------------- ("shared")
            (prove_predicate(env, Predicate::Parameter(ParameterPredicate::Shared, p)) => ())
        )

        (
            (prove_share_predicate(&env, &p) => ())
            ---------------------------- ("share")
            (prove_predicate(env, Predicate::Parameter(ParameterPredicate::Share, p)) => ())
        )

        (
            (variance_predicate(env, kind, parameter) => ())
            ---------------------------- ("variance")
            (prove_predicate(env, Predicate::Variance(kind, parameter)) => ())
        )
    }
}

// =========================================================================
// Per-predicate judgment functions
// =========================================================================

// --- Copy ---

judgment_fn! {
    fn prove_copy_predicate(
        env: Env,
        p: Parameter,
    ) => () {
        debug(p, env)

        // shared class is copy if all parameters are copy
        (
            (if let true = env.is_shared_ty(&name)?)
            (for_all(parameter in &parameters)
                (prove_predicate(&env, Predicate::copy(parameter)) => ()))
            ----------------------------- ("shared-class copy")
            (prove_copy_predicate(env, Parameter::Ty(Ty::NamedTy(NamedTy { name, parameters }))) => ())
        )

        // ApplyPerm — copy if either side is copy
        (
            (prove_predicate(&env, Predicate::copy(perm)) => ())
            ----------------------------- ("apply-perm")
            (prove_copy_predicate(env, Parameter::Ty(Ty::ApplyPerm(perm, _ty))) => ())
        )

        // ApplyPerm — copy if either side is copy
        (
            (prove_predicate(&env, Predicate::copy(&*ty)) => ())
            ----------------------------- ("apply-perm")
            (prove_copy_predicate(env, Parameter::Ty(Ty::ApplyPerm(_perm, ty))) => ())
        )


        // Perm::Shared is copy
        (
            ----------------------------- ("shared copy")
            (prove_copy_predicate(_env, Parameter::Perm(Perm::Shared)) => ())
        )

        // ref is always copy
        (
            ----------------------------- ("rf copy")
            (prove_copy_predicate(_env, Parameter::Perm(Perm::Rf(_places))) => ())
        )

        // given_from[places] is copy if any place's type is copy
        (
            (prove_any_place_predicate(&env, ParameterPredicate::Copy, &places) => ())
            ----------------------------- ("mv copy")
            (prove_copy_predicate(env, Parameter::Perm(Perm::Mv(places))) => ())
        )

        // mut[places] is copy if any place's type is copy
        (
            (prove_any_place_predicate(&env, ParameterPredicate::Copy, &places) => ())
            ----------------------------- ("mt copy")
            (prove_copy_predicate(env, Parameter::Perm(Perm::Mt(places))) => ())
        )

        // Perm::Apply — compose
        (
            (prove_compose_predicate(&env, ParameterPredicate::Copy, Parameter::Perm((*perm1).clone()), Parameter::Perm((*perm2).clone())) => ())
            ----------------------------- ("perm-apply")
            (prove_copy_predicate(env, Parameter::Perm(Perm::Apply(perm1, perm2))) => ())
        )

    }
}

// --- Move ---

judgment_fn! {
    fn prove_move_predicate(
        env: Env,
        p: Parameter,
    ) => () {
        debug(p, env)

        // move(P) is provable from mut(P)
        (
            (prove_predicate(&env, Predicate::mut_(p)) => ())
            ---------------------------- ("mut => move")
            (prove_move_predicate(env, p) => ())
        )

        // shared class is move if any parameter is move
        (
            (if let true = env.is_shared_ty(&name)?)
            (prove_any_parameter_predicate(&env, ParameterPredicate::Move, &parameters) => ())
            ----------------------------- ("shared-class move")
            (prove_move_predicate(env, Parameter::Ty(Ty::NamedTy(NamedTy { name, parameters }))) => ())
        )

        // non-shared class is always move
        (
            (if let false = env.is_shared_ty(&name)?)
            ----------------------------- ("class move")
            (prove_move_predicate(env, Parameter::Ty(Ty::NamedTy(NamedTy { name, parameters: _ }))) => ())
        )

        // ApplyPerm — compose
        (
            (prove_compose_predicate(&env, ParameterPredicate::Move, Parameter::Perm(perm.clone()), Parameter::Ty((&*ty).clone())) => ())
            ----------------------------- ("apply-perm")
            (prove_move_predicate(env, Parameter::Ty(Ty::ApplyPerm(perm, ty))) => ())
        )

        // Perm::Given is move
        (
            ----------------------------- ("given move")
            (prove_move_predicate(_env, Parameter::Perm(Perm::Given)) => ())
        )

        // given_from[places] is move if all places' types are move
        (
            (for_all(place in &places)
                (let ty = env.place_ty(place)?)
                (prove_predicate(&env, Predicate::move_(Parameter::Ty(ty))) => ()))
            ----------------------------- ("mv move")
            (prove_move_predicate(env, Parameter::Perm(Perm::Mv(places))) => ())
        )

        // ref is move only if ALL places have copy types that are move
        (
            (for_all(place in &places)
                (let ty = env.place_ty(place)?)
                (if let true = is_known_copy(&env, &Parameter::Ty(ty.clone()))?)
                (prove_predicate(&env, Predicate::move_(Parameter::Ty(ty))) => ()))
            ----------------------------- ("rf move")
            (prove_move_predicate(env, Parameter::Perm(Perm::Rf(places))) => ())
        )

        // mut[places] is move if all places' types are move
        (
            (for_all(place in &places)
                (let ty = env.place_ty(place)?)
                (prove_predicate(&env, Predicate::move_(Parameter::Ty(ty))) => ()))
            ----------------------------- ("mt move")
            (prove_move_predicate(env, Parameter::Perm(Perm::Mt(places))) => ())
        )

        // Perm::Apply — compose
        (
            (prove_compose_predicate(&env, ParameterPredicate::Move, Parameter::Perm((*perm1).clone()), Parameter::Perm((*perm2).clone())) => ())
            ----------------------------- ("perm-apply")
            (prove_move_predicate(env, Parameter::Perm(Perm::Apply(perm1, perm2))) => ())
        )

    }
}

// --- Owned ---

judgment_fn! {
    fn prove_owned_predicate(
        env: Env,
        p: Parameter,
    ) => () {
        debug(p, env)

        // shared class is owned if all parameters are owned
        (
            (if let true = env.is_shared_ty(&name)?)
            (for_all(parameter in &parameters)
                (prove_predicate(&env, Predicate::owned(parameter)) => ()))
            ----------------------------- ("shared-class owned")
            (prove_owned_predicate(env, Parameter::Ty(Ty::NamedTy(NamedTy { name, parameters }))) => ())
        )

        // non-shared class is owned if all parameters are owned
        (
            (if let false = env.is_shared_ty(&name)?)
            (for_all(parameter in &parameters)
                (prove_predicate(&env, Predicate::owned(parameter)) => ()))
            ----------------------------- ("class owned")
            (prove_owned_predicate(env, Parameter::Ty(Ty::NamedTy(NamedTy { name, parameters }))) => ())
        )

        // ApplyPerm — compose
        (
            (prove_compose_predicate(&env, ParameterPredicate::Owned, Parameter::Perm(perm.clone()), Parameter::Ty((&*ty).clone())) => ())
            ----------------------------- ("apply-perm")
            (prove_owned_predicate(env, Parameter::Ty(Ty::ApplyPerm(perm, ty))) => ())
        )

        // Perm::Given is owned
        (
            ----------------------------- ("given owned")
            (prove_owned_predicate(_env, Parameter::Perm(Perm::Given)) => ())
        )

        // Perm::Shared is owned
        (
            ----------------------------- ("shared owned")
            (prove_owned_predicate(_env, Parameter::Perm(Perm::Shared)) => ())
        )

        // given_from[places] is owned if all places' types are owned
        (
            (for_all(place in &places)
                (let ty = env.place_ty(place)?)
                (prove_predicate(&env, Predicate::owned(Parameter::Ty(ty))) => ()))
            ----------------------------- ("mv owned")
            (prove_owned_predicate(env, Parameter::Perm(Perm::Mv(places))) => ())
        )

        // ref is owned only if ALL places have copy types that are owned
        (
            (for_all(place in &places)
                (let ty = env.place_ty(place)?)
                (if let true = is_known_copy(&env, &Parameter::Ty(ty.clone()))?)
                (prove_predicate(&env, Predicate::owned(Parameter::Ty(ty))) => ()))
            ----------------------------- ("rf owned")
            (prove_owned_predicate(env, Parameter::Perm(Perm::Rf(places))) => ())
        )

        // mut[places] is owned only if ALL places have copy types that are owned
        (
            (for_all(place in &places)
                (let ty = env.place_ty(place)?)
                (if let true = is_known_copy(&env, &Parameter::Ty(ty.clone()))?)
                (prove_predicate(&env, Predicate::owned(Parameter::Ty(ty))) => ()))
            ----------------------------- ("mt owned")
            (prove_owned_predicate(env, Parameter::Perm(Perm::Mt(places))) => ())
        )

        // Perm::Apply — compose
        (
            (prove_compose_predicate(&env, ParameterPredicate::Owned, Parameter::Perm((*perm1).clone()), Parameter::Perm((*perm2).clone())) => ())
            ----------------------------- ("perm-apply")
            (prove_owned_predicate(env, Parameter::Perm(Perm::Apply(perm1, perm2))) => ())
        )

    }
}

// --- Mut ---

judgment_fn! {
    fn prove_mut_predicate(
        env: Env,
        p: Parameter,
    ) => () {
        debug(p, env)

        // ApplyPerm — compose
        (
            (prove_compose_predicate(&env, ParameterPredicate::Mut, Parameter::Perm(perm.clone()), Parameter::Ty((&*ty).clone())) => ())
            ----------------------------- ("apply-perm")
            (prove_mut_predicate(env, Parameter::Ty(Ty::ApplyPerm(perm, ty))) => ())
        )

        // ref is mut if any place's type is mut
        (
            (prove_any_place_predicate(&env, ParameterPredicate::Mut, &places) => ())
            ----------------------------- ("rf mut")
            (prove_mut_predicate(env, Parameter::Perm(Perm::Rf(places))) => ())
        )

        // given_from[places] is mut if any place's type is mut
        (
            (prove_any_place_predicate(&env, ParameterPredicate::Mut, &places) => ())
            ----------------------------- ("mv mut")
            (prove_mut_predicate(env, Parameter::Perm(Perm::Mv(places))) => ())
        )

        // mut[places] is mut if any place's type is NOT copy (SomeMut.mut=true makes || true)
        (
            (place in &places)
            (let ty = env.place_ty(place)?)
            (prove_isnt_known_to_be_copy(&env, &Parameter::Ty(ty)) => ())
            ----------------------------- ("mt mut non-copy")
            (prove_mut_predicate(env, Parameter::Perm(Perm::Mt(places))) => ())
        )

        // mut[places] is mut if any place's type IS copy but also mut
        (
            (prove_any_place_predicate(&env, ParameterPredicate::Mut, &places) => ())
            ----------------------------- ("mt mut copy-place")
            (prove_mut_predicate(env, Parameter::Perm(Perm::Mt(places))) => ())
        )

        // Perm::Apply — compose
        (
            (prove_compose_predicate(&env, ParameterPredicate::Mut, Parameter::Perm((*perm1).clone()), Parameter::Perm((*perm2).clone())) => ())
            ----------------------------- ("perm-apply")
            (prove_mut_predicate(env, Parameter::Perm(Perm::Apply(perm1, perm2))) => ())
        )

    }
}

// --- Given (the predicate, not the permission) ---

judgment_fn! {
    fn prove_given_predicate(
        env: Env,
        p: Parameter,
    ) => () {
        debug(p, env)

        // Perm::Given satisfies the given predicate
        (
            ----------------------------- ("given given")
            (prove_given_predicate(_env, Parameter::Perm(Perm::Given)) => ())
        )

    }
}

// --- Shared (the predicate: copy + owned) ---

judgment_fn! {
    fn prove_shared_predicate(
        env: Env,
        p: Parameter,
    ) => () {
        debug(p, env)

        // shared === copy + owned
        (
            (prove_is_copy(&env, &p) => ())
            (prove_is_owned(&env, &p) => ())
            ----------------------------- ("shared = copy + owned")
            (prove_shared_predicate(env, p) => ())
        )

        // Perm::Shared satisfies the shared predicate
        (
            ----------------------------- ("shared shared")
            (prove_shared_predicate(_env, Parameter::Perm(Perm::Shared)) => ())
        )

    }
}

// --- Share (can be shared: share class, no given class parameters) ---

judgment_fn! {
    fn prove_share_predicate(
        env: Env,
        p: Parameter,
    ) => () {
        debug(p, env)

        // share(T) — a named type is share if declared to be and all type parameters are share.
        (
            (if let true = env.meets_class_predicate(&name, ClassPredicate::Share)?)
            (for_all(parameter in &parameters)
                (prove_predicate(&env, Predicate::share(parameter)) => ()))
            ----------------------------- ("share class")
            (prove_share_predicate(env, Parameter::Ty(Ty::NamedTy(NamedTy { name, parameters }))) => ())
        )

        // share(P T) — if T is share
        (
            (prove_predicate(&env, Predicate::share(&*ty)) => ())
            ----------------------------- ("share P T")
            (prove_share_predicate(env, Parameter::Ty(Ty::ApplyPerm(_, ty))) => ())
        )

        // share(P T) — if P is mut
        (
            (prove_is_mut(&env, perm) => ())
            ----------------------------- ("share mut T")
            (prove_share_predicate(env, Parameter::Ty(Ty::ApplyPerm(perm, _))) => ())
        )

        // share(P T) — if P is copy (ref or shared)
        (
            (prove_is_copy(&env, perm) => ())
            ----------------------------- ("share copy T")
            (prove_share_predicate(env, Parameter::Ty(Ty::ApplyPerm(perm, _))) => ())
        )

    }
}

// =========================================================================
// Variance
// =========================================================================

judgment_fn! {
    fn variance_predicate(
        env: Env,
        kind: VarianceKind,
        parameter: Parameter,
    ) => () {
        debug(kind, parameter, env)

        (
            (for_all(parameter in &parameters)
                (prove_predicate(&env, kind.apply(parameter)) => ()))
            ----------------------------- ("ty-named")
            (variance_predicate(env, kind, NamedTy { name: _, parameters }) => ())
        )

        (
            (prove_predicate(&env, kind.apply(perm)) => ())
            (prove_predicate(&env, kind.apply(&*ty)) => ())
            ----------------------------- ("ty")
            (variance_predicate(env, kind, Ty::ApplyPerm(perm, ty)) => ())
        )

        (
            ----------------------------- ("given")
            (variance_predicate(_env, _kind, Perm::Given) => ())
        )

        (
            ----------------------------- ("shared")
            (variance_predicate(_env, _kind, Perm::Shared) => ())
        )

        // FIXME: Is this right? What about e.g. `shared class Foo[perm P, ty T] { x: T, y: P ref[x] String }`
        // or other such things? and what about `given_from[x]`?

        (
            ----------------------------- ("shared")
            (variance_predicate(_env, _kind, Perm::Rf(_)) => ())
        )

        (
            (for_all(place in &places)
                (variance_predicate_place(&env, kind, place) => ()))
            ----------------------------- ("leased")
            (variance_predicate(env, kind, Perm::Mt(places)) => ())
        )

        (
            (for_all(place in &places)
                (variance_predicate_place(&env, kind, place) => ()))
            ----------------------------- ("given")
            (variance_predicate(env, kind, Perm::Mv(places)) => ())
        )

        (
            (prove_predicate(&env, kind.apply(&*perm1)) => ())
            (prove_predicate(&env, kind.apply(&*perm2)) => ())
            ----------------------------- ("perm-apply")
            (variance_predicate(env, kind, Perm::Apply(perm1, perm2)) => ())
        )

    }
}

judgment_fn! {
    fn variance_predicate_place(
        env: Env,
        kind: VarianceKind,
        place: Place,
    ) => () {
        debug(kind, place, env)

        (
            (let ty = env.place_ty(&place)?)
            (prove_predicate(&env, kind.apply(ty)) => ())
            ----------------------------- ("perm")
            (variance_predicate_place(env, kind, place) => ())
        )
    }
}

// =========================================================================
// Generic helpers (still parameterized over k: ParameterPredicate)
// =========================================================================

// Bridge function: routes back through prove_predicate for generic-k callers.
judgment_fn! {
    fn prove_parameter_predicate(
        env: Env,
        k: ParameterPredicate,
        p: Parameter,
    ) => () {
        debug(k, p, env)

        (
            (prove_predicate(&env, Predicate::Parameter(k, p)) => ())
            ----------------------------- ("bridge")
            (prove_parameter_predicate(env, k, p) => ())
        )
    }
}

// Compose predicate: prove k(lhs rhs) based on composition rules.
//
// If rhs is copy, (lhs rhs) = rhs, so just check rhs.
// Otherwise:
//   - Copy/Mut: lhs meets k OR rhs meets k
//   - Move/Owned: lhs meets k AND rhs meets k
judgment_fn! {
    fn prove_compose_predicate(
        env: Env,
        k: ParameterPredicate,
        lhs: Parameter,
        rhs: Parameter,
    ) => () {
        debug(k, lhs, rhs, env)

        // If rhs is copy, (lhs rhs) = rhs, so just check rhs for k
        (
            (if let true = is_known_copy(&env, &rhs)?)
            (prove_parameter_predicate(&env, k, &rhs) => ())
            ----------------------------- ("compose rhs-copy")
            (prove_compose_predicate(env, k, _lhs, rhs) => ())
        )

        // Copy/Mut with || semantics: lhs meets k
        (
            (if let false = is_known_copy(&env, &rhs)?)
            (prove_parameter_predicate(&env, k, &lhs) => ())
            ----------------------------- ("compose or-lhs")
            (prove_compose_predicate(env, k @ (ParameterPredicate::Copy | ParameterPredicate::Mut), lhs, rhs) => ())
        )

        // Copy/Mut with || semantics: rhs meets k
        (
            (if let false = is_known_copy(&env, &rhs)?)
            (prove_parameter_predicate(&env, k, &rhs) => ())
            ----------------------------- ("compose or-rhs")
            (prove_compose_predicate(env, k @ (ParameterPredicate::Copy | ParameterPredicate::Mut), _lhs, rhs) => ())
        )

        // Move/Owned with && semantics: both must meet k
        (
            (if let false = is_known_copy(&env, &rhs)?)
            (prove_parameter_predicate(&env, k, &lhs) => ())
            (prove_parameter_predicate(&env, k, &rhs) => ())
            ----------------------------- ("compose and")
            (prove_compose_predicate(env, k @ (ParameterPredicate::Move | ParameterPredicate::Owned), lhs, rhs) => ())
        )
    }
}

// Prove that any place in the set has a type meeting predicate k.
judgment_fn! {
    fn prove_any_place_predicate(
        env: Env,
        k: ParameterPredicate,
        places: Set<Place>,
    ) => () {
        debug(k, places, env)

        (
            (place in &places)
            (let ty = env.place_ty(place)?)
            (prove_parameter_predicate(&env, k, &Parameter::Ty(ty)) => ())
            ----------------------------- ("any place")
            (prove_any_place_predicate(env, k, places) => ())
        )
    }
}

// Prove that any parameter in the set meets predicate k.
judgment_fn! {
    fn prove_any_parameter_predicate(
        env: Env,
        k: ParameterPredicate,
        parameters: Vec<Parameter>,
    ) => () {
        debug(k, parameters, env)

        (
            (parameter in &parameters)
            (prove_parameter_predicate(&env, k, parameter) => ())
            ----------------------------- ("any parameter")
            (prove_any_parameter_predicate(env, k, parameters) => ())
        )
    }
}

// =========================================================================
// is_known_copy — plain function guard for compose rules
// =========================================================================

/// Check if a parameter is structurally known to be copy.
///
/// This is a plain function (not a judgment) used as a guard in compose rules
/// to avoid cycles: the compose judgment needs to know if rhs is copy before
/// deciding which compose rule to apply, but checking via prove_is_copy would
/// create cycles through prove_predicate → prove_compose_predicate →
/// prove_is_copy → prove_predicate → ...
fn is_known_copy(env: &Env, param: &Parameter) -> Fallible<bool> {
    match param {
        Parameter::Ty(ty) => is_known_copy_ty(env, ty),
        Parameter::Perm(perm) => is_known_copy_perm(env, perm),
    }
}

fn is_known_copy_ty(env: &Env, ty: &Ty) -> Fallible<bool> {
    match ty {
        Ty::NamedTy(NamedTy { name, parameters }) => {
            if env.is_shared_ty(name)? {
                // Shared (value) type is copy iff all parameters are copy
                parameters
                    .iter()
                    .try_fold(true, |acc, p| Ok(acc && is_known_copy(env, p)?))
            } else {
                // Non-shared class is never copy
                Ok(false)
            }
        }
        Ty::ApplyPerm(perm, ty) => {
            // For Copy, compose simplifies to lhs.copy || rhs.copy
            Ok(is_known_copy_perm(env, perm)? || is_known_copy_ty(env, ty)?)
        }
        Ty::Var(Variable::UniversalVar(v)) => Ok(env.assumed_to_meet(v, ParameterPredicate::Copy)),
        Ty::Var(Variable::ExistentialVar(_)) | Ty::Var(Variable::BoundVar(_)) => {
            panic!("unexpected variable: {ty:?}")
        }
    }
}

fn is_known_copy_perm(env: &Env, perm: &Perm) -> Fallible<bool> {
    match perm {
        Perm::Given => Ok(false),
        Perm::Shared => Ok(true),
        Perm::Mv(places) => {
            // Any place's type is copy
            for place in places.iter() {
                let place_ty = env.place_ty(place)?;
                if is_known_copy_ty(env, &place_ty)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        Perm::Rf(_) => {
            // ref is always copy (SomeCopy || anything = true for Copy)
            Ok(true)
        }
        Perm::Mt(places) => {
            // SomeMut is not copy, so Compose(SomeMut, place).copy = false || place.copy
            // Any place's type being copy makes this copy
            for place in places.iter() {
                let place_ty = env.place_ty(place)?;
                if is_known_copy_ty(env, &place_ty)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        Perm::Var(Variable::UniversalVar(v)) => {
            Ok(env.assumed_to_meet(v, ParameterPredicate::Copy))
        }
        Perm::Var(Variable::ExistentialVar(_)) | Perm::Var(Variable::BoundVar(_)) => {
            panic!("unexpected variable: {perm:?}")
        }
        Perm::Apply(p1, p2) => {
            // For Copy, compose simplifies to lhs.copy || rhs.copy
            Ok(is_known_copy_perm(env, p1)? || is_known_copy_perm(env, p2)?)
        }
    }
}
