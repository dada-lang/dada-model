use super::{env::Env, types::check_parameter};
use crate::{
    dada_lang::grammar::UniversalVar,
    grammar::{
        ClassPredicate, NamedTy, Parameter, ParameterPredicate, Perm, Place, Predicate, Ty,
        TypeName, VarianceKind,
    },
};
use formality_core::{judgment::ProofTree, judgment_fn, Downcast, ProvenSet, Upcast};

judgment_fn! {
    pub fn check_predicates(
        env: Env,
        predicates: Vec<Predicate>,
    ) => () {
        debug(predicates, env)

        (
            (for_all(predicate in predicates)
                (check_predicate(env, predicate) => ()))
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
            (check_predicate_parameter(env, parameter) => ())
            ----------------------- ("parameter")
            (check_predicate(env, Predicate::Parameter(_kind, parameter)) => ())
        )

        (
            (check_predicate_parameter(env, parameter) => ())
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
            (check_parameter(env, parameter) => ())
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
            (for_all(predicate in predicates)
                (prove_predicate(env, predicate) => ()))
            ----------------------- ("prove_predicates")
            (prove_predicates(env, predicates) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_is_shared(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_predicate(env, Predicate::is_shared(a)) => ())
            ---------------------------- ("is")
            (prove_is_shared(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_is_struct(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_predicate(env, Predicate::struct_(a)) => ())
            ---------------------------- ("is")
            (prove_is_struct(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_isnt_known_to_be_shared(
        env: Env,
        p: Parameter,
    ) => () {
        debug(p, env)

        (
            (if !prove_is_shared(env, p).is_proven())
            ---------------------------- ("isnt shared")
            (prove_isnt_known_to_be_shared(env, p) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_is_unique(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_predicate(env, Predicate::unique(a)) => ())
            ---------------------------- ("is-unique")
            (prove_is_unique(env, a) => ())
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
    pub fn prove_is_unique_owned(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_is_unique(env, a) => ())
            (prove_is_owned(env, a) => ())
            ---------------------------- ("prove")
            (prove_is_unique_owned(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_is_shared_owned(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_is_shared(env, a) => ())
            (prove_is_owned(env, a) => ())
            ---------------------------- ("prove")
            (prove_is_shared_owned(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_is_boxed(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_predicate(env, Predicate::boxed(a)) => ())
            ---------------------------- ("prove")
            (prove_is_boxed(env, a) => ())
        )
    }
}

pub fn prove_is_unique_if_some(
    env: impl Upcast<Env>,
    a: impl Upcast<Option<(Place, Parameter)>>,
) -> ProvenSet<()> {
    let a: Option<(Place, Parameter)> = a.upcast();
    match a {
        Some((_, a)) => prove_is_unique(env, a),
        None => ProvenSet::singleton(((), ProofTree::leaf("prove_is_unique_if_some: None"))),
    }
}

// FIXME: Why does the judgment function below not work but the function above does?
// judgment_fn! {
//     pub fn prove_is_unique_if_some(
//         env: Env,
//         a: Option<Parameter>,
//     ) => () {
//         debug(a, env)

//         (
//             (prove_predicate(env, Predicate::unique(a)) => ())
//             ---------------------------- ("is-unique-some")
//             (prove_is_unique_if_some(env, Some::<Parameter>(a)) => ()) // annoying type hint that doesn't seem like it should be needed
//         )

//         (
//             ---------------------------- ("is-unique-none")
//             (prove_is_unique_if_some(_env, Option::<Parameter>::None) => ())
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
            (if env.assumptions().contains(&predicate))!
            ---------------------------- ("assumption")
            (prove_predicate(env, predicate) => ())
        )

        (
            (prove_shared_predicate(env, p) => ())
            ---------------------------- ("shared")
            (prove_predicate(env, Predicate::Parameter(ParameterPredicate::Shared, p)) => ())
        )

        (
            (prove_unique_predicate(env, p) => ())
            ---------------------------- ("unique")
            (prove_predicate(env, Predicate::Parameter(ParameterPredicate::Unique, p)) => ())
        )

        (
            (prove_owned_predicate(env, p) => ())
            ---------------------------- ("owned")
            (prove_predicate(env, Predicate::Parameter(ParameterPredicate::Owned, p)) => ())
        )

        (
            (prove_mut_predicate(env, p) => ())
            ---------------------------- ("mut")
            (prove_predicate(env, Predicate::Parameter(ParameterPredicate::Mut, p)) => ())
        )

        (
            (prove_struct_predicate(env, p) => ())
            ---------------------------- ("struct")
            (prove_predicate(env, Predicate::Parameter(ParameterPredicate::Struct, p)) => ())
        )

        (
            (prove_boxed_predicate(env, p) => ())
            ---------------------------- ("boxed")
            (prove_predicate(env, Predicate::Parameter(ParameterPredicate::Boxed, p)) => ())
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

// --- Shared (duplicable, including shared views of places) ---

judgment_fn! {
    fn prove_shared_predicate(
        env: Env,
        p: Parameter,
    ) => () {
        debug(p, env)

        // a shared-class instantiation is duplicable if all parameters are shared
        (
            (if let true = env.is_shared_ty(name)?)!
            (for_all(parameter in parameters)
                (prove_predicate(env, Predicate::is_shared(parameter)) => ()))
            ----------------------------- ("shared-class shared")
            (prove_shared_predicate(env, Parameter::Ty(Ty::NamedTy(NamedTy { name, parameters }))) => ())
        )

        // ApplyPerm — shared if either side is shared
        (
            (prove_shared_composed_predicate(env, perm, &**ty) => ())
            ----------------------------- ("apply-perm")
            (prove_shared_predicate(env, Parameter::Ty(Ty::ApplyPerm(perm, ty))) => ())
        )


        // Perm::Shared is shared
        (
            ----------------------------- ("shared shared")
            (prove_shared_predicate(_env, Parameter::Perm(Perm::Shared)) => ())
        )

        // place sharing is always shared
        (
            ----------------------------- ("shared places")
            (prove_shared_predicate(_env, Parameter::Perm(Perm::SharedFrom(_places))) => ())
        )

        // ^[places] is shared if all places' types are shared
        (
            (for_all(place in places)
                (let ty = env.place_ty(place)?)
                (prove_predicate(env, Predicate::is_shared(Parameter::ty(ty))) => ()))
            ----------------------------- ("mv shared")
            (prove_shared_predicate(env, Parameter::Perm(Perm::Mv(places))) => ())
        )

        // Perm::Apply — compose
        (
            (prove_shared_composed_predicate(env, &**perm1, &**perm2) => ())
            ----------------------------- ("perm-apply")
            (prove_shared_predicate(env, Parameter::Perm(Perm::Apply(perm1, perm2))) => ())
        )

        // Perm::Or — for-all: all branches must be shared
        (
            (for_all(perm in perms)
                (prove_shared_predicate(env, Parameter::perm(perm)) => ()))
            ----------------------------- ("or shared")
            (prove_shared_predicate(env, Parameter::Perm(Perm::Or(perms))) => ())
        )

    }
}

judgment_fn! {
    fn prove_shared_composed_predicate(
        env: Env,
        lhs: Parameter,
        rhs: Parameter,
    ) => () {
        debug(lhs, rhs, env)

        (
            (prove_shared_predicate(env, lhs) => ())
            ----------------------------- ("shared-lhs")
            (prove_shared_composed_predicate(env, lhs, rhs) => ())
        )

        (
            (prove_shared_predicate(env, rhs) => ())
            ----------------------------- ("shared-rhs")
            (prove_shared_composed_predicate(env, lhs, rhs) => ())
        )

    }
}

// --- Unique ---

judgment_fn! {
    fn prove_unique_predicate(
        env: Env,
        p: Parameter,
    ) => () {
        debug(p, env)

        // unique(P) is provable from mut(P)
        (
            (prove_predicate(env, Predicate::mut_(p)) => ())
            ---------------------------- ("mut => unique")
            (prove_unique_predicate(env, p) => ())
        )

        // shared struct is unique if any parameter is unique
        (
            (if let true = env.is_shared_ty(name)?)
            (parameter in parameters)
            (prove_parameter_predicate(env, ParameterPredicate::Unique, parameter) => ())
            ----------------------------- ("shared-class unique")
            (prove_unique_predicate(env, Parameter::Ty(Ty::NamedTy(NamedTy { name, parameters }))) => ())
        )

        // class or ordinary struct is always unique
        (
            (if let false = env.is_shared_ty(name)?)
            ----------------------------- ("class unique")
            (prove_unique_predicate(env, Parameter::Ty(Ty::NamedTy(NamedTy { name, parameters: _ }))) => ())
        )

        // ApplyPerm — compose
        (
            (prove_is_unique(env, perm) => ())
            (prove_is_unique(env, &**ty) => ())
            ----------------------------- ("apply-perm")
            (prove_unique_predicate(env, Parameter::Ty(Ty::ApplyPerm(perm, ty))) => ())
        )

        // Perm::Given is unique
        (
            ----------------------------- ("^ unique")
            (prove_unique_predicate(_env, Parameter::Perm(Perm::Given)) => ())
        )

        // ^[places] is unique if all places' types are unique
        (
            (for_all(place in places)
                (let ty = env.place_ty(place)?)
                (prove_predicate(env, Predicate::unique(Parameter::Ty(ty.clone()))) => ()))
            ----------------------------- ("mv unique")
            (prove_unique_predicate(env, Parameter::Perm(Perm::Mv(places))) => ())
        )

        // place sharing is unique only if ALL places have copy types that are unique
        (
            (for_all(place in places)
                (let ty = env.place_ty(place)?)
                (prove_predicate(env, Predicate::is_shared(Parameter::Ty(ty.clone()))) => ())
                (prove_predicate(env, Predicate::unique(Parameter::Ty(ty.clone()))) => ()))
            ----------------------------- ("shared places unique")
            (prove_unique_predicate(env, Parameter::Perm(Perm::SharedFrom(places))) => ())
        )

        // ![places] is unique if all places' types are unique
        (
            (for_all(place in places)
                (let ty = env.place_ty(place)?)
                (prove_predicate(env, Predicate::unique(Parameter::Ty(ty.clone()))) => ()))
            ----------------------------- ("mt unique")
            (prove_unique_predicate(env, Parameter::Perm(Perm::Mt(places))) => ())
        )

        // Perm::Apply — compose
        (
            (prove_is_unique(env, &**perm1) => ())
            (prove_is_unique(env, &**perm2) => ())
            ----------------------------- ("perm-apply")
            (prove_unique_predicate(env, Parameter::Perm(Perm::Apply(perm1, perm2))) => ())
        )

        // Perm::Or — for-all: all branches must be unique
        (
            (for_all(perm in perms)
                (prove_unique_predicate(env, Parameter::perm(perm)) => ()))
            ----------------------------- ("or unique")
            (prove_unique_predicate(env, Parameter::Perm(Perm::Or(perms))) => ())
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

        // shared struct is owned if all parameters are owned
        (
            (if let true = env.is_shared_ty(name)?)
            (for_all(parameter in parameters)
                (prove_predicate(env, Predicate::owned(parameter)) => ()))
            ----------------------------- ("shared-class owned")
            (prove_owned_predicate(env, Parameter::Ty(Ty::NamedTy(NamedTy { name, parameters }))) => ())
        )

        // class or ordinary struct is owned if all parameters are owned
        (
            (if let false = env.is_shared_ty(name)?)
            (for_all(parameter in parameters)
                (prove_predicate(env, Predicate::owned(parameter)) => ()))
            ----------------------------- ("class owned")
            (prove_owned_predicate(env, Parameter::Ty(Ty::NamedTy(NamedTy { name, parameters }))) => ())
        )

        // ApplyPerm — compose
        (
            (prove_owned_composed_predicate(env, perm, &**ty) => ())
            ----------------------------- ("apply-perm")
            (prove_owned_predicate(env, Parameter::Ty(Ty::ApplyPerm(perm, ty))) => ())
        )

        // Perm::Given is owned
        (
            ----------------------------- ("^ owned")
            (prove_owned_predicate(_env, Parameter::Perm(Perm::Given)) => ())
        )

        // Perm::Shared is owned
        (
            ----------------------------- ("shared owned")
            (prove_owned_predicate(_env, Parameter::Perm(Perm::Shared)) => ())
        )

        // ^[places] is owned if all places' types are owned
        (
            (for_all(place in places)
                (let ty = env.place_ty(place)?)
                (prove_predicate(env, Predicate::owned(Parameter::Ty(ty.clone()))) => ()))
            ----------------------------- ("mv owned")
            (prove_owned_predicate(env, Parameter::Perm(Perm::Mv(places))) => ())
        )

        // place sharing is owned only if ALL places have copy types that are owned
        (
            (for_all(place in places)
                (let ty = env.place_ty(place)?)
                (prove_predicate(env, Predicate::is_shared(Parameter::Ty(ty.clone()))) => ())
                (prove_predicate(env, Predicate::owned(Parameter::Ty(ty.clone()))) => ()))
            ----------------------------- ("shared places owned")
            (prove_owned_predicate(env, Parameter::Perm(Perm::SharedFrom(places))) => ())
        )

        // ![places] is owned only if ALL places have copy types that are owned
        (
            (for_all(place in places)
                (let ty = env.place_ty(place)?)
                (prove_predicate(env, Predicate::is_shared(Parameter::Ty(ty.clone()))) => ())
                (prove_predicate(env, Predicate::owned(Parameter::Ty(ty.clone()))) => ()))
            ----------------------------- ("mt owned")
            (prove_owned_predicate(env, Parameter::Perm(Perm::Mt(places))) => ())
        )

        // Perm::Apply — compose
        (
            (prove_owned_composed_predicate(env, &**perm1, &**perm2) => ())
            ----------------------------- ("perm-apply")
            (prove_owned_predicate(env, Parameter::Perm(Perm::Apply(perm1, perm2))) => ())
        )

        // Perm::Or — for-all: all branches must be owned
        (
            (for_all(perm in perms)
                (prove_owned_predicate(env, Parameter::perm(perm)) => ()))
            ----------------------------- ("or owned")
            (prove_owned_predicate(env, Parameter::Perm(Perm::Or(perms))) => ())
        )

    }
}

judgment_fn! {
    fn prove_owned_composed_predicate(
        env: Env,
        lhs: Parameter,
        rhs: Parameter,
    ) => () {
        debug(lhs, rhs, env)

        (
            (prove_is_shared(env, rhs) => ())
            (prove_is_owned(env, rhs) => ())
            ----------------------------- ("shared-rhs")
            (prove_owned_composed_predicate(env, lhs, rhs) => ())
        )

        (
            (prove_is_owned(env, lhs) => ())
            (prove_is_owned(env, rhs) => ())
            ----------------------------- ("owned-lhs-rhs")
            (prove_owned_composed_predicate(env, lhs, rhs) => ())
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
            (prove_mut_composed_predicate(env, perm, &**ty) => ())
            ----------------------------- ("apply-perm")
            (prove_mut_predicate(env, Parameter::Ty(Ty::ApplyPerm(perm, ty))) => ())
        )

        // place sharing is never mut (read-only borrow strips mutability)

        // ^[places] is mut if all places' types are mut
        (
            (for_all(place in places)
                (let ty = env.place_ty(place)?)
                (prove_predicate(env, Predicate::mut_(Parameter::Ty(ty.clone()))) => ()))
            ----------------------------- ("mv mut")
            (prove_mut_predicate(env, Parameter::Perm(Perm::Mv(places))) => ())
        )

        // ![places] is mut if, for each place, the composition SomeMut ∘ place_ty is mut.
        // That holds when the place's type is either non-copy (SomeMut dominates)
        // or copy-and-mut (the copy type itself carries mutability).
        (
            (for_all(place in places)
                (let ty = env.place_ty(place)?)
                (prove_place_ty_mut(env, ty) => ()))
            ----------------------------- ("mt mut")
            (prove_mut_predicate(env, Parameter::Perm(Perm::Mt(places))) => ())
        )

        // Perm::Apply — compose
        (
            (prove_mut_composed_predicate(env, &**perm1, &**perm2) => ())
            ----------------------------- ("perm-apply")
            (prove_mut_predicate(env, Parameter::Perm(Perm::Apply(perm1, perm2))) => ())
        )

        // Perm::Or — for-all: all branches must be mut
        (
            (for_all(perm in perms)
                (prove_mut_predicate(env, Parameter::perm(perm)) => ()))
            ----------------------------- ("or mut")
            (prove_mut_predicate(env, Parameter::Perm(Perm::Or(perms))) => ())
        )

    }
}

judgment_fn! {
    fn prove_mut_composed_predicate(
        env: Env,
        lhs: Parameter,
        rhs: Parameter,
    ) => () {
        debug(lhs, rhs, env)

        (
            (prove_mut_predicate(env, lhs) => ())
            (prove_unique_predicate(env, rhs) => ())
            ----------------------------- ("mut-lhs")
            (prove_mut_composed_predicate(env, lhs, rhs) => ())
        )

        (
            (prove_unique_predicate(env, lhs) => ())
            (prove_mut_predicate(env, rhs) => ())
            ----------------------------- ("mut-rhs")
            (prove_mut_composed_predicate(env, lhs, rhs) => ())
        )

    }
}

// --- Struct (values can be shared) ---

judgment_fn! {
    fn prove_struct_predicate(
        env: Env,
        p: Parameter,
    ) => () {
        debug(p, env)

        // struct(T) — a named type is struct if declared to be and all type parameters are struct.
        (
            (if let true = env.meets_class_predicate(name, ClassPredicate::Struct)?)
            (for_all(parameter in parameters)
                (prove_predicate(env, Predicate::struct_(parameter)) => ()))
            ----------------------------- ("struct")
            (prove_struct_predicate(env, Parameter::Ty(Ty::NamedTy(NamedTy { name, parameters }))) => ())
        )

        // struct(P T) — if T is struct
        (
            (prove_predicate(env, Predicate::struct_(&**ty)) => ())
            ----------------------------- ("struct P T")
            (prove_struct_predicate(env, Parameter::Ty(Ty::ApplyPerm(_, ty))) => ())
        )

        // struct(P T) — if P is mut
        (
            (prove_is_mut(env, perm) => ())
            ----------------------------- ("struct mut T")
            (prove_struct_predicate(env, Parameter::Ty(Ty::ApplyPerm(perm, _))) => ())
        )

        // struct(P T) — if P is shared (place sharing or shared)
        (
            (prove_is_shared(env, perm) => ())
            ----------------------------- ("struct shared T")
            (prove_struct_predicate(env, Parameter::Ty(Ty::ApplyPerm(perm, _))) => ())
        )

    }
}

// --- Boxed ---

judgment_fn! {
    fn prove_boxed_predicate(
        env: Env,
        p: Parameter,
    ) => () {
        debug(p, env)

        // Arrays are boxed.
        (
            ----------------------------- ("boxed array")
            (prove_boxed_predicate(env, NamedTy { name: TypeName::Array, .. }) => ())
        )

        // Perms don't matter.
        (
            (prove_boxed_predicate(env, &**ty) => ())
            ----------------------------- ("boxed array")
            (prove_boxed_predicate(env, Ty::ApplyPerm(_perm, ty)) => ())
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
            (for_all(parameter in parameters)
                (prove_predicate(env, kind.apply(parameter)) => ()))
            ----------------------------- ("ty-named")
            (variance_predicate(env, kind, NamedTy { name: _, parameters }) => ())
        )

        (
            (prove_predicate(env, kind.apply(perm)) => ())
            (prove_predicate(env, kind.apply(&**ty)) => ())
            ----------------------------- ("ty")
            (variance_predicate(env, kind, Ty::ApplyPerm(perm, ty)) => ())
        )

        (
            ----------------------------- ("^")
            (variance_predicate(_env, _kind, Perm::Given) => ())
        )

        (
            ----------------------------- ("shared")
            (variance_predicate(_env, _kind, Perm::Shared) => ())
        )

        // FIXME: Is this right? What about e.g. `shared struct Foo[perm P, ty T] { x: T, y: P shared[x] String }`
        // or other such things? and what about `^[x]`?

        (
            ----------------------------- ("shared")
            (variance_predicate(_env, _kind, Perm::SharedFrom(_)) => ())
        )

        (
            (for_all(place in places)
                (variance_predicate_place(env, kind, place) => ()))
            ----------------------------- ("leased")
            (variance_predicate(env, kind, Perm::Mt(places)) => ())
        )

        (
            (for_all(place in places)
                (variance_predicate_place(env, kind, place) => ()))
            ----------------------------- ("^")
            (variance_predicate(env, kind, Perm::Mv(places)) => ())
        )

        (
            (prove_predicate(env, kind.apply(&**perm1)) => ())
            (prove_predicate(env, kind.apply(&**perm2)) => ())
            ----------------------------- ("perm-apply")
            (variance_predicate(env, kind, Perm::Apply(perm1, perm2)) => ())
        )

        (
            (for_all(perm in perms)
                (variance_predicate(env, kind, perm) => ()))
            ----------------------------- ("perm-or")
            (variance_predicate(env, kind, Perm::Or(perms)) => ())
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
            (let ty = env.place_ty(place)?)
            (prove_predicate(env, kind.apply(ty)) => ())
            ----------------------------- ("perm")
            (variance_predicate_place(env, kind, place) => ())
        )
    }
}

// A place's type is "mut under composition with SomeMut" if either:
// - the type is non-copy (SomeMut ∘ NonCopy = SomeMut → mut), or
// - the type is itself mut (SomeMut ∘ CopyMut = CopyMut → mut)
judgment_fn! {
    fn prove_place_ty_mut(
        env: Env,
        ty: Ty,
    ) => () {
        debug(ty, env)

        // non-copy type: SomeMut dominates
        (
            (prove_isnt_known_to_be_shared(env, Parameter::Ty(ty.clone())) => ())
            ----------------------------- ("non-shared")
            (prove_place_ty_mut(env, ty) => ())
        )

        // copy type that is itself mut
        (
            (prove_predicate(env, Predicate::mut_(Parameter::Ty(ty.clone()))) => ())
            ----------------------------- ("shared-mut")
            (prove_place_ty_mut(env, ty) => ())
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
            (prove_predicate(env, Predicate::Parameter(k.clone(), p.clone())) => ())
            ----------------------------- ("bridge")
            (prove_parameter_predicate(env, k, p) => ())
        )
    }
}
