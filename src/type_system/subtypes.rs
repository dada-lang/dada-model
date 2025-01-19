use formality_core::{judgment_fn, Cons, Set};

use crate::{
    grammar::{NamedTy, Parameter, Perm, Place, Predicate, Ty, VarianceKind},
    type_system::{
        env::Env,
        is_::{lien_chain_is_copy, lien_chain_is_leased, lien_chain_is_owned},
        lien_chains::{lien_chains, ty_chains, Lien, LienChain, My, Our, TyChain},
        liveness::LivePlaces,
        predicates::prove_predicate,
        quantifiers::{fold, fold_zipped},
    },
};

judgment_fn! {
    /// Provable if `a <: b` in an owned (`my`) context.
    pub fn sub(
        env: Env,
        live_after: LivePlaces,
        a: Parameter,
        b: Parameter,
    ) => Env {
        debug(a, b, live_after, env)

        (
            (sub_in_cx(env, live_after, My(), a, My(), b) => env)
            ------------------------------- ("sub")
            (sub(env, live_after, a, b) => env)
        )
    }
}

judgment_fn! {
    /// Provable if `a <: b` when appearing in the context of lien chains `chain_a` and `chain_b` respectively.
    fn sub_in_cx(
        env: Env,
        live_after: LivePlaces,
        cx_a: LienChain,
        a: Parameter,
        cx_b: LienChain,
        b: Parameter,
    ) => Env {
        debug(cx_a, a, cx_b, b, live_after, env)

        (
            (ty_chains(&env, cx_a, a) => ty_liens_a)
            (ty_chains(&env, &cx_b, &b) => ty_liens_b)
            (sub_ty_chain_sets(&env, &live_after, &ty_liens_a, ty_liens_b) => env)
            ------------------------------- ("sub")
            (sub_in_cx(env, live_after, cx_a, a: Ty, cx_b, b: Ty) => env)
        )

        (
            (lien_chains(&env, cx_a, a) => chain_a)
            (lien_chains(&env, &cx_b, &b) => chain_b)
            (sub_lien_chain_sets(&env, &live_after, &chain_a, chain_b) => env)
            ------------------------------- ("sub")
            (sub_in_cx(env, live_after, cx_a, a: Perm, cx_b, b: Perm) => env)
        )
    }
}

judgment_fn! {
    fn sub_ty_chain_sets(
        env: Env,
        live_after: LivePlaces,
        ty_liens_a: Set<TyChain>,
        ty_liens_b: Set<TyChain>,
    ) => Env {
        debug(ty_liens_a, ty_liens_b, live_after, env)

        (
            ------------------------------- ("nil")
            (sub_ty_chain_sets(env, _live_after, (), _b_s) => env)
        )

        (
            (&b_s => b)
            (sub_ty_chains(&env, &live_after, &a, &b) => env)
            (sub_ty_chain_sets(env, &live_after, &a_s, &b_s) => env)
            ------------------------------- ("cons")
            (sub_ty_chain_sets(env, live_after, Cons(a, a_s), b_s) => env)
        )
    }
}

judgment_fn! {
    fn sub_ty_chains(
        env: Env,
        live_after: LivePlaces,
        ty_chain_a: TyChain,
        ty_chain_b: TyChain,
    ) => Env {
        debug(ty_chain_a, ty_chain_b, live_after, env)

        (
            (if a == b)!
            (sub_lien_chains(env, live_after, &chain_a, &chain_b) => env)
            -------------------------------- ("var")
            (sub_ty_chains(env, live_after, TyChain::Var(chain_a, a), TyChain::Var(chain_b, b)) => env)
        )

        (
            (let NamedTy { name: name_a, parameters: parameters_a } = a)
            (let NamedTy { name: name_b, parameters: parameters_b } = b)
            (assert env.is_class_ty(&name_a))
            (if name_a == name_b)! // FIXME: subtyping between classes
            (sub_lien_chains(env, &live_after, &chain_a, &chain_b) => env)
            (let variances = env.variances(&name_a)?)
            (if parameters_a.len() == variances.len())
            (if parameters_b.len() == variances.len())
            (fold(env, 0..variances.len(), &|env, &i| {
                sub_generic_parameter(env, &live_after, &variances[i], &chain_a, &parameters_a[i], &chain_b, &parameters_b[i])
            }) => env)
            -------------------------------- ("class ty")
            (sub_ty_chains(env, live_after, TyChain::ClassTy(chain_a, a), TyChain::ClassTy(chain_b, b)) => env)
        )

        (
            (let NamedTy { name: name_a, parameters: parameters_a } = a)
            (let NamedTy { name: name_b, parameters: parameters_b } = b)
            (assert env.is_value_ty(&name_a))
            (if name_a == name_b)!
            (fold_zipped(env, &parameters_a, &parameters_b, &|env, parameter_a, parameter_b| {
                sub_in_cx(env, &live_after, &chain_a, parameter_a, &chain_b, parameter_b)
            }) => env)
            -------------------------------- ("value ty")
            (sub_ty_chains(env, live_after, TyChain::ValueTy(chain_a, a), TyChain::ValueTy(chain_b, b)) => env)
        )
    }
}

judgment_fn! {
    fn sub_generic_parameter(
        env: Env,
        live_after: LivePlaces,
        variances: Vec<VarianceKind>,
        cx_a: LienChain,
        a: Parameter,
        cx_b: LienChain,
        b: Parameter,
    ) => Env {
        debug(variances, cx_a, a, cx_b, b, live_after, env)

        // FIXME: this may be stricter than needed: we may everything invariant
        // even if it's just relative and not atomic, is that correct?

        (
            (sub_in_cx(env, &live_after, My(), &a, My(), &b) => env)
            (sub_in_cx(env, &live_after, My(), &b, My(), &a) => env)
            ------------------------------- ("invariant")
            (sub_generic_parameter(env, live_after, _variances, _cx_a, a, _cx_b, b) => env)
        )

        (
            (lien_chain_is_copy(&env, &cx_a) => ())
            (sub_in_cx(&env, &live_after, &cx_a, &a, &cx_b, &b) => env)
            ------------------------------- ("shared_a")
            (sub_generic_parameter(env, live_after, (), cx_a, a, cx_b, b) => env)
        )

        (
            (lien_chain_is_copy(&env, &cx_b) => ())
            (sub_in_cx(&env, &live_after, &cx_a, &a, &cx_b, &b) => env)
            ------------------------------- ("shared_b")
            (sub_generic_parameter(env, live_after, (), cx_a, a, cx_b, b) => env)
        )

        (
            (sub_in_cx(env, live_after, My(), a, My(), b) => env)
            ------------------------------- ("my")
            (sub_generic_parameter(env, live_after, (), My(), a, My(), b) => env)
        )
    }
}

judgment_fn! {
    /// Provable if every chain in `chains_a` is a subchain of some chain in `chains_b`.
    fn sub_lien_chain_sets(
        env: Env,
        live_after: LivePlaces,
        chains_a: Set<LienChain>,
        chains_b: Set<LienChain>,
    ) => Env {
        debug(chains_a, chains_b, live_after, env)

        (
            ------------------------------- ("nil")
            (sub_lien_chain_sets(env, _live_after, (), _chains_b) => env)
        )

        (
            (&chains_b => chain_b)
            (sub_lien_chains(&env, &live_after, &chain_a, &chain_b) => env)
            (sub_lien_chain_sets(env, &live_after, &chains_a, &chains_b) => env)
            ------------------------------- ("cons")
            (sub_lien_chain_sets(env, live_after, Cons(chain_a, chains_a), chains_b) => env)
        )
    }
}

judgment_fn! {
    /// `sub_lien_chains(env, live_after, a, b)` indicates a value of some type `a T`
    /// can be safely converted to a value of type `b T` in the environment `env`
    /// and assuming that the places in `live_after` are live at the point of conversion.
    fn sub_lien_chains(
        env: Env,
        live_after: LivePlaces,
        a: LienChain,
        b: LienChain,
    ) => Env {
        debug(a, b, live_after, env)

        // My is a subchain of everything BUT leased.
        //
        // It has full permissions but it is not layout compatible with leased.

        (
            (lien_chain_is_copy(&env, &b) => ())
            --------------------------- ("my-copy")
            (sub_lien_chains(env, _live_after, My(), b) => &env)
        )

        (
            (lien_chain_is_owned(&env, &b) => ())
            --------------------------- ("my-owned")
            (sub_lien_chains(env, _live_after, My(), b) => &env)
        )

        // Our is a subchain of everything that is copy.
        //
        // It has full permissions but it is not layout compatible with leased.

        (
            (lien_chain_is_copy(&env, &b) => ())
            --------------------------- ("our-copy")
            (sub_lien_chains(env, _live_after, Our(), b) => &env)
        )

        // If the start of `a` is *covered* by the start of `b`
        // (covered = gives a superset of permissions)
        // and all permissions from the subchains are also covered,
        // then `a` is a subpermission of `b`.

        (
            (lien_covered_by(&env, lien_a, lien_b) => ())
            (extension_covered_by(&env, &chain_a, &chain_b) => env)
            --------------------------- ("matched starts")
            (sub_lien_chains(env, _live_after, Cons(lien_a, chain_a), Cons(lien_b, chain_b)) => &env)
        )

        //

        // We can go from `shared[p] leased[d]` to `our leased[d]` if `p` is dead.
        // Here `p: leased[d]` so it previously had unique access to `d`.
        (
            (lien_chain_is_leased(&env, &chain_a) => ())
            (if !live_after.is_live(place))
            (sub_lien_chains(&env, &live_after, Cons(Lien::Our, &chain_a), &chain_b) => env)
            --------------------------- ("cancel shared")
            (sub_lien_chains(env, live_after, Cons(Lien::Shared(place), chain_a), chain_b) => env)
        )

        // We can go from `leased[p] leased[d]` to `leased[d]` if `p` is dead.
        // Here `p: leased[d]` so it previously had unique access to `d`.
        (
            (lien_chain_is_leased(&env, &chain_a) => ())
            (if !live_after.is_live(place))
            (sub_lien_chains(&env, &live_after, &chain_a, &chain_b) => env)
            --------------------------- ("cancel leased")
            (sub_lien_chains(env, live_after, Cons(Lien::Leased(place), chain_a), chain_b) => env)
        )
    }
}

judgment_fn! {
    /// We say that an extension `a` is *covered* by an extension `b` if they have
    /// the same length and each lien in the extension covers the corresponding lien
    /// in the other extension.
    fn extension_covered_by(
        env: Env,
        a: LienChain,
        b: LienChain,
    ) => Env {
        debug(a, b, env)

        (
            ------------------------------- ("my-*")
            (extension_covered_by(env, My(), My()) => &env)
        )

        (
            (lien_covered_by(&env, lien_a, lien_b) => ())
            (extension_covered_by(&env, &chain_a, &chain_b) => env)
            ------------------------------- ("lien-lien")
            (extension_covered_by(env, Cons(lien_a, chain_a), Cons(lien_b, chain_b)) => env)
        )
    }
}

judgment_fn! {
    /// A lien `a` is *covered by* a lien `b` if
    ///
    /// 1. `a` *gives* a superset of `b`'s permissions to the place they are applied to
    /// 2. `a` *imposes* a subset of `b`'s restrictions on other places
    /// 3. `a` and `b` are 'layout compatible' -- i.e., for all types `T`, `a T` and `b T` have the same layout
    ///
    /// Permissions can be `move` or `copy` and correspond to the columns in the permission matrix.
    ///
    /// Restrictions correspond to read or read/write restrictions on places. e.g., `shared[p]` imposes a read
    /// striction on `p`, meaning that only reads from `p` are allowed so long as a `shared[p]` value is live.
    fn lien_covered_by(
        env: Env,
        a: Lien,
        b: Lien,
    ) => () {
        debug(a, b, env)

        trivial(a == b => ())

        // if `a` is `copy + owned`, it must be `our`, and so is covered by anything meeting `copy` bound:
        // 1. `our` gives `copy` permissions and so does anything meeting `copy` bound
        // 2. `our` imposes no restrictions so it must be a subset of the restrictions imposed by `sup_lien`.
        // 3. everything `copy` is by value
        (
            (lien_is_copy(&env, &a) => ())
            (lien_is_owned(&env, &a) => ())
            (lien_is_copy(&env, &b) => ())
            ------------------------------- ("our-copy")
            (lien_covered_by(env, a, b) => ())
        )

        // if `a` is `move + owned`, it must be `my`, so if both `a` and `b` are `my`, they are equal.
        //
        // Note that `move + owned <= move` is false (unlike with `copy`) because `my` and `leased`
        // are not layout compatible, failing condition 3.
        (
            (lien_is_move(&env, &a) => ())
            (lien_is_owned(&env, &a) => ())
            (lien_is_move(&env, &b) => ())
            (lien_is_owned(&env, &b) => ())
            ------------------------------- ("my-var-my-var")
            (lien_covered_by(env, Lien::Var(a), Lien::Var(b)) => ())
        )

        // e.g., `shared[a.b]` is covered by `shared[a]`:
        // 1. both give `copy` permissions
        // 2. `shared[a.b]` imposes a read restriction on `a.b`
        //    but `shared[a]` imposes a read striction on all of `a`.
        // 3. everything `copy` (including `shared`) is by value
        (
            (if place_covered_by_place(&a, &b))
            ------------------------------- ("shared-shared")
            (lien_covered_by(_env, Lien::Shared(a), Lien::Shared(b)) => ())
        )

        // e.g., `leased[a.b]` is covered by `leased[a]`:
        // 1. both give `move` permissions
        // 2. `leased[a.b]` imposes a read/write restriction on `a.b`
        //    but `leased[a]` imposes a read/write restriction on all of `a`.
        // 3. everything leased is by value
        (
            (if place_covered_by_place(&a, &b))
            ------------------------------- ("lease-lease")
            (lien_covered_by(_env, Lien::Leased(a), Lien::Leased(b)) => ())
        )
    }
}

judgment_fn! {
    /// A lien `a` is *copy* if it corresponds to a permission from the
    /// `copy` column of the permission matrix. All such permissions:
    /// * permit reads but not writes from the place they are applied to
    /// * permit the place they are applied to to be duplicated
    fn lien_is_copy(
        env: Env,
        a: Lien,
    ) => () {
        debug(a, env)

        (
            ------------------------------- ("our is copy")
            (lien_is_copy(_env, Lien::Our) => ())
        )

        (
            ------------------------------- ("shared is copy")
            (lien_is_copy(_env, Lien::Shared(_)) => ())
        )

        (
            (prove_predicate(env, Predicate::copy(v)) => ())
            ------------------------------- ("var is copy")
            (lien_is_copy(_env, Lien::Var(v)) => ())
        )
    }
}

judgment_fn! {
    /// A lien `a` is *move* if it corresponds to a permission from the
    /// `move` column of the permission matrix. All such permissions:
    /// * permit reads and writes from the place they are applied to
    /// * forbid the place they are applied to to be duplicated
    fn lien_is_move(
        env: Env,
        a: Lien,
    ) => () {
        debug(a, env)

        (
            ------------------------------- ("leased is move")
            (lien_is_move(_env, Lien::Leased(_)) => ())
        )

        (
            (prove_predicate(env, Predicate::moved(v)) => ())
            ------------------------------- ("var is move")
            (lien_is_move(_env, Lien::Var(v)) => ())
        )
    }
}

judgment_fn! {
    /// A lien `a` is *owned* if it corresponds to the owned row
    /// of the permission matrix (`my` or `our`). All such permissions
    /// impose no restrictions on any places in the environment.
    fn lien_is_owned(
        env: Env,
        a: Lien,
    ) => () {
        debug(a, env)

        (
            ------------------------------- ("our is owned")
            (lien_is_owned(_env, Lien::Our) => ())
        )

        (
            (prove_predicate(env, Predicate::owned(v)) => ())
            ------------------------------- ("var is owned")
            (lien_is_owned(_env, Lien::Var(v)) => ())
        )
    }
}

/// A place P1 *covers* a place P2 if it is a prefix:
/// for example, `x.y` covers `x.y` and `x.y.z` but not `x.z` or `x1`.
#[tracing::instrument(level = "Debug", ret)]
fn place_covered_by_place(place: &Place, covering_place: &Place) -> bool {
    covering_place.is_prefix_of(place)
}
