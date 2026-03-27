//! Normalization of types at scope-pop boundaries.
//!
//! When a method call returns, the fresh temporary variables used for
//! parameters go out of scope. The return type may reference those
//! temporaries (via `ref[temp]`, `mut[temp]`, `given_from[temp]`).
//! This module resolves those references by:
//!
//! 1. Expanding permissions via `red_perm` (which handles `given_from`
//!    replacement and ref/mut chain extension)
//! 2. Stripping dead links to popped variables
//! 3. Converting back to `Perm` (multiple chains become `Perm::Or`)

use formality_core::{judgment_fn, Cons, Upcast};

use crate::grammar::{NamedTy, Parameter, Perm, Ty, Var};

use super::{
    env::Env,
    liveness::LivePlaces,
    predicates::prove_is_copy,
    redperms::{dead_link_is_strippable, red_perm, Given, Head, RedChain, RedLink, RedPerm, Tail},
};

judgment_fn! {
    /// Normalize a type for popping the given variables.
    ///
    /// Walks the type structure, normalizing each permission that references
    /// any of the `popped_vars`. Permissions that don't reference popped vars
    /// are left unchanged.
    pub fn normalize_ty_for_pop(
        env: Env,
        live_after: LivePlaces,
        ty: Ty,
        popped_vars: Vec<Var>,
    ) => Ty {
        debug(ty, popped_vars, env, live_after)

        // NamedTy: normalize each parameter recursively.
        (
            (let NamedTy { name, parameters } = named_ty)
            (normalize_params_for_pop(env, live_after, parameters, popped_vars) => norm_params)
            --- ("named")
            (normalize_ty_for_pop(env, live_after, Ty::NamedTy(named_ty), popped_vars)
                => Ty::NamedTy(NamedTy { name: name.clone(), parameters: norm_params.to_vec() }))
        )

        // Type variable: pass through unchanged.
        (
            --- ("var")
            (normalize_ty_for_pop(_env, _live_after, Ty::Var(v), _popped_vars) => Ty::var(v))
        )

        // ApplyPerm where inner type is copy: strip the permission entirely.
        (
            (normalize_ty_for_pop(env, live_after, Ty::clone(inner_ty), popped_vars) => new_ty)
            (prove_is_copy(env, Parameter::ty(new_ty)) => ())
            --- ("apply_perm_copy")
            (normalize_ty_for_pop(env, live_after, Ty::ApplyPerm(_perm, inner_ty), popped_vars) => new_ty)
        )

        // ApplyPerm where inner type is NOT copy: normalize both perm and inner type.
        (
            (normalize_ty_for_pop(env, live_after, Ty::clone(inner_ty), popped_vars) => new_ty)
            (if !prove_is_copy(&env, &Parameter::ty(&new_ty)).is_proven())
            (normalize_perm_for_pop(env, live_after, Perm::clone(perm), popped_vars) => new_perm)
            --- ("apply_perm")
            (normalize_ty_for_pop(env, live_after, Ty::ApplyPerm(perm, inner_ty), popped_vars)
                => Ty::apply_perm(new_perm, new_ty))
        )
    }
}

judgment_fn! {
    /// Normalize a list of parameters for popping.
    fn normalize_params_for_pop(
        env: Env,
        live_after: LivePlaces,
        params: Vec<Parameter>,
        popped_vars: Vec<Var>,
    ) => Vec<Parameter> {
        debug(params, popped_vars, env, live_after)

        // Base case: empty parameter list.
        (
            --- ("nil")
            (normalize_params_for_pop(_env, _live_after, (), _popped_vars) => Vec::<Parameter>::new())
        )

        // Recursive: normalize head, then tail, then combine.
        (
            (normalize_param_for_pop(env, live_after, param, popped_vars) => norm_param)
            (normalize_params_for_pop(env, live_after, rest, popped_vars) => norm_rest)
            (let result: Vec<Parameter> = std::iter::once(Parameter::clone(&norm_param)).chain(norm_rest.iter().cloned()).collect())
            --- ("cons")
            (normalize_params_for_pop(env, live_after, Cons(param, rest), popped_vars) => result)
        )
    }
}

judgment_fn! {
    /// Normalize a single parameter for popping.
    fn normalize_param_for_pop(
        env: Env,
        live_after: LivePlaces,
        param: Parameter,
        popped_vars: Vec<Var>,
    ) => Parameter {
        debug(param, popped_vars, env, live_after)

        (
            (normalize_ty_for_pop(env, live_after, ty, popped_vars) => norm_ty)
            --- ("ty")
            (normalize_param_for_pop(env, live_after, Parameter::Ty(ty), popped_vars) => Parameter::ty(norm_ty))
        )

        (
            (normalize_perm_for_pop(env, live_after, perm, popped_vars) => norm_perm)
            --- ("perm")
            (normalize_param_for_pop(env, live_after, Parameter::Perm(perm), popped_vars) => Parameter::perm(norm_perm))
        )
    }
}

judgment_fn! {
    /// Normalize a permission for popping.
    ///
    /// If the permission doesn't reference any popped vars, returns it unchanged.
    /// Otherwise, expands via `red_perm`, strips dead links to popped vars,
    /// and converts back to `Perm`.
    fn normalize_perm_for_pop(
        env: Env,
        live_after: LivePlaces,
        perm: Perm,
        popped_vars: Vec<Var>,
    ) => Perm {
        debug(perm, popped_vars, env, live_after)

        // Perm doesn't reference popped vars → return unchanged.
        (
            (if !perm_references_vars(&perm, &popped_vars))
            --- ("no popped refs")
            (normalize_perm_for_pop(_env, _live_after, perm, _popped_vars) => perm)
        )

        // Perm references popped vars → expand via red_perm, strip all chains, convert back.
        (
            (if perm_references_vars(&perm, &popped_vars))
            (red_perm(env, live_after, perm) => red)
            (let chains_vec: Vec<RedChain> = RedPerm::clone(&red).chains.into_iter().collect())
            (strip_all_chains(env, chains_vec, popped_vars) => stripped_vec)
            (let stripped_perm = red_perm_to_perm(RedPerm { chains: stripped_vec.iter().cloned().collect() }))
            --- ("normalize via red_perm")
            (normalize_perm_for_pop(env, live_after, perm, popped_vars) => stripped_perm)
        )
    }
}

judgment_fn! {
    /// Strip all chains in a list. Every chain must strip successfully —
    /// if any chain can't be stripped (dangling borrow), the judgment fails.
    fn strip_all_chains(
        env: Env,
        chains: Vec<RedChain>,
        popped_vars: Vec<Var>,
    ) => Vec<RedChain> {
        debug(chains, popped_vars, env)

        (
            --- ("nil")
            (strip_all_chains(_env, (), _popped_vars) => Vec::<RedChain>::new())
        )

        (
            (strip_popped_dead_links(env, chain, popped_vars) => stripped)
            (strip_all_chains(env, rest, popped_vars) => stripped_rest)
            (let result: Vec<RedChain> = std::iter::once(RedChain::clone(&stripped)).chain(stripped_rest.iter().cloned()).collect())
            --- ("cons")
            (strip_all_chains(env, Cons(chain, rest), popped_vars) => result)
        )
    }
}

judgment_fn! {
    /// Strip dead links to popped variables from a single chain.
    ///
    /// Recursively processes the chain, applying stripping rules for dead links
    /// whose place is in `popped_vars`:
    /// - `Mtd(popped) :: tail` → drop `Mtd(popped)`, keep stripped tail
    ///   (requires shareable type + mut-based tail via `dead_link_is_strippable`)
    /// - `Rfd(popped) :: tail` → replace `Rfd(popped)` with `Shared`, keep stripped tail
    ///   (same conditions via `dead_link_is_strippable`)
    ///
    /// Links NOT referencing popped vars are kept as-is.
    /// Dangling borrows (live links to popped vars, or dead links that can't be
    /// stripped) cause judgment failure — no applicable rule matches.
    fn strip_popped_dead_links(
        env: Env,
        chain: RedChain,
        popped_vars: Vec<Var>,
    ) => RedChain {
        debug(chain, popped_vars, env)

        // Base case: empty chain (given) — nothing to strip.
        (
            --- ("given")
            (strip_popped_dead_links(_env, Given(), _popped_vars) => RedChain::given())
        )

        // Dead mut to popped var, strippable → drop the Mtd link, strip the tail.
        (
            (if popped_vars.contains(&place.var))!
            (dead_link_is_strippable(env, place, tail) => ())
            (strip_popped_dead_links(env, tail, popped_vars) => stripped)
            --- ("drop dead mut to popped")
            (strip_popped_dead_links(env, Head(RedLink::Mtd(place), Tail(tail)), popped_vars) => stripped)
        )

        // Dead ref to popped var, strippable → replace Rfd with Shared, strip the tail.
        (
            (if popped_vars.contains(&place.var))!
            (dead_link_is_strippable(env, place, tail) => ())
            (strip_popped_dead_links(env, tail, popped_vars) => stripped)
            --- ("weaken dead ref to shared")
            (strip_popped_dead_links(env, Head(RedLink::Rfd(place), Tail(tail)), popped_vars) => RedChain::cons(RedLink::Shared, stripped))
        )

        // Link does NOT reference a popped var → keep it, strip the tail.
        (
            (if !link_references_popped(&link, &popped_vars))
            (strip_popped_dead_links(env, tail, popped_vars) => stripped)
            --- ("keep non-popped link")
            (strip_popped_dead_links(env, Head(link, Tail(tail)), popped_vars) => RedChain::cons(link, stripped))
        )
    }
}

/// Check if a permission references any of the given variables.
fn perm_references_vars(perm: &Perm, vars: &[Var]) -> bool {
    match perm {
        Perm::Given | Perm::Shared => false,
        Perm::Var(_) => false,
        Perm::Mv(places) | Perm::Rf(places) | Perm::Mt(places) => {
            places.iter().any(|p| vars.contains(&p.var))
        }
        Perm::Apply(l, r) => perm_references_vars(l, vars) || perm_references_vars(r, vars),
        Perm::Or(perms) => perms.iter().any(|p| perm_references_vars(p, vars)),
    }
}

/// Check if a link references any of the popped variables.
fn link_references_popped(link: &RedLink, popped_vars: &[Var]) -> bool {
    match link {
        RedLink::Rfl(p) | RedLink::Rfd(p) | RedLink::Mtl(p) | RedLink::Mtd(p) | RedLink::Mv(p) => {
            popped_vars.contains(&p.var)
        }
        RedLink::Shared | RedLink::Var(_) => false,
    }
}

/// Convert a `RedPerm` (set of chains) back to a single `Perm`.
/// Single chain → unwrap via `UpcastFrom<RedChain>`.
/// Multiple chains → `Perm::Or`.
fn red_perm_to_perm(red_perm: RedPerm) -> Perm {
    let chains: Vec<RedChain> = red_perm.chains.into_iter().collect();
    match chains.len() {
        0 => Perm::Given, // empty set → given (shouldn't happen in practice)
        1 => chains.into_iter().next().unwrap().upcast(),
        _ => {
            let perms: Vec<Perm> = chains.into_iter().map(|c| c.upcast()).collect();
            Perm::flat_or(perms)
        }
    }
}
