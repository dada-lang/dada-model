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

use formality_core::{judgment_fn, Fallible, Upcast};

use crate::grammar::{NamedTy, Parameter, Perm, Ty, Var};

use super::{
    env::Env,
    liveness::LivePlaces,
    predicates::prove_is_copy,
    redperms::{dead_link_is_strippable, red_perm, Given, Head, RedChain, RedLink, RedPerm, Tail},
};

/// Normalize a type for popping the given fresh variables.
///
/// Walks the type structure, normalizing each permission that references
/// any of the `popped_vars`. Permissions that don't reference popped vars
/// are left unchanged.
pub fn normalize_ty_for_pop(
    env: &Env,
    live_after: &LivePlaces,
    ty: &Ty,
    popped_vars: &[Var],
) -> Fallible<Ty> {
    match ty {
        Ty::NamedTy(named_ty) => {
            let mut new_params = Vec::new();
            for param in &named_ty.parameters {
                let new_param = match param {
                    Parameter::Ty(inner_ty) => {
                        Parameter::Ty(normalize_ty_for_pop(env, live_after, inner_ty, popped_vars)?)
                    }
                    Parameter::Perm(perm) => {
                        Parameter::Perm(normalize_perm_for_pop(env, live_after, perm, popped_vars)?)
                    }
                };
                new_params.push(new_param);
            }
            Ok(Ty::NamedTy(NamedTy {
                name: named_ty.name.clone(),
                parameters: new_params,
            }))
        }
        Ty::Var(v) => Ok(Ty::Var(v.clone())),
        Ty::ApplyPerm(perm, inner_ty) => {
            let new_ty = normalize_ty_for_pop(env, live_after, inner_ty, popped_vars)?;
            // If the inner type is copy, the permission is irrelevant — strip it.
            let ty_param: Parameter = new_ty.clone().upcast();
            if prove_is_copy(env, &ty_param).is_proven() {
                return Ok(new_ty);
            }
            let new_perm = normalize_perm_for_pop(env, live_after, perm, popped_vars)?;
            Ok(Ty::apply_perm(new_perm, new_ty))
        }
    }
}

/// Normalize a permission for popping.
///
/// If the permission doesn't reference any popped vars, returns it unchanged.
/// Otherwise, expands via `red_perm`, strips dead links to popped vars,
/// and converts back to `Perm`.
fn normalize_perm_for_pop(
    env: &Env,
    live_after: &LivePlaces,
    perm: &Perm,
    popped_vars: &[Var],
) -> Fallible<Perm> {
    if !perm_references_vars(perm, popped_vars) {
        return Ok(perm.clone());
    }

    // Expand to reduced permissions. The popped vars are dead (not live after
    // the call), so red_perm will classify links to them as Rfd/Mtd.
    let (red, _proof) = red_perm(env, live_after, perm)
        .into_singleton()
        .map_err(|e| anyhow::anyhow!("red_perm failed for {:?}: {:?}", perm, e))?;

    // Strip dead links to popped vars from each chain
    let popped_vec: Vec<Var> = popped_vars.to_vec();
    let mut stripped_chains = Vec::new();
    for chain in &red.chains {
        let (stripped, _proof) = strip_popped_dead_links(env, chain, &popped_vec)
            .into_singleton()
            .map_err(|_| dangling_borrow_error(chain, popped_vars))?;
        stripped_chains.push(stripped);
    }

    // Convert back to Perm
    let stripped_perm = red_perm_to_perm(RedPerm {
        chains: stripped_chains.into_iter().collect(),
    });

    Ok(stripped_perm)
}

/// Produce a clean error message for a chain that couldn't be stripped.
/// Analyzes the chain to determine the specific dangling borrow scenario.
fn dangling_borrow_error(chain: &RedChain, popped_vars: &[Var]) -> anyhow::Error {
    for (i, link) in chain.links.iter().enumerate() {
        match link {
            RedLink::Rfd(place) if popped_vars.contains(&place.var) => {
                let tail = &chain.links[i + 1..];
                if tail.is_empty() {
                    // ref from given (empty tail) — the classic dangling borrow
                    return anyhow::anyhow!(
                        "dangling borrow: return type borrows from `{:?}` which has `given` permission \
                         — the borrow would outlive the owned value",
                        place
                    );
                }
                return anyhow::anyhow!(
                    "dangling borrow: chain `{:?}` borrows through `{:?}` which is being popped \
                     (type not shareable or tail not mut-based)",
                    chain, place
                );
            }
            RedLink::Mtd(place) if popped_vars.contains(&place.var) => {
                return anyhow::anyhow!(
                    "dangling borrow: chain `{:?}` borrows through `{:?}` which is being popped \
                     (type not shareable or tail not mut-based)",
                    chain, place
                );
            }
            RedLink::Rfl(place) | RedLink::Mtl(place) if popped_vars.contains(&place.var) => {
                return anyhow::anyhow!(
                    "dangling borrow: live link `{:?}` references popped variable `{:?}`",
                    link, place.var
                );
            }
            _ => {}
        }
    }
    anyhow::anyhow!(
        "dangling borrow: chain `{:?}` references popped variables",
        chain
    )
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
