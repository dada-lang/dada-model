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

use anyhow::bail;
use formality_core::{Fallible, Upcast};

use crate::grammar::{NamedTy, Parameter, Perm, Ty, Var};

use super::{
    env::Env,
    liveness::LivePlaces,
    predicates::{prove_is_mut, prove_is_shareable},
    redperms::{red_perm, RedChain, RedLink, RedPerm},
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
            let new_perm = normalize_perm_for_pop(env, live_after, perm, popped_vars)?;
            let new_ty = normalize_ty_for_pop(env, live_after, inner_ty, popped_vars)?;
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
    let mut stripped_chains = Vec::new();
    for chain in &red.chains {
        let stripped = strip_popped_dead_links(env, chain, popped_vars)?;
        stripped_chains.push(stripped);
    }

    // Convert back to Perm
    let stripped_perm = red_perm_to_perm(RedPerm {
        chains: stripped_chains.into_iter().collect(),
    });

    Ok(stripped_perm)
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

/// Strip dead links to popped variables from a single chain.
///
/// Scans the chain for `Rfd`/`Mtd` links where the place's variable is
/// in `popped_vars` and applies stripping rules:
/// - `Mtd(popped) :: tail` → drop `Mtd(popped)`, keep `tail` (if shareable + mut tail)
/// - `Rfd(popped) :: tail` → replace `Rfd(popped)` with `Shared` (if shareable + mut tail)
///
/// Returns error for dangling borrows (chain still references a popped var after stripping).
fn strip_popped_dead_links(
    env: &Env,
    chain: &RedChain,
    popped_vars: &[Var],
) -> Fallible<RedChain> {
    let mut result_links: Vec<RedLink> = Vec::new();

    let links = &chain.links;
    let mut i = 0;
    while i < links.len() {
        let link = &links[i];
        match link {
            RedLink::Mv(place) if popped_vars.contains(&place.var) => {
                // Mv links should have been replaced during red_perm expansion.
                // If we see one here, it's a bug.
                panic!(
                    "BUG: Mv link referencing popped var {:?} survived red_perm expansion",
                    place
                );
            }
            RedLink::Mtd(place) if popped_vars.contains(&place.var) => {
                // Dead mut to popped var: try to strip it.
                let tail = RedChain {
                    links: links[i + 1..].to_vec(),
                };
                let place_ty: Parameter = env.place_ty(place)?.upcast();
                if prove_is_shareable(env, &place_ty).is_proven()
                    && prove_is_mut(env, Parameter::Perm(tail_to_perm(&tail))).is_proven()
                {
                    // Drop Mtd(popped), keep processing tail
                    i += 1;
                    continue;
                } else {
                    bail!(
                        "dangling borrow: chain `{:?}` borrows through `{:?}` which is being popped \
                         (type not shareable or tail not mut-based)",
                        chain, place
                    );
                }
            }
            RedLink::Rfd(place) if popped_vars.contains(&place.var) => {
                // Dead ref to popped var: try to weaken to Shared.
                let tail = RedChain {
                    links: links[i + 1..].to_vec(),
                };
                let place_ty: Parameter = env.place_ty(place)?.upcast();
                if prove_is_shareable(env, &place_ty).is_proven()
                    && prove_is_mut(env, Parameter::Perm(tail_to_perm(&tail))).is_proven()
                {
                    // Replace Rfd(popped) with Shared
                    result_links.push(RedLink::Shared);
                    i += 1;
                    continue;
                } else if tail.links.is_empty() {
                    // ref from given (empty tail) — dangling borrow
                    bail!(
                        "dangling borrow: return type borrows from `{:?}` which has `given` permission \
                         — the borrow would outlive the owned value",
                        place
                    );
                } else {
                    bail!(
                        "dangling borrow: chain `{:?}` borrows through `{:?}` which is being popped \
                         (type not shareable or tail not mut-based)",
                        chain, place
                    );
                }
            }
            RedLink::Rfl(place) | RedLink::Mtl(place) if popped_vars.contains(&place.var) => {
                // Live link to a popped var — should not happen (popped vars are dead)
                bail!(
                    "dangling borrow: live link `{:?}` references popped variable `{:?}`",
                    link, place.var
                );
            }
            _ => {
                // Not a link to a popped var — keep it
                result_links.push(link.clone());
                i += 1;
            }
        }
    }

    Ok(RedChain {
        links: result_links,
    })
}

/// Convert a RedChain tail to a Perm for predicate checking.
fn tail_to_perm(chain: &RedChain) -> Perm {
    chain.clone().upcast()
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
