//! Resolve permissions before removing the variables they depend on.
use anyhow::{bail, ensure, Result};
use formality_core::Upcast;

use super::{
    env::Env,
    liveness::LivePlaces,
    predicates::{prove_is_mut, prove_is_shareable},
    redperms::{red_perm, RedChain, RedLink},
};
use crate::grammar::{ty_impls::PermTy, Parameter, Perm, Ty, Var};

/// Normalize the complete type, including type and permission arguments.
/// The environment must still contain every variable being popped.
pub fn normalize_ty_for_pop(
    env: &Env,
    live_after: &LivePlaces,
    ty: &Ty,
    popped_vars: &[Var],
) -> Result<Ty> {
    let PermTy(perm, base) = ty.upcast();
    let perm = normalize_perm_for_pop(env, live_after, &perm, popped_vars)?;
    let base = match base {
        Ty::NamedTy(mut named) => {
            named.parameters = named
                .parameters
                .iter()
                .map(|p| match p {
                    Parameter::Ty(ty) => Ok(Parameter::Ty(normalize_ty_for_pop(
                        env,
                        live_after,
                        ty,
                        popped_vars,
                    )?)),
                    Parameter::Perm(perm) => Ok(Parameter::Perm(normalize_perm_for_pop(
                        env,
                        live_after,
                        perm,
                        popped_vars,
                    )?)),
                })
                .collect::<Result<_>>()?;
            Ty::NamedTy(named)
        }
        Ty::Var(_) => base,
        Ty::ApplyPerm(..) => unreachable!("PermTy removes outer permissions"),
    };
    Ok(PermTy(perm, base).upcast())
}

fn normalize_perm_for_pop(
    env: &Env,
    live_after: &LivePlaces,
    perm: &Perm,
    popped_vars: &[Var],
) -> Result<Perm> {
    let (reduced, _) = red_perm(env, live_after, perm).into_singleton()?;
    let perms = reduced
        .chains
        .into_iter()
        .map(|chain| Ok(strip_popped_dead_links(env, &chain, popped_vars)?.upcast()))
        .collect::<Result<Vec<Perm>>>()?;
    let mut perms: formality_core::Set<Perm> = perms.into_iter().collect();
    if perms.len() == 1 {
        Ok(perms.pop_first().unwrap())
    } else {
        Ok(Perm::Or(perms))
    }
}

fn strip_popped_dead_links(env: &Env, chain: &RedChain, popped_vars: &[Var]) -> Result<RedChain> {
    let mut links = vec![];
    for (index, link) in chain.links.iter().enumerate() {
        let place = match link {
            RedLink::Rfd(p)
            | RedLink::Mtd(p)
            | RedLink::Rfl(p)
            | RedLink::Mtl(p)
            | RedLink::Mv(p)
                if popped_vars.contains(&p.var) =>
            {
                p
            }
            _ => {
                links.push(link.clone());
                continue;
            }
        };
        match link {
            RedLink::Mv(_) => panic!("unexpanded move link in {chain:?}"),
            RedLink::Rfl(_) | RedLink::Mtl(_) => {
                bail!("dangling borrow: live link to {place:?} in {chain:?}")
            }
            _ => {}
        }
        let ty = env.place_ty(place)?;
        ensure!(
            prove_is_shareable(env, &ty).into_singleton().is_ok(),
            "dangling borrow: {place:?} of type {ty:?} is not shareable in {chain:?}"
        );
        let tail = RedChain {
            links: chain.links[index + 1..].to_vec(),
        };
        ensure!(
            prove_is_mut(env, &tail).into_singleton().is_ok(),
            "dangling borrow: {place:?} has no mut-based tail in {chain:?}"
        );
        if matches!(link, RedLink::Rfd(_)) {
            links.push(RedLink::Shared);
        }
    }
    Ok(RedChain { links })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{dada_lang::term, grammar::Program};

    fn env() -> Env {
        let program: Program =
            term("class Data {} given class Guard {} class Wrap[ty T, perm P] {}");
        let mut env = Env::new(program);
        for (name, ty) in [
            ("a", "Data"),
            ("b", "Data"),
            ("x", "mut[a] Data"),
            ("y", "mut[b] Data"),
            ("guard", "Guard"),
        ] {
            env = env
                .push_local_variable(term::<Var>(name), term::<Ty>(ty))
                .unwrap();
        }
        env
    }

    #[test]
    fn resolved_permissions_and_nested_arguments() {
        let env = env();
        let popped = [term::<Var>("x"), term::<Var>("y")];
        for (input, expected) in [
            ("mut[x, y] Data", "or(mut[a], mut[b]) Data"),
            ("ref[x, y] Data", "or(shared mut[a], shared mut[b]) Data"),
            (
                "Wrap[ref[x] Data, mut[y]]",
                "Wrap[shared mut[a] Data, mut[b]]",
            ),
            ("given_from[a, b] Data", "Data"),
        ] {
            let actual =
                normalize_ty_for_pop(&env, &LivePlaces::default(), &term(input), &popped).unwrap();
            assert_eq!(actual, term::<Ty>(expected));
        }
    }

    #[test]
    fn guard_link_cannot_be_stripped() {
        let env = env();
        let popped = [term::<Var>("guard")];
        for input in ["mut[guard] mut[a] Data", "ref[guard] mut[a] Data"] {
            let error = normalize_ty_for_pop(&env, &LivePlaces::default(), &term(input), &popped)
                .unwrap_err();
            assert!(error.to_string().contains("not shareable"), "{error:?}");
        }
    }
}
