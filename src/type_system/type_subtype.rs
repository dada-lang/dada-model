use anyhow::bail;
use contracts::requires;
use formality_core::{judgment_fn, Fallible};

use crate::{
    dada_lang::grammar::Variable,
    grammar::{ClassTy, Parameter, Perm, Place, Ty},
    type_system::env::Env,
};

impl Env {
    pub fn assignable(&mut self, from: &Parameter, to: &Parameter) -> Fallible<()> {
        match (from, to) {
            _ if from == to => Ok(()),
            (Parameter::Ty(a), Parameter::Ty(b)) => {
                self.assignable_types(&a.simplify(), &b.simplify())
            }
            (Parameter::Perm(a), Parameter::Perm(b)) => {
                self.assignable_perms(&a.simplify(), &b.simplify())
            }
            _ => panic!("mismatched kinds: `{from:?}` vs `{to:?}`"),
        }
    }

    #[requires(from.is_simplified() && matches!(from, Ty::ApplyPerm(..)))]
    #[requires(to.is_simplified() && matches!(to, Ty::ApplyPerm(..)))]
    fn assignable_types(&mut self, from: &Ty, to: &Ty) -> Fallible<()> {
        match (from, to) {
            (Ty::ApplyPerm(perm_from, ty_from), Ty::ApplyPerm(perm_to, ty_to)) => {
                self.assignable_perms(perm_from, perm_to)?;
                self.assignable_type_atoms(&ty_from, &ty_to)?;
                Ok(())
            }

            _ => bail!("cannot assign a value of type `{from:?}` to a location of type `{to:?}`"),
        }
    }

    #[requires(!matches!(from, Ty::ApplyPerm(..)))]
    #[requires(!matches!(to, Ty::ApplyPerm(..)))]
    fn assignable_type_atoms(&mut self, from: &Ty, to: &Ty) -> Fallible<()> {
        match (from, to) {
            _ if from == to => Ok(()),

            (
                Ty::ClassTy(ClassTy {
                    name: name_from,
                    parameters: parameters_from,
                }),
                Ty::ClassTy(ClassTy {
                    name: name_to,
                    parameters: parameters_to,
                }),
            ) => {
                if name_from == name_to {
                    assert_eq!(parameters_from.len(), parameters_to.len());
                    for (parameter_from, parameter_to) in parameters_from.iter().zip(parameters_to)
                    {
                        // FIXME: variance
                        self.assignable(parameter_from, parameter_to)?;
                    }
                    Ok(())
                } else {
                    bail!("FIXME: upcasting")
                }
            }

            // FIXME: relations between existential variables
            _ => bail!(
                "cannot assign from a value of type `{from:?}` to a location of type `{to:?}`"
            ),
        }
    }

    #[requires(from.is_simplified())]
    #[requires(to.is_simplified())]
    fn assignable_perms(&mut self, from: &Perm, to: &Perm) -> Fallible<()> {
        if from == to {
            return Ok(());
        }

        macro_rules! bail_because {
            ($($b:tt)*) => {
                bail!("cannot assign from a value with perms `{from:?}` to a location with perms `{to:?}`: {}", format!($($b)*))
            }
        }

        match (from, to) {
            (Perm::Owned, Perm::Owned) => Ok(()),

            (Perm::Owned, Perm::Shared(_, to1)) => Ok(()),

            (Perm::Owned, Perm::Leased(_, _)) => {
                bail_because!(
                    "owned is not a subpermission of leased, memory representation differs"
                )
            }

            (Perm::Shared(_, _), Perm::Owned) => {
                bail_because!("shared permissions are not assigned to owned")
            }

            (Perm::Shared(places_a, subperm_a), Perm::Shared(places_b, subperm_b)) => {
                require_all_places_covered_by_one_of(places_a, places_b)?;
                self.assignable_perms(subperm_a, subperm_b)?;
                Ok(())
            }

            (Perm::Leased(places_a, subperm_a), Perm::Leased(places_b, subperm_b)) => {
                if require_all_places_covered_by_one_of(places_a, places_b).is_ok() {
                    self.assignable_perms(subperm_a, subperm_b)
                } else {
                    todo!()
                }
            }

            (Perm::Leased(_, _), other @ Perm::Shared(_, _))
            | (Perm::Leased(_, _), other @ Perm::Owned)
            | (other @ Perm::Shared(_, _), Perm::Leased(_, _)) => {
                bail_because!("leased has a distinct memory representation from `{other:?}`")
            }

            (Perm::Var(Variable::UniversalVar(var), _), other @ Perm::Owned)
            | (Perm::Var(Variable::UniversalVar(var), _), other @ Perm::Shared(_, _))
            | (Perm::Var(Variable::UniversalVar(var), _), other @ Perm::Leased(_, _))
            | (other @ Perm::Owned, Perm::Var(Variable::UniversalVar(var), _))
            | (other @ Perm::Leased(_, _), Perm::Var(Variable::UniversalVar(var), _))
            | (other @ Perm::Shared(_, _), Perm::Var(Variable::UniversalVar(var), _)) => {
                bail_because!(
                    "`{other:?}` may have distinctx memory representation from variable `{var:?}`"
                )
            }

            (
                Perm::Var(Variable::UniversalVar(var_from), subperm_from),
                Perm::Var(Variable::UniversalVar(var_to), subperm_to),
            ) => {
                if var_from == var_to {
                    self.assignable_perms(subperm_from, subperm_to)
                } else {
                    bail_because!("distinct universal vars (`{var_from:?}` vs `{var_to:?}`)")
                }
            }
        }
    }
}

/// True if every place listed in `places` is "covered" by one of the places in
/// `covering_places`. A place P1 *covers* a place P2 if it is a prefix:
/// for example, `x.y` covers `x.y` and `x.y.z` but not `x.z` or `x1`.
fn require_all_places_covered_by_one_of(
    places: &[Place],
    covering_places: &[Place],
) -> Fallible<()> {
    for place in places {
        if !place_covered_by_one_of(place, covering_places) {
            bail!("`{place:?}` not covered by one of `{covering_places:?}`")
        }
    }
    Ok(())
}

/// See [`all_places_covered_by_one_of`][].
#[tracing::instrument(level = "Debug", ret)]
fn place_covered_by_one_of(place: &Place, covering_places: &[Place]) -> bool {
    covering_places
        .iter()
        .any(|covering_place| place_covered_by_place(place, covering_place))
}

/// See [`all_places_covered_by_one_of`][].
#[tracing::instrument(level = "Debug", ret)]
fn place_covered_by_place(place: &Place, covering_place: &Place) -> bool {
    place.var == covering_place.var
        && place.projections.len() >= covering_place.projections.len()
        && place
            .projections
            .iter()
            .zip(&covering_place.projections)
            .all(|(proj1, proj2)| proj1 == proj2)
}

#[cfg(test)]
mod tests;
