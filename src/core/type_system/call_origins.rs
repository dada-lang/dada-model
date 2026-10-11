//! Capture-avoiding instantiation of caller-supplied generic arguments.
//!
//! Generic arguments can contain caller places named `self` or the same name as
//! a callee input/local. Protect those places while instantiating the callee and
//! renaming its own bindings, then restore them before any environment lookup.
//! This is equivalent to renaming callee bindings before generic substitution,
//! while preserving existing temporary allocation and interpreter trace names.

use formality_core::{cast_impl, Set};

use crate::grammar::{NamedTy, Parameter, Perm, Ty, ValueId, Var};

use super::in_flight::{InFlight, Transform};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct CallerOrigins {
    caller: Vec<Var>,
    protected: Vec<Var>,
}

cast_impl!(CallerOrigins);

impl CallerOrigins {
    pub(crate) fn new(class_arguments: &[Parameter], method_arguments: &[Parameter]) -> Self {
        let mut places = Set::new();
        for parameter in class_arguments.iter().chain(method_arguments) {
            collect_parameter(parameter, &mut places);
        }
        let caller: Vec<_> = places.into_iter().collect();
        // `$` cannot occur in a source ValueId. Existing internal places use
        // distinct Var variants (Fresh/InFlight/Magic/Return), and interpreter
        // alpha-renaming creates `_depth_name` identifiers. These IDs therefore
        // cannot coincide with any source or runtime binding. They never enter
        // an Env or escape a single signature-instantiation operation; nested
        // calls may safely reuse this private namespace.
        let protected = (0..caller.len())
            .map(|index| Var::Id(ValueId::new(&format!("$caller_origin_{index}"))))
            .collect();
        Self { caller, protected }
    }

    pub(crate) fn protect<T: InFlight>(&self, term: &T) -> T {
        term.with_places_transformed(Transform::Rename(&self.caller, &self.protected))
    }

    pub(crate) fn restore<T: InFlight>(&self, term: &T) -> T {
        term.with_places_transformed(Transform::Rename(&self.protected, &self.caller))
    }
}

fn collect_parameter(parameter: &Parameter, places: &mut Set<Var>) {
    match parameter {
        Parameter::Ty(ty) => collect_type(ty, places),
        Parameter::Perm(perm) => collect_permission(perm, places),
    }
}

fn collect_type(ty: &Ty, places: &mut Set<Var>) {
    match ty {
        Ty::NamedTy(NamedTy { parameters, .. }) => {
            for parameter in parameters {
                collect_parameter(parameter, places);
            }
        }
        Ty::ApplyPerm(perm, ty) => {
            collect_permission(perm, places);
            collect_type(ty, places);
        }
        Ty::Var(_) => {}
    }
}

fn collect_permission(perm: &Perm, places: &mut Set<Var>) {
    match perm {
        Perm::SharedFrom(origins) | Perm::Mv(origins) | Perm::Mt(origins) => {
            places.extend(origins.iter().map(|place| place.var.clone()));
        }
        Perm::Apply(left, right) => {
            collect_permission(left, places);
            collect_permission(right, places);
        }
        Perm::Or(alternatives) => {
            for alternative in alternatives {
                collect_permission(alternative, places);
            }
        }
        Perm::Given | Perm::Shared | Perm::Var(_) => {}
    }
}
