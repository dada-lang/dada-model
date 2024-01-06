use formality_core::{seq, Set, Upcast};

use crate::grammar::{LocalVariableDecl, NamedTy, Parameter, Perm, Place, Predicate, Ty, Var};

pub trait InFlight: Sized {
    fn with_place_in_flight(&self, place: impl Upcast<Place>) -> Self {
        let place = place.upcast();
        self.with_places_transformed(Transform::Give(&place))
    }

    fn with_in_flight_stored_to(&self, place: impl Upcast<Place>) -> Self {
        let place = place.upcast();
        self.with_places_transformed(Transform::Put(&place))
    }

    fn with_places_transformed(&self, transform: Transform<'_>) -> Self;
}

#[derive(Copy, Clone)]
pub enum Transform<'a> {
    Give(&'a Place),
    Put(&'a Place),
}

impl<T> InFlight for Vec<T>
where
    T: InFlight,
{
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        self.iter()
            .map(|e| e.with_places_transformed(transform))
            .collect()
    }
}

impl<T> InFlight for Set<T>
where
    T: InFlight + Ord,
{
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        self.iter()
            .map(|e| e.with_places_transformed(transform))
            .collect()
    }
}

impl InFlight for LocalVariableDecl {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        LocalVariableDecl {
            name: self.name.clone(),
            ty: self.ty.with_places_transformed(transform),
        }
    }
}

impl InFlight for Parameter {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        match self {
            Parameter::Ty(ty) => ty.with_places_transformed(transform).upcast(),
            Parameter::Perm(perm) => perm.with_places_transformed(transform).upcast(),
        }
    }
}

impl InFlight for Ty {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        match self {
            Ty::NamedTy(n) => n.with_places_transformed(transform).upcast(),
            Ty::Var(v) => Ty::Var(v.clone()),
            Ty::ApplyPerm(perm, ty) => Ty::apply_perm(
                perm.with_places_transformed(transform),
                ty.with_places_transformed(transform),
            ),
        }
    }
}

impl InFlight for NamedTy {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        Self {
            name: self.name.clone(),
            parameters: self.parameters.with_places_transformed(transform),
        }
    }
}

impl InFlight for Perm {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        match self {
            Perm::My => Perm::My,
            Perm::Given(places) => Perm::Given(places.with_places_transformed(transform)),
            Perm::Shared(places) => Perm::Shared(places.with_places_transformed(transform)),
            Perm::Leased(places) => Perm::Leased(places.with_places_transformed(transform)),
            Perm::ShLeased(places) => Perm::ShLeased(places.with_places_transformed(transform)),
            Perm::Var(v) => Perm::Var(v.clone()),
        }
    }
}

impl InFlight for Place {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        match transform {
            Transform::Give(place) => {
                if place.is_prefix_of(self) {
                    Place {
                        var: Var::InFlight,
                        projections: self.projections[place.projections.len()..].to_vec(),
                    }
                } else {
                    self.clone()
                }
            }

            Transform::Put(place) => match self.var {
                Var::InFlight => {
                    Place::new(&place.var, seq![..&place.projections, ..&self.projections])
                }
                _ => self.clone(),
            },
        }
    }
}

impl InFlight for Predicate {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        match self {
            Predicate::Shared(s) => Predicate::Shared(s.with_places_transformed(transform)),
            Predicate::Leased(s) => Predicate::Leased(s.with_places_transformed(transform)),
            Predicate::Mine(s) => Predicate::Mine(s.with_places_transformed(transform)),
        }
    }
}
