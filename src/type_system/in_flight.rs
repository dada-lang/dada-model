use formality_core::{seq, Map, Set, Upcast};

use crate::grammar::{
    FieldDecl, LocalVariableDecl, NamedTy, Parameter, Perm, Place, Predicate, ThisDecl, Ty, Var,
};

pub trait InFlight: Sized {
    fn with_place_in_flight(&self, place: impl Upcast<Place>) -> Self {
        let place = place.upcast();
        self.with_places_transformed(Transform::Give(&place))
    }

    fn with_in_flight_stored_to(&self, place: impl Upcast<Place>) -> Self {
        let place = place.upcast();
        self.with_places_transformed(Transform::Put(&[Var::InFlight], &[place]))
    }

    fn with_this_stored_to(&self, place: impl Upcast<Place>) -> Self {
        let place = place.upcast();
        self.with_places_transformed(Transform::Put(&[Var::This], &[place]))
    }

    fn with_var_stored_to(&self, input: impl Upcast<Var>, place: impl Upcast<Place>) -> Self {
        self.with_vars_stored_to(vec![input], vec![place])
    }

    fn with_vars_stored_to(
        &self,
        inputs: impl Upcast<Vec<Var>>,
        places: impl Upcast<Vec<Place>>,
    ) -> Self {
        let inputs = inputs.upcast();
        let places = places.upcast();
        self.with_places_transformed(Transform::Put(&inputs, &places))
    }

    fn with_places_transformed(&self, transform: Transform<'_>) -> Self;
}

#[derive(Copy, Clone)]
pub enum Transform<'a> {
    Give(&'a Place),
    Put(&'a [Var], &'a [Place]),
}

impl<T> InFlight for Option<T>
where
    T: InFlight,
{
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        self.as_ref().map(|e| e.with_places_transformed(transform))
    }
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

impl<K, V> InFlight for Map<K, V>
where
    K: InFlight + Ord,
    V: InFlight,
{
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        self.iter()
            .map(|(k, v)| {
                (
                    k.with_places_transformed(transform),
                    v.with_places_transformed(transform),
                )
            })
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
            Perm::Our => Perm::Our,
            Perm::Mv(places) => Perm::Mv(places.with_places_transformed(transform)),
            Perm::Rf(places) => Perm::Rf(places.with_places_transformed(transform)),
            Perm::Mt(places) => Perm::Mt(places.with_places_transformed(transform)),
            Perm::Var(v) => Perm::Var(v.clone()),
            Perm::Apply(l, r) => Perm::Apply(
                l.with_places_transformed(transform).into(),
                r.with_places_transformed(transform).into(),
            ),
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

            Transform::Put(vars, places) => {
                if let Some(index) = vars.iter().position(|var| self.var == *var) {
                    let place = &places[index];
                    Place::new(&place.var, seq![..&place.projections, ..&self.projections])
                } else {
                    self.clone()
                }
            }
        }
    }
}

impl InFlight for Predicate {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        match self {
            Predicate::Parameter(kind, parameter) => {
                Predicate::Parameter(*kind, parameter.with_places_transformed(transform))
            }
            Predicate::Variance(kind, parameter) => {
                Predicate::Variance(*kind, parameter.with_places_transformed(transform))
            }
        }
    }
}

impl InFlight for Var {
    fn with_places_transformed(&self, _transform: Transform<'_>) -> Self {
        self.clone()
    }
}

impl<A: InFlight, B: InFlight> InFlight for (A, B) {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        (
            self.0.with_places_transformed(transform),
            self.1.with_places_transformed(transform),
        )
    }
}

impl<A: InFlight, B: InFlight, C: InFlight> InFlight for (A, B, C) {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        (
            self.0.with_places_transformed(transform),
            self.1.with_places_transformed(transform),
            self.2.with_places_transformed(transform),
        )
    }
}

impl InFlight for FieldDecl {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        FieldDecl {
            atomic: self.atomic.clone(),
            name: self.name.clone(),
            ty: self.ty.with_places_transformed(transform),
        }
    }
}

impl InFlight for ThisDecl {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        ThisDecl {
            perm: self.perm.with_places_transformed(transform),
        }
    }
}
