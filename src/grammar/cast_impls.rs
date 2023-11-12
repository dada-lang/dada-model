use super::*;
use formality_core::{cast_impl, Downcast, DowncastTo, Upcast, UpcastFrom};

impl UpcastFrom<Variable> for Parameter {
    fn upcast_from(term: Variable) -> Self {
        match term.kind() {
            Kind::Ty => Ty::Var(term).upcast(),
            Kind::Perm => Perm::Var(term).upcast(),
        }
    }
}

impl DowncastTo<Variable> for Parameter {
    fn downcast_to(&self) -> Option<Variable> {
        match self {
            Parameter::Ty(t) => t.downcast(),
            Parameter::Perm(p) => p.downcast(),
        }
    }
}

cast_impl!((BoundVar) <: (Variable) <: (Parameter));
cast_impl!((ExistentialVar) <: (Variable) <: (Parameter));
cast_impl!((UniversalVar) <: (Variable) <: (Parameter));
