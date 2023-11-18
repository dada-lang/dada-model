use super::*;
use formality_core::{cast_impl, Downcast, DowncastTo, Upcast, UpcastFrom};

impl UpcastFrom<ClassName> for ClassTy {
    fn upcast_from(term: ClassName) -> Self {
        ClassTy::new(term, ())
    }
}

impl DowncastTo<ClassName> for ClassTy {
    fn downcast_to(&self) -> Option<ClassName> {
        let Self { name, parameters } = self;
        if parameters.is_empty() {
            Some(name.clone())
        } else {
            None
        }
    }
}

impl UpcastFrom<ValueId> for Place {
    fn upcast_from(term: ValueId) -> Self {
        Place::new(term, ())
    }
}

impl UpcastFrom<Variable> for Parameter {
    fn upcast_from(term: Variable) -> Self {
        match term.kind() {
            Kind::Ty => Ty::var(term).upcast(),
            Kind::Perm => Perm::var(term, Perm::Owned).upcast(),
        }
    }
}

impl DowncastTo<Variable> for Parameter {
    fn downcast_to(&self) -> Option<Variable> {
        match self {
            Parameter::Ty(t) => t.downcast(),
            Parameter::Perm(p) => match p {
                Perm::Var(v, p) if matches!(&**p, Perm::Owned) => Some(*v),
                _ => None,
            },
        }
    }
}

cast_impl!((BoundVar) <: (Variable) <: (Parameter));
cast_impl!((ExistentialVar) <: (Variable) <: (Parameter));
cast_impl!((UniversalVar) <: (Variable) <: (Parameter));
cast_impl!((ClassName) <: (ClassTy) <: (Ty));
