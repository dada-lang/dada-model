use super::*;
use formality_core::{cast_impl, Downcast, DowncastTo, Upcast, UpcastFrom};

impl UpcastFrom<TypeName> for NamedTy {
    fn upcast_from(term: TypeName) -> Self {
        NamedTy::new(term, ())
    }
}

impl DowncastTo<TypeName> for NamedTy {
    fn downcast_to(&self) -> Option<TypeName> {
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
            Kind::Perm => Perm::var(term).upcast(),
        }
    }
}

impl DowncastTo<Variable> for Parameter {
    fn downcast_to(&self) -> Option<Variable> {
        match self {
            Parameter::Ty(t) => t.downcast(),
            Parameter::Perm(p) => match p {
                Perm::Var(v) => Some(*v),
                _ => None,
            },
        }
    }
}

impl DowncastTo<UniversalVar> for Ty {
    fn downcast_to(&self) -> Option<UniversalVar> {
        let v: Variable = self.downcast()?;
        v.downcast()
    }
}

cast_impl!((BoundVar) <: (Variable) <: (Parameter));
cast_impl!((ExistentialVar) <: (Variable) <: (Parameter));
cast_impl!((UniversalVar) <: (Variable) <: (Parameter));
cast_impl!((TypeName) <: (NamedTy) <: (Ty));
cast_impl!((NamedTy) <: (Ty) <: (Parameter));
cast_impl!((NamedTy) <: (Ty) <: (Arc<Ty>));
