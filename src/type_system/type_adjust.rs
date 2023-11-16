use std::sync::Arc;

use formality_core::Upcast;

use crate::{
    dada_lang::grammar::Variable,
    grammar::{Perm, Place, Ty},
};

impl Ty {
    pub fn is_simplified(&self) -> bool {
        *self == self.simplify()
    }

    pub fn simplify(&self) -> Self {
        todo!()
    }
}

impl Perm {
    pub fn simplify(&self) -> Perm {
        match self {
            Perm::My | Perm::Var(_) => self.clone(),
            Perm::Shared(places, perm) => {
                let perm = perm.simplify();
                if let Perm::Shared(..) = perm {
                    perm
                } else {
                    Perm::shared(places, perm)
                }
            }
            Perm::Leased(places, perm) => {
                let perm = perm.simplify();
                if let Perm::Shared(..) = perm {
                    perm
                } else {
                    Perm::leased(places, perm)
                }
            }
        }
    }
}
