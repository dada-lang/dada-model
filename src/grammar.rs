pub use crate::dada_lang::grammar::*;
use crate::dada_lang::FormalityLang;
use formality_core::term;

mod cast_impls;

#[cfg(test)]
mod test_parse;

#[term]
pub enum Kind {
    Ty,
    Perm,
}

impl Copy for Kind {}

#[term]
pub enum Parameter {
    #[cast]
    Ty(Ty),

    #[cast]
    Perm(Perm),
}

impl formality_core::language::HasKind<FormalityLang> for Parameter {
    fn kind(&self) -> formality_core::language::CoreKind<FormalityLang> {
        match self {
            Parameter::Ty(_) => Kind::Ty,
            Parameter::Perm(_) => Kind::Perm,
        }
    }
}

#[term]
pub enum Ty {
    #[cast]
    ClassTy(ClassTy),

    #[variable]
    Var(Variable),
}

#[term($perm $id $[?parameters])]
pub struct ClassTy {
    pub perm: Perm,
    pub id: TyId,
    pub parameters: Parameters,
}

pub type Parameters = Vec<Parameter>;

#[term]
pub enum Perm {
    My,

    #[grammar(shared $(?v0))]
    Shared(Vec<Place>),

    #[grammar(leased $(v0))]
    Leased(Vec<Place>),

    #[variable]
    Var(Variable),
}

#[term($var $*projections)]
pub struct Place {
    pub var: VarId,
    pub projections: Vec<Projection>,
}

#[term]
pub enum Projection {
    #[grammar(. $v0)]
    Field(FieldId),
}

formality_core::id!(TyId);
formality_core::id!(VarId);
formality_core::id!(FieldId);
