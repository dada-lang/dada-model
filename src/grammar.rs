pub use crate::dada_lang::grammar::*;
use crate::dada_lang::FormalityLang;
use formality_core::term;
use std::sync::Arc;

mod cast_impls;

#[cfg(test)]
mod test_parse;

#[term($*decls)]
pub struct Program {
    pub decls: Vec<Decl>,
}

#[term]
pub enum Decl {
    #[cast]
    ClassDecl(ClassDecl),

    #[cast]
    FnDecl(FnDecl),
}

#[term(class $name $binder)]
pub struct ClassDecl {
    pub name: ValueId,
    pub binder: Binder<ClassDeclBoundData>,
}

#[term({ $*fields })]
pub struct ClassDeclBoundData {
    pub fields: Vec<FieldDecl>,
}

#[term($name : $ty ;)]
pub struct FieldDecl {
    pub name: FieldId,
    pub ty: Ty,
}

#[term(fn $name $binder)]
pub struct FnDecl {
    pub name: ValueId,
    pub binder: FnDeclBoundData,
}

#[term($(inputs) -> $output $body)]
pub struct FnDeclBoundData {
    pub inputs: Vec<VariableDecl>,
    pub output: Ty,
    pub body: Block,
}

#[term($name : $ty)]
pub struct VariableDecl {
    pub name: ValueId,
    pub ty: Ty,
}

#[term({ $*statements })]
pub struct Block {
    statements: Vec<Statement>,
}

#[term]
pub enum Statement {
    #[grammar($v0 ;)]
    #[cast]
    Expr(Expr),

    #[grammar(let $v0 = $v1 ;)]
    Let(Place, Arc<Expr>),

    #[grammar($v0 = $v1 ;)]
    Reassign(Place, Expr),

    #[grammar(loop { $v0 })]
    Loop(Arc<Expr>),

    #[grammar(break)]
    Break,
}

#[term]
pub enum Expr {
    #[cast]
    Block(Block),

    #[grammar($v0)]
    Integer(usize),

    #[cast]
    Place(PlaceExpr),

    #[grammar(($*v0))]
    Tuple(Vec<Expr>),

    #[grammar($v0 $(v1))]
    Call(Arc<Expr>, Vec<Expr>),

    // FIXME: the ambiguity rules for formality-core prevent
    // me from doing `$v0.await` without a custom parse impl
    #[grammar(await $v0)]
    Await(Place),

    #[grammar($$clear($v0))]
    Clear(ValueId),

    #[grammar(if $v0 { $v1 } else { $v2 })]
    If(Arc<Expr>, Arc<Expr>, Arc<Expr>),
}

#[term]
pub enum PlaceExpr {
    #[grammar($v0)]
    Share(Place),
    #[grammar($v0.give)]
    Give(Place),
    #[grammar($v0.lease)]
    Lease(Place),
}

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
    pub id: ClassName,
    pub parameters: Parameters,
}

#[term]
pub enum ClassName {
    Tuple(usize),

    Int,

    #[cast]
    Id(TyId),
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
    pub var: ValueId,
    pub projections: Vec<Projection>,
}

#[term]
pub enum Projection {
    #[grammar(. $v0)]
    Field(FieldId),
}

formality_core::id!(BasicBlockId);
formality_core::id!(TyId);
formality_core::id!(ValueId);
formality_core::id!(FieldId);
