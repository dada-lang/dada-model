pub use crate::dada_lang::grammar::*;
use crate::dada_lang::FormalityLang;
use formality_core::{term, variable, Fallible, Set, Upcast};
use std::sync::Arc;

mod cast_impls;

#[cfg(test)]
mod test_parse;

#[term($*decls)]
pub struct Program {
    pub decls: Vec<Decl>,
}

impl Program {
    pub fn class_named(&self, name: &ValueId) -> Fallible<&ClassDecl> {
        self.decls
            .iter()
            .filter_map(|d| d.as_class_decl())
            .filter(|d| d.name == *name)
            .next()
            .ok_or_else(|| anyhow::anyhow!("no class named `{:?}`", name))
    }

    pub fn fn_named(&self, name: &ValueId) -> Fallible<&FnDecl> {
        self.decls
            .iter()
            .filter_map(|d| d.as_fn_decl())
            .filter(|d| d.name == *name)
            .next()
            .ok_or_else(|| anyhow::anyhow!("no fn named `{:?}`", name))
    }
}

#[term]
pub enum Decl {
    #[cast]
    ClassDecl(ClassDecl),

    #[cast]
    FnDecl(FnDecl),
}

// ANCHOR: ClassDecl
#[term(class $name $binder)]
pub struct ClassDecl {
    pub name: ValueId,
    pub binder: Binder<ClassDeclBoundData>,
}

#[term({ $*fields })]
pub struct ClassDeclBoundData {
    pub fields: Vec<FieldDecl>,
}
// ANCHOR_END: ClassDecl

// ANCHOR: FieldDecl
#[term($?atomic $name : $ty ;)]
pub struct FieldDecl {
    pub atomic: Atomic,
    pub name: FieldId,
    pub ty: Ty,
}
// ANCHOR_END: FieldDecl

// ANCHOR: Atomic
#[term]
#[derive(Default)]
pub enum Atomic {
    #[default]
    #[grammar(nonatomic)]
    No,

    #[grammar(atomic)]
    Yes,
}
// ANCHOR_END: Atomic

#[term(fn $name $binder)]
pub struct FnDecl {
    pub name: ValueId,
    pub binder: Binder<FnDeclBoundData>,
}

#[term($(inputs) -> $output $body)]
pub struct FnDeclBoundData {
    pub inputs: Vec<LocalVariableDecl>,
    pub output: Ty,
    pub body: Block,
}

#[term($name : $ty)]
pub struct LocalVariableDecl {
    pub name: ValueId,
    pub ty: Ty,
}

#[term({ $*statements })]
pub struct Block {
    pub statements: Vec<Statement>,
}

#[term]
pub enum Statement {
    #[grammar($v0 ;)]
    #[cast]
    Expr(Expr),

    #[grammar(let $v0 = $v1 ;)]
    Let(ValueId, Arc<Expr>),

    #[grammar($v0 = $v1 ;)]
    Reassign(Place, Expr),

    #[grammar(loop { $v0 })]
    Loop(Arc<Expr>),

    #[grammar(break ;)]
    Break,

    #[grammar(return $v0 ;)]
    Return(Expr),
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

    #[grammar(if $v0 $v1 else $v2)]
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

    #[variable(Kind::Ty)]
    Var(Variable),

    #[grammar($v0 $v1)]
    ApplyPerm(Perm, Arc<Ty>),
}

impl Ty {
    pub fn unit() -> Ty {
        ClassTy {
            name: ClassName::Tuple(0),
            parameters: vec![],
        }
        .upcast()
    }

    pub fn int() -> Ty {
        ClassTy {
            name: ClassName::Int,
            parameters: vec![],
        }
        .upcast()
    }

    pub fn tuple(parameters: impl Upcast<Vec<Ty>>) -> Ty {
        let parameters: Vec<Ty> = parameters.upcast();
        ClassTy {
            name: ClassName::Tuple(parameters.len()),
            parameters: parameters.upcast(),
        }
        .upcast()
    }

    /// Returns a new type that has each of the `ApplyPerm` layers from `self`, but applied to `onto`.
    /// E.g. if `self = shared(x) given(y) Foo` and `onto` is `Bar`, would return `shared(x) given(y) Bar`.
    pub fn rebase_perms(&self, onto: impl Upcast<Ty>) -> Ty {
        match self {
            Ty::ClassTy(_) | Ty::Var(_) => onto.upcast(),
            Ty::ApplyPerm(perm, ty) => Ty::apply_perm(perm, ty.rebase_perms(onto)),
        }
    }
}

#[term]
pub enum Perm {
    #[grammar(given $(?v0))]
    Given(Set<Place>),

    #[grammar(shared $(?v0))]
    Shared(Set<Place>),

    #[grammar(leased $(v0))]
    Leased(Set<Place>),

    #[variable(Kind::Perm)]
    Var(Variable),
}
mod perm_impls;

#[term($name $[?parameters])]
#[customize(parse, debug)]
pub struct ClassTy {
    pub name: ClassName,
    pub parameters: Parameters,
}
mod classty_impls;

#[term]
pub enum ClassName {
    Tuple(usize),

    #[grammar(Int)]
    Int,

    #[cast]
    Id(ValueId),
}

pub type Parameters = Vec<Parameter>;

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
formality_core::id!(ValueId);
formality_core::id!(FieldId);

#[term]
pub enum Predicate {
    Shared(Parameter),
    Leased(Parameter),
    Owned(Parameter),
}
