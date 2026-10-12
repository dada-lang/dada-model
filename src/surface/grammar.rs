//! Surface AST. Concrete permissions and identifier/binding infrastructure are
//! shared with core; types, declarations, and expressions are distinct terms.

pub use crate::core::grammar::{
    Access, Atomic, BinaryOp, ClassPredicate, FieldId, Kind, MethodId, ParameterPredicate, Perm,
    Place, PlaceExpr, TypeName, ValueId, VarianceKind,
};
pub use crate::dada_lang::grammar::*;
use formality_core::{term, Set, Upcast};
use std::sync::Arc;

mod cast_impls;
mod method_impls;
mod named_ty_impls;
mod parameter_impls;
mod receiver_impls;

#[term($*decls)]
pub struct Program {
    pub decls: Vec<Decl>,
}

#[term]
pub enum Decl {
    #[cast]
    ClassDecl(ClassDecl),
}

#[term($class_predicate $name $binder)]
pub struct ClassDecl {
    pub name: ValueId,
    pub class_predicate: ClassPredicate,
    pub binder: Binder<ClassDeclBoundData>,
}

#[term($:where $,predicates { $*fields $*methods $?drop_body })]
pub struct ClassDeclBoundData {
    pub predicates: Vec<Predicate>,
    pub fields: Vec<FieldDecl>,
    pub methods: Vec<MethodDecl>,
    pub drop_body: DropBody,
}
/// Optional drop body for a class. When present, the statements are executed
/// when an owned handle to the class is dropped. Default is an empty block
/// (no drop body), which is semantically equivalent to `drop { }`.
#[term(drop $block)]
#[derive(Default)]
pub struct DropBody {
    pub block: Block,
}

#[term($?atomic $name : $ty ;)]
pub struct FieldDecl {
    pub atomic: Atomic,
    pub name: FieldId,
    pub ty: Ty,
}

#[term(fn $name $binder)]
pub struct MethodDecl {
    pub name: MethodId,
    pub binder: Binder<MethodDeclBoundData>,
}

// FIXME: need to guard `$inputs` by a comma and output by `->`, using customized parse
#[term(($this $,inputs) -> $output $:where $,predicates $body)]
#[customize(parse)]
pub struct MethodDeclBoundData {
    pub this: ThisDecl,
    pub inputs: Vec<LocalVariableDecl>,
    pub output: Ty,
    pub predicates: Vec<Predicate>,
    pub body: MethodBody,
}
#[term]
pub enum MethodBody {
    #[grammar( ...;)]
    Trusted,

    #[cast]
    Block(Block),
}

#[term($perm self)]
#[customize(parse, debug)]
pub struct ThisDecl {
    pub perm: ReceiverPermission,
}

/// Permission shorthand is restricted to the outermost parameter/receiver.
#[term]
#[customize(parse)]
pub enum ReceiverPermission {
    #[cast]
    Explicit(Perm),

    #[grammar(any)]
    Any,

    #[grammar(!)]
    Mutable,
}

#[term]
#[customize(parse)]
pub enum ParameterTy {
    #[cast]
    Explicit(Ty),

    #[grammar(any $v0)]
    Any(Ty),

    #[grammar(! $v0)]
    Mutable(Ty),
}

#[term($name : $ty)]
pub struct LocalVariableDecl {
    pub name: ValueId,
    pub ty: ParameterTy,
}

#[term({ $*statements })]
#[derive(Default)]
pub struct Block {
    pub statements: Vec<Statement>,
}

#[term]
pub enum Statement {
    #[grammar($v0 ;)]
    #[cast]
    Expr(Expr),

    #[grammar(let $v0 $?v1 = $v2 ;)]
    Let(ValueId, Ascription, Arc<Expr>),
    #[grammar($v0 = $v1 ;)]
    Reassign(Place, Expr),

    #[grammar(drop $v0 ;)]
    Drop(Place),

    #[grammar(loop $v0)]
    Loop(Block),

    #[grammar(break ;)]
    Break,

    #[grammar(return $v0 ;)]
    Return(Expr),

    #[grammar(print ( $v0 ) ;)]
    Print(Expr),
}

#[term]
#[derive(Default)]
pub enum Ascription {
    #[default]
    NoTy,

    #[grammar(: $v0)]
    #[cast]
    Ty(Ty),
}

#[term]
pub enum Expr {
    #[cast]
    Block(Block),

    #[grammar($v0)]
    Integer(usize),
    #[grammar(true)]
    True,

    #[grammar(false)]
    False,

    #[grammar($v0 $v1 $v2)]
    #[precedence(0)]
    BinaryOp(Arc<Expr>, BinaryOp, Arc<Expr>),

    #[cast]
    Place(PlaceExpr),

    #[grammar($v0.share)]
    ShareValue(Arc<Expr>),

    #[grammar(($*v0))]
    Tuple(Vec<Expr>),

    #[grammar($v0 . $v1 $[?v2] $(v3))]
    Call(Arc<Expr>, MethodId, Vec<Parameter>, Vec<Expr>),

    #[grammar(new $v0 $[?v1] $(v2))]
    New(ValueId, Vec<Parameter>, Vec<Expr>),
    #[grammar($$clear($v0))]
    Clear(ValueId),

    #[grammar(if $v0 $v1 else $v2)]
    If(Arc<Expr>, Arc<Expr>, Arc<Expr>),

    #[grammar(size_of $[v0] ( ))]
    SizeOf(Vec<Parameter>),

    #[grammar(array_new $[v0] ( $v1 ))]
    ArrayNew(Vec<Parameter>, Arc<Expr>),

    #[grammar(array_capacity $[v0] ( $v1 ))]
    ArrayCapacity(Vec<Parameter>, Arc<Expr>),

    #[grammar(array_give $[v0] ( $v1 , $v2 ))]
    ArrayGive(Vec<Parameter>, Arc<Expr>, Arc<Expr>),

    #[grammar(array_drop $[v0] ( $v1 , $v2 , $v3 ))]
    ArrayDrop(Vec<Parameter>, Arc<Expr>, Arc<Expr>, Arc<Expr>),

    #[grammar(array_write $[v0] ( $v1 , $v2 , $v3 ))]
    ArrayWrite(Vec<Parameter>, Arc<Expr>, Arc<Expr>, Arc<Expr>),

    #[grammar(is_last_ref $[v0] ( $v1 ))]
    IsLastRef(Vec<Parameter>, Arc<Expr>),

    /// `!` panics the progarm, but it's main purpose is to simplify writing tests by allowing us
    /// to produce a value of any type. `!` can only be used in places where we have an expected type from context.
    #[grammar(!)]
    Panic,
}

#[term]
pub enum Parameter {
    #[cast]
    Ty(Ty),

    #[cast]
    Perm(Perm),
}

#[term]
pub enum Ty {
    #[cast]
    NamedTy(NamedTy),

    #[variable(Kind::Ty)]
    Var(Variable),

    #[grammar($v0 $v1)]
    ApplyPerm(Perm, Arc<Ty>),

    /// Surface shorthand for `given[origins] T`, including `[] T`.
    #[grammar($[v0] $v1)]
    GivenFrom(Set<Place>, Arc<Ty>),
}

impl Ty {
    pub fn unit() -> Self {
        NamedTy {
            name: TypeName::Tuple(0),
            parameters: vec![],
        }
        .upcast()
    }
}

#[term($name $[?parameters])]
#[customize(parse, debug)]
pub struct NamedTy {
    pub name: TypeName,
    pub parameters: Parameters,
}
pub type Parameters = Vec<Parameter>;

#[term]
pub enum Predicate {
    #[grammar($v1 is $v0)]
    Parameter(ParameterPredicate, Parameter),

    #[grammar($v1 is $v0)]
    Variance(VarianceKind, Parameter),
}
