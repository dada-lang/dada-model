pub use crate::dada_lang::grammar::*;
use crate::dada_lang::FormalityLang;
use formality_core::{term, Downcast, Fallible, Set, Upcast, UpcastFrom};
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
}

#[term]
pub enum Decl {
    #[cast]
    ClassDecl(ClassDecl),
}

// ANCHOR: ClassDecl
#[term(class $name $binder)]
pub struct ClassDecl {
    pub name: ValueId,
    pub binder: Binder<ClassDeclBoundData>,
}

#[term($:where $,predicates { $*fields $*methods })]
pub struct ClassDeclBoundData {
    pub predicates: Vec<Predicate>,
    pub fields: Vec<FieldDecl>,
    pub methods: Vec<MethodDecl>,
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
    pub body: Block,
}
mod method_impls;

#[term($perm self)]
pub struct ThisDecl {
    pub perm: Perm,
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

    #[grammar(let $v0 $?v1 = $v2 ;)]
    Let(ValueId, Ascription, Arc<Expr>),

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

    #[grammar($v0 + $v1)]
    #[precedence(0)]
    Add(Arc<Expr>, Arc<Expr>),

    #[cast]
    Place(PlaceExpr),

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

    /// `!` panics the progarm, but it's main purpose is to simplify writing tests by allowing us
    /// to produce a value of any type. `!` can only be used in places where we have an expected type from context.
    #[grammar(!)]
    Panic,
}

#[term]
#[derive(Copy, Default)]
pub enum Access {
    #[default]
    Share,

    Give,

    Lease,

    Drop,
}

impl Access {
    pub fn give_to_drop(self) -> Self {
        match self {
            Access::Share | Access::Lease => self,
            Access::Give | Access::Drop => Access::Drop,
        }
    }
}

#[term($place . $access)]
pub struct PlaceExpr {
    pub place: Place,
    pub access: Access,
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

impl Parameter {
    pub fn is_var(&self, v: impl Upcast<Variable>) -> bool {
        let Some(u) = self.downcast::<Variable>() else {
            return false;
        };

        let v: Variable = v.upcast();
        v == u
    }
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
    NamedTy(NamedTy),

    #[variable(Kind::Ty)]
    Var(Variable),

    #[grammar($v0 $v1)]
    ApplyPerm(Perm, Arc<Ty>),

    #[grammar($v0 | $v1)]
    Or(Arc<Ty>, Arc<Ty>),
}

impl Ty {
    pub fn unit() -> Ty {
        NamedTy {
            name: TypeName::Tuple(0),
            parameters: vec![],
        }
        .upcast()
    }

    pub fn int() -> Ty {
        NamedTy {
            name: TypeName::Int,
            parameters: vec![],
        }
        .upcast()
    }

    pub fn tuple(parameters: impl Upcast<Vec<Ty>>) -> Ty {
        let parameters: Vec<Ty> = parameters.upcast();
        NamedTy {
            name: TypeName::Tuple(parameters.len()),
            parameters: parameters.upcast(),
        }
        .upcast()
    }

    pub fn strip_perm(&self) -> Ty {
        match self {
            Ty::NamedTy(_) | Ty::Var(_) => self.clone(),
            Ty::ApplyPerm(_, ty) => ty.strip_perm(),
            Ty::Or(ty1, ty2) => Ty::or(ty1.strip_perm(), ty2.strip_perm()),
        }
    }
}

#[term]
pub enum Perm {
    #[grammar(my)]
    My,

    #[grammar(our)]
    Our,

    #[grammar(given $[?v0])]
    Given(Set<Place>),

    #[grammar(shared $[?v0])]
    Shared(Set<Place>),

    #[grammar(leased $[v0])]
    Leased(Set<Place>),

    #[variable(Kind::Perm)]
    Var(Variable),

    #[grammar($v0 $v1)]
    Apply(Arc<Perm>, Arc<Perm>),

    #[grammar($v0 | $v1)]
    Or(Arc<Perm>, Arc<Perm>),
}
mod perm_impls;

#[term($name $[?parameters])]
#[customize(parse, debug)]
pub struct NamedTy {
    pub name: TypeName,
    pub parameters: Parameters,
}
mod named_ty_impls;

#[term]
pub enum TypeName {
    Tuple(usize),

    #[grammar(Int)]
    Int,

    #[cast]
    Id(ValueId),
}

pub type Parameters = Vec<Parameter>;

#[term($var $*projections)]
pub struct Place {
    pub var: Var,
    pub projections: Vec<Projection>,
}

impl Place {
    /// True if `self` is a prefix of `place`.
    pub fn is_overlapping_with(&self, place: &Place) -> bool {
        self.is_prefix_of(place) || place.is_prefix_of(self)
    }

    /// True if `self` is disjoint from `place`.
    pub fn is_disjoint_from(&self, place: &Place) -> bool {
        !self.is_overlapping_with(place)
    }

    /// True if self is a prefix of `place` (and not equal to it).
    pub fn is_strict_prefix_of(&self, place: &Place) -> bool {
        self != place && self.is_prefix_of(place)
    }

    /// True if self is a prefix of `place` (or equal to it).
    pub fn is_prefix_of(&self, place: &Place) -> bool {
        self.var == place.var
            && self.projections.len() <= place.projections.len()
            && self
                .projections
                .iter()
                .zip(&place.projections)
                .all(|(p1, p2)| p1 == p2)
    }

    pub fn project(&self, projection: impl Upcast<Projection>) -> Place {
        let projection = projection.upcast();
        Place {
            var: self.var.clone(),
            projections: self
                .projections
                .iter()
                .chain(std::iter::once(&projection))
                .cloned()
                .collect(),
        }
    }

    /// Returns all "strict prefixes" of this place -- so for `foo.bar.baz`,
    /// returns `[foo, foo.bar]` (but not `foo.bar.baz`).
    pub fn strict_prefixes(&self) -> Vec<Place> {
        (0..self.projections.len())
            .map(|i| Place {
                var: self.var.clone(),
                projections: self.projections[..i].to_vec(),
            })
            .collect()
    }

    /// Returns this place but without one layer of projection (e.g., given `a.b.c` returns `a.b`).
    /// If the place has just a variable (e.g., `a`), returns `None`.
    pub fn owner(&self) -> Option<Place> {
        if let Some((_, p)) = self.projections.split_last() {
            Some(Place {
                var: self.var.clone(),
                projections: p.to_vec(),
            })
        } else {
            None
        }
    }
}

impl UpcastFrom<Var> for Place {
    fn upcast_from(var: Var) -> Self {
        Place {
            var,
            projections: vec![],
        }
    }
}

#[term]
pub enum Projection {
    #[grammar(. $v0 $!)]
    Field(FieldId),
}

#[term]
pub enum Var {
    #[grammar(self)]
    This,

    /// Special variable (nameable by user) representing
    /// the return value of a function.
    #[grammar(return)]
    Return,

    /// A special variable used only in the type-system.
    /// Represents a value that is in the process of being moved.
    #[grammar(@ in_flight)]
    InFlight,

    /// Fresh values introduced during type check
    #[grammar(@ fresh($v0))]
    Fresh(usize),

    #[cast]
    Id(ValueId),
}

impl Var {
    pub fn dot(&self, f: impl Upcast<FieldId>) -> Place {
        Place {
            var: self.clone(),
            projections: vec![Projection::field(f)],
        }
    }
}

formality_core::id!(BasicBlockId);
formality_core::id!(ValueId);
formality_core::id!(FieldId);
formality_core::id!(MethodId);

#[term]
pub enum Predicate {
    /// A parameter `a` is **copy** when a value of this type, or of a type
    /// with this permission, is non-affine and hence is copied upon being
    /// given rather than moved.
    ///
    /// Note that "copy" does not respect Liskov Substitution Principle:
    /// `my` is not `copy` but is a subtype of `our` which *is* copy.
    Copy(Parameter),

    /// A parameter `a` is **leased** when it is a `leased` permission or
    /// a type with a `leased` permission, and hence represents indirect,
    /// mutable access to data owned by someone else.
    Leased(Parameter),

    #[grammar($v0($v1))]
    Variance(VarianceKind, Parameter),
}

#[term]
#[derive(Copy)]
pub enum VarianceKind {
    /// `relative(p)` is used to express variance.
    /// Whenever a type `P T` appears in a struct
    /// and `P != my`, `Relative(T)` must hold.
    /// This indicates that `T`
    /// appears in a position that is relative to some
    /// permission.
    Relative,

    /// `atomic(p)` is used to express variance.
    /// It has to hold for all types appearing
    /// an atomic field.
    Atomic,
}

impl VarianceKind {
    pub fn apply(self, parameter: impl Upcast<Parameter>) -> Predicate {
        Predicate::variance(self, parameter)
    }
}
