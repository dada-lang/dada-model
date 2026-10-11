//! Structural surface-to-core judgments. Parameter sugar appends fresh permission
//! binders while preserving explicit generic order and call arguments.

use std::sync::Arc;

use formality_core::{fold::CoreFold, judgment_fn, Fallible};

use super::grammar as surface;
use crate::core::grammar as core;
use crate::dada_lang::FormalityLang;

/// Lower one parsed program. Parsing stays separate so callers can distinguish
/// syntax/lowering failures from checker failures and runtime faults.
pub fn program(program: &surface::Program) -> Fallible<core::Program> {
    lower(program)
}

trait Lower {
    type Output;
    fn lower(&self) -> Fallible<Self::Output>;
}

fn lower<T: Lower>(term: &T) -> Fallible<T::Output> {
    term.lower()
}

impl<T: Lower> Lower for Vec<T> {
    type Output = Vec<T::Output>;
    fn lower(&self) -> Fallible<Self::Output> {
        self.iter().map(lower).collect()
    }
}

impl<T: Lower> Lower for Arc<T> {
    type Output = Arc<T::Output>;
    fn lower(&self) -> Fallible<Self::Output> {
        Ok(Arc::new(lower(&**self)?))
    }
}

impl<T> Lower for surface::Binder<T>
where
    T: Lower + CoreFold<FormalityLang>,
    T::Output: CoreFold<FormalityLang>,
{
    type Output = core::Binder<T::Output>;
    fn lower(&self) -> Fallible<Self::Output> {
        let (variables, body) = self.open();
        Ok(core::Binder::new(variables, lower(&body)?))
    }
}

impl Lower for surface::Program {
    type Output = core::Program;
    fn lower(&self) -> Fallible<Self::Output> {
        Ok(lower_program(self.clone()).into_singleton()?.0)
    }
}

judgment_fn! {
    pub fn lower_program(term: surface::Program) => core::Program {
        debug(term)

        (
            (let result = Ok::<_, anyhow::Error>(core::Program { decls: lower(decls)? })?)
            ------------------------------- ("lower_program")
            (lower_program(surface::Program { decls }) => result)
        )
    }
}

impl Lower for surface::ClassDecl {
    type Output = core::ClassDecl;
    fn lower(&self) -> Fallible<Self::Output> {
        Ok(lower_class(self.clone()).into_singleton()?.0)
    }
}

judgment_fn! {
    pub fn lower_class(term: surface::ClassDecl) => core::ClassDecl {
        debug(term)

        (
            (let result = Ok::<_, anyhow::Error>(core::ClassDecl { name: name.clone(), class_predicate: class_predicate.clone(), binder: lower(binder)? })?)
            ------------------------------- ("lower_class")
            (lower_class(surface::ClassDecl { name, class_predicate, binder }) => result)
        )
    }
}

impl Lower for surface::ClassDeclBoundData {
    type Output = core::ClassDeclBoundData;
    fn lower(&self) -> Fallible<Self::Output> {
        Ok(lower_class_body(self.clone()).into_singleton()?.0)
    }
}

judgment_fn! {
    pub fn lower_class_body(term: surface::ClassDeclBoundData) => core::ClassDeclBoundData {
        debug(term)

        (
            (let result = Ok::<_, anyhow::Error>(core::ClassDeclBoundData { predicates: lower(predicates)?, fields: lower(fields)?, methods: lower(methods)?, drop_body: lower(drop_body)? })?)
            ------------------------------- ("lower_class_body")
            (lower_class_body(surface::ClassDeclBoundData { predicates, fields, methods, drop_body }) => result)
        )
    }
}

impl Lower for surface::DropBody {
    type Output = core::DropBody;
    fn lower(&self) -> Fallible<Self::Output> {
        Ok(lower_drop_body(self.clone()).into_singleton()?.0)
    }
}

judgment_fn! {
    pub fn lower_drop_body(term: surface::DropBody) => core::DropBody {
        debug(term)

        (
            (let result = Ok::<_, anyhow::Error>(core::DropBody { block: lower(block)? })?)
            ------------------------------- ("lower_drop_body")
            (lower_drop_body(surface::DropBody { block }) => result)
        )
    }
}

impl Lower for surface::FieldDecl {
    type Output = core::FieldDecl;
    fn lower(&self) -> Fallible<Self::Output> {
        Ok(lower_field(self.clone()).into_singleton()?.0)
    }
}

judgment_fn! {
    pub fn lower_field(term: surface::FieldDecl) => core::FieldDecl {
        debug(term)

        (
            (let result = Ok::<_, anyhow::Error>(core::FieldDecl { atomic: atomic.clone(), name: name.clone(), ty: lower(ty)? })?)
            ------------------------------- ("lower_field")
            (lower_field(surface::FieldDecl { atomic, name, ty }) => result)
        )
    }
}

impl Lower for surface::MethodDecl {
    type Output = core::MethodDecl;
    fn lower(&self) -> Fallible<Self::Output> {
        Ok(lower_method(self.clone()).into_singleton()?.0)
    }
}

judgment_fn! {
    pub fn lower_method(term: surface::MethodDecl) => core::MethodDecl {
        debug(term)

        (
            (let (explicit, data) = source_binder.open())
            (lower_method_body(data) => (data, generated))
            (let all_variables: Vec<core::BoundVar> = explicit.iter().chain(generated).copied().collect())
            (let binder = core::Binder::new(all_variables, data.clone()))
            ----------------------------------- ("lower_method")
            (lower_method(surface::MethodDecl { name, binder: source_binder }) => core::MethodDecl {
                name: name.clone(), binder: binder.clone()
            })
        )
    }
}

// Binder construction and collection are bookkeeping; the judgments below
// decide which syntax introduces a variable and which constraint it requires.
fn collect_method(
    this: &surface::ThisDecl,
    inputs: &[surface::LocalVariableDecl],
    output: &surface::Ty,
    explicit_predicates: &[surface::Predicate],
    body: &surface::MethodBody,
) -> Fallible<(core::MethodDeclBoundData, Vec<core::BoundVar>)> {
    let ((perm, mut generated, mut generated_predicates), _) =
        lower_receiver(this.perm.clone()).into_singleton()?;
    let mut core_inputs = vec![];
    for input in inputs {
        let ((ty, variables, predicates), _) =
            lower_parameter_type(input.ty.clone()).into_singleton()?;
        core_inputs.push(core::LocalVariableDecl {
            name: input.name.clone(),
            ty,
        });
        generated.extend(variables);
        generated_predicates.extend(predicates);
    }
    let mut predicates = explicit_predicates
        .iter()
        .map(lower)
        .collect::<Fallible<Vec<_>>>()?;
    predicates.extend(generated_predicates);
    Ok((
        core::MethodDeclBoundData {
            this: core::ThisDecl { perm },
            inputs: core_inputs,
            output: lower(output)?,
            predicates,
            body: lower(body)?,
        },
        generated,
    ))
}

judgment_fn! {
    pub fn lower_method_body(term: surface::MethodDeclBoundData)
        => (core::MethodDeclBoundData, Vec<core::BoundVar>) {
        debug(term)

        (
            (let (data, generated) = collect_method(this, inputs, output, predicates, body)?)
            ----------------------------------- ("lower_method_body")
            (lower_method_body(surface::MethodDeclBoundData {
                this, inputs, output, predicates, body
            }) => (data, generated))
        )
    }
}

judgment_fn! {
    pub fn lower_receiver(permission: surface::ReceiverPermission)
        => (core::Perm, Vec<core::BoundVar>, Vec<core::Predicate>) {
        debug(permission)

        (
            ----------------------------------- ("explicit")
            (lower_receiver(surface::ReceiverPermission::Explicit(permission)) =>
                (permission, Vec::<core::BoundVar>::new(), Vec::<core::Predicate>::new()))
        )

        (
            (let variable = core::BoundVar::fresh(core::Kind::Perm))
            ----------------------------------- ("any")
            (lower_receiver(surface::ReceiverPermission::Any) =>
                (core::Perm::var(variable), vec![variable], Vec::<core::Predicate>::new()))
        )

        (
            (let variable = core::BoundVar::fresh(core::Kind::Perm))
            ----------------------------------- ("mutable")
            (lower_receiver(surface::ReceiverPermission::Mutable) =>
                (core::Perm::var(variable), vec![variable], vec![core::Predicate::mut_(variable)]))
        )
    }
}

judgment_fn! {
    pub fn lower_parameter_type(ty: surface::ParameterTy)
        => (core::Ty, Vec<core::BoundVar>, Vec<core::Predicate>) {
        debug(ty)

        (
            (if !matches!(ty, surface::Ty::NamedTy(_) | surface::Ty::Var(_)))
            (lower_type(ty) => ty)
            ----------------------------------- ("explicit")
            (lower_parameter_type(surface::ParameterTy::Explicit(ty)) => (ty, Vec::<core::BoundVar>::new(), Vec::<core::Predicate>::new()))
        )

        (
            (if matches!(ty, surface::Ty::NamedTy(_) | surface::Ty::Var(_)))
            (lower_parameter_type(surface::ParameterTy::Any(ty.clone())) => result)
            ----------------------------------- ("omitted_permission")
            (lower_parameter_type(surface::ParameterTy::Explicit(ty)) => result)
        )

        (
            (lower_type(ty) => ty)
            (let variable = core::BoundVar::fresh(core::Kind::Perm))
            ----------------------------------- ("any")
            (lower_parameter_type(surface::ParameterTy::Any(ty)) =>
                (apply_permission(core::Perm::var(variable), ty.clone()), vec![variable], Vec::<core::Predicate>::new()))
        )

        (
            (lower_type(ty) => ty)
            (let variable = core::BoundVar::fresh(core::Kind::Perm))
            ----------------------------------- ("mutable")
            (lower_parameter_type(surface::ParameterTy::Mutable(ty)) =>
                (apply_permission(core::Perm::var(variable), ty.clone()), vec![variable],
                    vec![core::Predicate::mut_(variable)]))
        )
    }
}

impl Lower for surface::Block {
    type Output = core::Block;
    fn lower(&self) -> Fallible<Self::Output> {
        Ok(lower_block(self.clone()).into_singleton()?.0)
    }
}

judgment_fn! {
    pub fn lower_block(term: surface::Block) => core::Block {
        debug(term)

        (
            (let result = Ok::<_, anyhow::Error>(core::Block { statements: lower(statements)? })?)
            ------------------------------- ("lower_block")
            (lower_block(surface::Block { statements }) => result)
        )
    }
}

impl Lower for surface::NamedTy {
    type Output = core::NamedTy;
    fn lower(&self) -> Fallible<Self::Output> {
        Ok(lower_named_type(self.clone()).into_singleton()?.0)
    }
}

judgment_fn! {
    pub fn lower_named_type(term: surface::NamedTy) => core::NamedTy {
        debug(term)

        (
            (let result = Ok::<_, anyhow::Error>(core::NamedTy { name: name.clone(), parameters: lower(parameters)? })?)
            ------------------------------- ("lower_named_type")
            (lower_named_type(surface::NamedTy { name, parameters }) => result)
        )
    }
}

impl Lower for surface::Decl {
    type Output = core::Decl;
    fn lower(&self) -> Fallible<Self::Output> {
        Ok(lower_decl(self.clone()).into_singleton()?.0)
    }
}

judgment_fn! {
    pub fn lower_decl(term: surface::Decl) => core::Decl {
        debug(term)

        (
            (let result = Ok::<_, anyhow::Error>(core::Decl::ClassDecl(lower(v0)?))?)
            ------------------------------- ("ClassDecl")
            (lower_decl(surface::Decl::ClassDecl(v0)) => result)
        )

    }
}

impl Lower for surface::MethodBody {
    type Output = core::MethodBody;
    fn lower(&self) -> Fallible<Self::Output> {
        Ok(lower_method_contents(self.clone()).into_singleton()?.0)
    }
}

judgment_fn! {
    pub fn lower_method_contents(term: surface::MethodBody) => core::MethodBody {
        debug(term)

        (
            (let result = Ok::<_, anyhow::Error>(core::MethodBody::Trusted)?)
            ------------------------------- ("Trusted")
            (lower_method_contents(surface::MethodBody::Trusted) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::MethodBody::Block(lower(v0)?))?)
            ------------------------------- ("Block")
            (lower_method_contents(surface::MethodBody::Block(v0)) => result)
        )

    }
}

impl Lower for surface::Statement {
    type Output = core::Statement;
    fn lower(&self) -> Fallible<Self::Output> {
        Ok(lower_statement(self.clone()).into_singleton()?.0)
    }
}

judgment_fn! {
    pub fn lower_statement(term: surface::Statement) => core::Statement {
        debug(term)

        (
            (let result = Ok::<_, anyhow::Error>(core::Statement::Expr(lower(v0)?))?)
            ------------------------------- ("Expr")
            (lower_statement(surface::Statement::Expr(v0)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Statement::Let(v0.clone(), lower(v1)?, lower(v2)?))?)
            ------------------------------- ("Let")
            (lower_statement(surface::Statement::Let(v0, v1, v2)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Statement::Reassign(v0.clone(), lower(v1)?))?)
            ------------------------------- ("Reassign")
            (lower_statement(surface::Statement::Reassign(v0, v1)) => result)
        )

        (
            ------------------------------- ("Drop")
            (lower_statement(surface::Statement::Drop(place)) => core::Statement::Drop(place.clone()))
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Statement::Loop(lower(v0)?))?)
            ------------------------------- ("Loop")
            (lower_statement(surface::Statement::Loop(v0)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Statement::Break)?)
            ------------------------------- ("Break")
            (lower_statement(surface::Statement::Break) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Statement::Return(lower(v0)?))?)
            ------------------------------- ("Return")
            (lower_statement(surface::Statement::Return(v0)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Statement::Print(lower(v0)?))?)
            ------------------------------- ("Print")
            (lower_statement(surface::Statement::Print(v0)) => result)
        )

    }
}

impl Lower for surface::Ascription {
    type Output = core::Ascription;
    fn lower(&self) -> Fallible<Self::Output> {
        Ok(lower_ascription(self.clone()).into_singleton()?.0)
    }
}

judgment_fn! {
    pub fn lower_ascription(term: surface::Ascription) => core::Ascription {
        debug(term)

        (
            (let result = Ok::<_, anyhow::Error>(core::Ascription::NoTy)?)
            ------------------------------- ("NoTy")
            (lower_ascription(surface::Ascription::NoTy) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Ascription::Ty(lower(v0)?))?)
            ------------------------------- ("Ty")
            (lower_ascription(surface::Ascription::Ty(v0)) => result)
        )

    }
}

impl Lower for surface::Expr {
    type Output = core::Expr;
    fn lower(&self) -> Fallible<Self::Output> {
        Ok(lower_expr(self.clone()).into_singleton()?.0)
    }
}

judgment_fn! {
    pub fn lower_expr(term: surface::Expr) => core::Expr {
        debug(term)

        (
            (let result = Ok::<_, anyhow::Error>(core::Expr::Block(lower(v0)?))?)
            ------------------------------- ("Block")
            (lower_expr(surface::Expr::Block(v0)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Expr::Integer(v0.clone()))?)
            ------------------------------- ("Integer")
            (lower_expr(surface::Expr::Integer(v0)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Expr::True)?)
            ------------------------------- ("True")
            (lower_expr(surface::Expr::True) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Expr::False)?)
            ------------------------------- ("False")
            (lower_expr(surface::Expr::False) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Expr::BinaryOp(lower(v0)?, v1.clone(), lower(v2)?))?)
            ------------------------------- ("BinaryOp")
            (lower_expr(surface::Expr::BinaryOp(v0, v1, v2)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Expr::Place(v0.clone()))?)
            ------------------------------- ("Place")
            (lower_expr(surface::Expr::Place(v0)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Expr::ShareValue(lower(v0)?))?)
            ------------------------------- ("Share")
            (lower_expr(surface::Expr::ShareValue(v0)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Expr::Tuple(lower(v0)?))?)
            ------------------------------- ("Tuple")
            (lower_expr(surface::Expr::Tuple(v0)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Expr::Call(lower(v0)?, v1.clone(), lower(v2)?, lower(v3)?))?)
            ------------------------------- ("Call")
            (lower_expr(surface::Expr::Call(v0, v1, v2, v3)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Expr::New(v0.clone(), lower(v1)?, lower(v2)?))?)
            ------------------------------- ("New")
            (lower_expr(surface::Expr::New(v0, v1, v2)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Expr::Clear(v0.clone()))?)
            ------------------------------- ("Clear")
            (lower_expr(surface::Expr::Clear(v0)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Expr::If(lower(v0)?, lower(v1)?, lower(v2)?))?)
            ------------------------------- ("If")
            (lower_expr(surface::Expr::If(v0, v1, v2)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Expr::SizeOf(lower(v0)?))?)
            ------------------------------- ("SizeOf")
            (lower_expr(surface::Expr::SizeOf(v0)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Expr::ArrayNew(lower(v0)?, lower(v1)?))?)
            ------------------------------- ("ArrayNew")
            (lower_expr(surface::Expr::ArrayNew(v0, v1)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Expr::ArrayCapacity(lower(v0)?, lower(v1)?))?)
            ------------------------------- ("ArrayCapacity")
            (lower_expr(surface::Expr::ArrayCapacity(v0, v1)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Expr::ArrayGive(lower(v0)?, lower(v1)?, lower(v2)?))?)
            ------------------------------- ("ArrayGive")
            (lower_expr(surface::Expr::ArrayGive(v0, v1, v2)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Expr::ArrayDrop(lower(v0)?, lower(v1)?, lower(v2)?, lower(v3)?))?)
            ------------------------------- ("ArrayDrop")
            (lower_expr(surface::Expr::ArrayDrop(v0, v1, v2, v3)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Expr::ArrayWrite(lower(v0)?, lower(v1)?, lower(v2)?, lower(v3)?))?)
            ------------------------------- ("ArrayWrite")
            (lower_expr(surface::Expr::ArrayWrite(v0, v1, v2, v3)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Expr::IsLastRef(lower(v0)?, lower(v1)?))?)
            ------------------------------- ("IsLastRef")
            (lower_expr(surface::Expr::IsLastRef(v0, v1)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Expr::Panic)?)
            ------------------------------- ("Panic")
            (lower_expr(surface::Expr::Panic) => result)
        )

    }
}

impl Lower for surface::Parameter {
    type Output = core::Parameter;
    fn lower(&self) -> Fallible<Self::Output> {
        Ok(lower_parameter(self.clone()).into_singleton()?.0)
    }
}

judgment_fn! {
    pub fn lower_parameter(term: surface::Parameter) => core::Parameter {
        debug(term)

        (
            (let result = Ok::<_, anyhow::Error>(core::Parameter::Ty(lower(v0)?))?)
            ------------------------------- ("Ty")
            (lower_parameter(surface::Parameter::Ty(v0)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Parameter::Perm(v0.clone()))?)
            ------------------------------- ("Perm")
            (lower_parameter(surface::Parameter::Perm(v0)) => result)
        )

    }
}

impl Lower for surface::Ty {
    type Output = core::Ty;
    fn lower(&self) -> Fallible<Self::Output> {
        Ok(lower_type(self.clone()).into_singleton()?.0)
    }
}

judgment_fn! {
    pub fn lower_type(term: surface::Ty) => core::Ty {
        debug(term)

        (
            (let result = Ok::<_, anyhow::Error>(core::Ty::NamedTy(lower(v0)?))?)
            ------------------------------- ("NamedTy")
            (lower_type(surface::Ty::NamedTy(v0)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Ty::Var(v0.clone()))?)
            ------------------------------- ("Var")
            (lower_type(surface::Ty::Var(v0)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(apply_permission(v0.clone(), lower(&**v1)?))?)
            ------------------------------- ("ApplyPerm")
            (lower_type(surface::Ty::ApplyPerm(v0, v1)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(apply_permission(core::Perm::share_from(origins), lower(&**ty)?))?)
            ------------------------------- ("shared origins shorthand")
            (lower_type(surface::Ty::ShareFrom(origins, ty)) => result)
        )

    }
}

/// Match the core grammar's permission grouping when a surface shorthand
/// interrupts an otherwise contiguous permission prefix.
pub(crate) fn apply_permission(permission: core::Perm, ty: core::Ty) -> core::Ty {
    match ty {
        core::Ty::ApplyPerm(inner, ty) => {
            apply_permission(concat_permissions(permission, inner), (*ty).clone())
        }
        ty => core::Ty::ApplyPerm(permission, Arc::new(ty)),
    }
}

fn concat_permissions(outer: core::Perm, inner: core::Perm) -> core::Perm {
    match outer {
        core::Perm::Apply(first, rest) => {
            core::Perm::apply(first, concat_permissions((*rest).clone(), inner))
        }
        outer => core::Perm::apply(outer, inner),
    }
}

impl Lower for surface::Predicate {
    type Output = core::Predicate;
    fn lower(&self) -> Fallible<Self::Output> {
        Ok(lower_predicate(self.clone()).into_singleton()?.0)
    }
}

judgment_fn! {
    pub fn lower_predicate(term: surface::Predicate) => core::Predicate {
        debug(term)

        (
            (let result = Ok::<_, anyhow::Error>(core::Predicate::Parameter(v0.clone(), lower(v1)?))?)
            ------------------------------- ("Parameter")
            (lower_predicate(surface::Predicate::Parameter(v0, v1)) => result)
        )

        (
            (let result = Ok::<_, anyhow::Error>(core::Predicate::Variance(v0.clone(), lower(v1)?))?)
            ------------------------------- ("Variance")
            (lower_predicate(surface::Predicate::Variance(v0, v1)) => result)
        )

    }
}
