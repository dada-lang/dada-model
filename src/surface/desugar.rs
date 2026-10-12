//! Structural surface-to-core judgments. Parameter sugar appends fresh permission
//! binders while preserving explicit generic order and call arguments.

use formality_core::{judgment_fn, seq, Fallible, Upcast};

use super::grammar as surface;
use crate::core::grammar as core;

/// Lower one parsed program. Parsing stays separate so callers can distinguish
/// syntax/lowering failures from checker failures and runtime faults.
pub fn program(program: &surface::Program) -> Fallible<core::Program> {
    Ok(lower_program(program).into_singleton()?.0)
}

judgment_fn! {
    pub fn lower_program(term: surface::Program) => core::Program {
        debug(term)

        (
            (let core_decls: Vec<core::Decl> = vec![])
            (for_all(decl in decls) with(core_decls)
                (lower_decl(decl) => decl)
                (let core_decls: Vec<core::Decl> = seq![..&core_decls, decl].upcast()))
            ----------------------------------- ("lower_program")
            (lower_program(surface::Program { decls }) => core::Program::new(core_decls))
        )
    }
}

judgment_fn! {
    pub fn lower_class(term: surface::ClassDecl) => core::ClassDecl {
        debug(term)

        (
            (let (variables, body) = binder.open())
            (lower_class_body(body) => body)
            (let binder = core::Binder::new(variables, body.clone()))
            ----------------------------------- ("lower_class")
            (lower_class(surface::ClassDecl { name, class_predicate, binder }) =>
                core::ClassDecl::new(name, class_predicate, binder))
        )
    }
}

judgment_fn! {
    pub fn lower_class_body(term: surface::ClassDeclBoundData) => core::ClassDeclBoundData {
        debug(term)

        (
            (lower_predicates(predicates) => predicates)
            (let core_fields: Vec<core::FieldDecl> = vec![])
            (for_all(field in fields) with(core_fields)
                (lower_field(field) => field)
                (let core_fields: Vec<core::FieldDecl> = seq![..&core_fields, field].upcast()))
            (let core_methods: Vec<core::MethodDecl> = vec![])
            (for_all(method in methods) with(core_methods)
                (lower_method(method) => method)
                (let core_methods: Vec<core::MethodDecl> = seq![..&core_methods, method].upcast()))
            (lower_drop_body(drop_body) => drop_body)
            ----------------------------------- ("lower_class_body")
            (lower_class_body(surface::ClassDeclBoundData { predicates, fields, methods, drop_body }) =>
                core::ClassDeclBoundData::new(predicates, &core_fields, &core_methods, drop_body))
        )
    }
}

judgment_fn! {
    pub fn lower_drop_body(term: surface::DropBody) => core::DropBody {
        debug(term)

        (
            (lower_block(block) => block)
            ----------------------------------- ("lower_drop_body")
            (lower_drop_body(surface::DropBody { block }) => core::DropBody::new(block))
        )
    }
}

judgment_fn! {
    pub fn lower_field(term: surface::FieldDecl) => core::FieldDecl {
        debug(term)

        (
            (lower_type(ty) => ty)
            ----------------------------------- ("lower_field")
            (lower_field(surface::FieldDecl { atomic, name, ty }) => core::FieldDecl::new(atomic, name, ty))
        )
    }
}

judgment_fn! {
    pub fn lower_method(term: surface::MethodDecl) => core::MethodDecl {
        debug(term)

        (
            (let (explicit, data) = binder.open())
            (lower_method_body(data) => (data, generated))
            (let binder = core::Binder::new(seq![..explicit, ..generated], data.clone()))
            ----------------------------------- ("lower_method")
            (lower_method(surface::MethodDecl::Explicit(name, binder)) => core::MethodDecl::new(name, binder))
        )

        (
            (lower_receiver_sigil(sigil) => permission)
            (let (explicit, data) = binder.open())
            (let surface::ReceiverMethodDeclBoundData { inputs, output, predicates, body } = data)
            (lower_method_body(surface::MethodDeclBoundData::new(surface::ThisDecl::new(permission), inputs, output, predicates, body)) => (data, generated))
            (let binder = core::Binder::new(seq![..explicit, ..generated], data.clone()))
            ----------------------------------- ("receiver_method")
            (lower_method(surface::MethodDecl::Receiver(sigil, name, binder)) => core::MethodDecl::new(name, binder))
        )
    }
}

judgment_fn! {
    pub fn lower_receiver_sigil(sigil: surface::ReceiverSigil) => surface::ReceiverPermission {
        debug(sigil)

        (
            ----------------------------------- ("any")
            (lower_receiver_sigil(surface::ReceiverSigil::Any) => surface::ReceiverPermission::Any)
        )

        (
            ----------------------------------- ("mutable")
            (lower_receiver_sigil(surface::ReceiverSigil::Mutable) => surface::ReceiverPermission::Mutable)
        )

        (
            ----------------------------------- ("given")
            (lower_receiver_sigil(surface::ReceiverSigil::Given) => core::Perm::Given)
        )
    }
}

judgment_fn! {
    pub fn lower_method_body(term: surface::MethodDeclBoundData)
        => (core::MethodDeclBoundData, Vec<core::BoundVar>) {
        debug(term)

        (
            (lower_receiver(&this.perm) => (perm, receiver_variables, receiver_predicates))
            (let generated: Vec<core::BoundVar> = receiver_variables.upcast())
            (let generated_predicates: Vec<core::Predicate> = receiver_predicates.upcast())
            (let core_inputs: Vec<core::LocalVariableDecl> = vec![])
            (for_all(input in inputs) with(core_inputs, generated, generated_predicates)
                (let surface::LocalVariableDecl { name, ty } = input)
                (lower_parameter_type(ty) => (ty, variables, predicates))
                (let input = core::LocalVariableDecl::new(name, ty))
                (let core_inputs: Vec<core::LocalVariableDecl> = seq![..&core_inputs, input].upcast())
                (let generated: Vec<core::BoundVar> = seq![..&generated, ..variables].upcast())
                (let generated_predicates: Vec<core::Predicate> = seq![..&generated_predicates, ..predicates].upcast()))
            (lower_predicates(predicates) => predicates)
            (let predicates = seq![..predicates, ..&generated_predicates])
            (lower_type(output) => output)
            (lower_method_contents(body) => body)
            ----------------------------------- ("lower_method_body")
            (lower_method_body(surface::MethodDeclBoundData { this, inputs, output, predicates, body }) =>
                (core::MethodDeclBoundData::new(core::ThisDecl::new(perm), &core_inputs, output, predicates, body), &generated))
        )
    }
}

judgment_fn! {
    pub fn lower_receiver(permission: surface::ReceiverPermission)
        => (core::Perm, Vec<core::BoundVar>, Vec<core::Predicate>) {
        debug(permission)

        (
            ----------------------------------- ("explicit")
            (lower_receiver(permission: surface::Perm) =>
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
            (lower_type(ty) => ty)
            ----------------------------------- ("explicit")
            (lower_parameter_type(ty @ (surface::Ty::ApplyPerm(..) | surface::Ty::GivenFrom(..))) =>
                (ty, Vec::<core::BoundVar>::new(), Vec::<core::Predicate>::new()))
        )

        (
            (lower_parameter_type(surface::ParameterTy::any(ty)) => result)
            ----------------------------------- ("omitted_permission")
            (lower_parameter_type(ty @ (surface::Ty::NamedTy(_) | surface::Ty::Var(_))) =>
                result)
        )

        (
            (lower_type(ty) => ty)
            (let variable = core::BoundVar::fresh(core::Kind::Perm))
            ----------------------------------- ("any")
            (lower_parameter_type(surface::ParameterTy::Any(ty)) =>
                (apply_permission(core::Perm::var(variable), ty), vec![variable], Vec::<core::Predicate>::new()))
        )

        (
            (lower_type(ty) => ty)
            (let variable = core::BoundVar::fresh(core::Kind::Perm))
            ----------------------------------- ("mutable")
            (lower_parameter_type(surface::ParameterTy::Mutable(ty)) =>
                (apply_permission(core::Perm::var(variable), ty), vec![variable], vec![core::Predicate::mut_(variable)]))
        )
    }
}

judgment_fn! {
    pub fn lower_block(term: surface::Block) => core::Block {
        debug(term)

        (
            (let core_statements: Vec<core::Statement> = vec![])
            (for_all(statement in statements) with(core_statements)
                (lower_statement(statement) => statement)
                (let core_statements: Vec<core::Statement> = seq![..&core_statements, statement].upcast()))
            ----------------------------------- ("lower_block")
            (lower_block(surface::Block { statements }) => core::Block::new(core_statements))
        )
    }
}

judgment_fn! {
    pub fn lower_named_type(term: surface::NamedTy) => core::NamedTy {
        debug(term)

        (
            (lower_parameters(parameters) => parameters)
            ----------------------------------- ("lower_named_type")
            (lower_named_type(surface::NamedTy { name, parameters }) => core::NamedTy::new(name, parameters))
        )
    }
}

judgment_fn! {
    pub fn lower_decl(term: surface::Decl) => core::Decl {
        debug(term)

        (
            (lower_class(class) => class)
            ----------------------------------- ("ClassDecl")
            (lower_decl(class: surface::ClassDecl) => class)
        )
    }
}

judgment_fn! {
    pub fn lower_method_contents(term: surface::MethodBody) => core::MethodBody {
        debug(term)

        (
            ----------------------------------- ("Trusted")
            (lower_method_contents(surface::MethodBody::Trusted) => core::MethodBody::Trusted)
        )

        (
            (lower_block(block) => block)
            ----------------------------------- ("Block")
            (lower_method_contents(block: surface::Block) => block)
        )
    }
}

judgment_fn! {
    pub fn lower_statement(term: surface::Statement) => core::Statement {
        debug(term)

        (
            (lower_expr(expr) => expr)
            ----------------------------------- ("Expr")
            (lower_statement(expr: surface::Expr) => expr)
        )

        (
            (lower_ascription(ascription) => ascription)
            (lower_expr(&**value) => value)
            ----------------------------------- ("Let")
            (lower_statement(surface::Statement::Let(name, ascription, value)) =>
                core::Statement::let_(name, ascription, value))
        )

        (
            (lower_expr(value) => value)
            ----------------------------------- ("Reassign")
            (lower_statement(surface::Statement::Reassign(place, value)) =>
                core::Statement::reassign(place, value))
        )

        (
            ----------------------------------- ("Drop")
            (lower_statement(surface::Statement::Drop(place)) => core::Statement::drop(place))
        )

        (
            (lower_block(block) => block)
            ----------------------------------- ("Loop")
            (lower_statement(surface::Statement::Loop(block)) => core::Statement::loop_(block))
        )

        (
            ----------------------------------- ("Break")
            (lower_statement(surface::Statement::Break) => core::Statement::Break)
        )

        (
            (lower_expr(value) => value)
            ----------------------------------- ("Return")
            (lower_statement(surface::Statement::Return(value)) => core::Statement::return_(value))
        )

        (
            (lower_expr(value) => value)
            ----------------------------------- ("Print")
            (lower_statement(surface::Statement::Print(value)) => core::Statement::print(value))
        )
    }
}

judgment_fn! {
    pub fn lower_ascription(term: surface::Ascription) => core::Ascription {
        debug(term)

        (
            ----------------------------------- ("NoTy")
            (lower_ascription(surface::Ascription::NoTy) => core::Ascription::NoTy)
        )

        (
            (lower_type(ty) => ty)
            ----------------------------------- ("Ty")
            (lower_ascription(ty: surface::Ty) => ty)
        )
    }
}

judgment_fn! {
    pub fn lower_expr(term: surface::Expr) => core::Expr {
        debug(term)

        (
            (lower_block(block) => block)
            ----------------------------------- ("Block")
            (lower_expr(block: surface::Block) => block)
        )

        (
            ----------------------------------- ("Integer")
            (lower_expr(surface::Expr::Integer(value)) => core::Expr::integer(value))
        )

        (
            ----------------------------------- ("True")
            (lower_expr(surface::Expr::True) => core::Expr::True)
        )

        (
            ----------------------------------- ("False")
            (lower_expr(surface::Expr::False) => core::Expr::False)
        )

        (
            (lower_expr(&**left) => left)
            (lower_expr(&**right) => right)
            ----------------------------------- ("BinaryOp")
            (lower_expr(surface::Expr::BinaryOp(left, op, right)) => core::Expr::binary_op(left, op, right))
        )

        (
            ----------------------------------- ("Place")
            (lower_expr(place: surface::PlaceExpr) => place)
        )

        (
            (lower_expr(&**value) => value)
            ----------------------------------- ("Share")
            (lower_expr(surface::Expr::ShareValue(value)) => core::Expr::share_value(value))
        )

        (
            (lower_exprs(elements) => elements)
            ----------------------------------- ("Tuple")
            (lower_expr(surface::Expr::Tuple(elements)) => core::Expr::tuple(elements))
        )

        (
            (lower_expr(&**receiver) => receiver)
            (lower_parameters(parameters) => parameters)
            (lower_exprs(arguments) => arguments)
            ----------------------------------- ("Call")
            (lower_expr(surface::Expr::Call(receiver, method, parameters, arguments)) =>
                core::Expr::call(receiver, method, parameters, arguments))
        )

        (
            (lower_parameters(parameters) => parameters)
            (lower_exprs(arguments) => arguments)
            ----------------------------------- ("SigilCall")
            (lower_expr(surface::Expr::SigilCall(surface::SigilCallReceiver { place_expr }, method, parameters, arguments)) =>
                core::Expr::call(core::Expr::place(place_expr), method, parameters, arguments))
        )

        (
            (lower_parameters(parameters) => parameters)
            (lower_exprs(arguments) => arguments)
            ----------------------------------- ("New")
            (lower_expr(surface::Expr::New(class, parameters, arguments)) =>
                core::Expr::new(class, parameters, arguments))
        )

        (
            ----------------------------------- ("Clear")
            (lower_expr(surface::Expr::Clear(name)) => core::Expr::clear(name))
        )

        (
            (lower_expr(&**condition) => condition)
            (lower_expr(&**then_expr) => then_expr)
            (lower_expr(&**else_expr) => else_expr)
            ----------------------------------- ("If")
            (lower_expr(surface::Expr::If(condition, then_expr, else_expr)) =>
                core::Expr::if_(condition, then_expr, else_expr))
        )

        (
            (lower_parameters(parameters) => parameters)
            ----------------------------------- ("SizeOf")
            (lower_expr(surface::Expr::SizeOf(parameters)) => core::Expr::size_of(parameters))
        )

        (
            (lower_parameters(parameters) => parameters)
            (lower_expr(&**capacity) => capacity)
            ----------------------------------- ("ArrayNew")
            (lower_expr(surface::Expr::ArrayNew(parameters, capacity)) =>
                core::Expr::array_new(parameters, capacity))
        )

        (
            (lower_parameters(parameters) => parameters)
            (lower_expr(&**array) => array)
            ----------------------------------- ("ArrayCapacity")
            (lower_expr(surface::Expr::ArrayCapacity(parameters, array)) =>
                core::Expr::array_capacity(parameters, array))
        )

        (
            (lower_parameters(parameters) => parameters)
            (lower_expr(&**array) => array)
            (lower_expr(&**index) => index)
            ----------------------------------- ("ArrayGive")
            (lower_expr(surface::Expr::ArrayGive(parameters, array, index)) =>
                core::Expr::array_give(parameters, array, index))
        )

        (
            (lower_parameters(parameters) => parameters)
            (lower_expr(&**array) => array)
            (lower_expr(&**start) => start)
            (lower_expr(&**end) => end)
            ----------------------------------- ("ArrayDrop")
            (lower_expr(surface::Expr::ArrayDrop(parameters, array, start, end)) =>
                core::Expr::array_drop(parameters, array, start, end))
        )

        (
            (lower_parameters(parameters) => parameters)
            (lower_expr(&**array) => array)
            (lower_expr(&**index) => index)
            (lower_expr(&**value) => value)
            ----------------------------------- ("ArrayWrite")
            (lower_expr(surface::Expr::ArrayWrite(parameters, array, index, value)) =>
                core::Expr::array_write(parameters, array, index, value))
        )

        (
            (lower_parameters(parameters) => parameters)
            (lower_expr(&**value) => value)
            ----------------------------------- ("IsLastRef")
            (lower_expr(surface::Expr::IsLastRef(parameters, value)) =>
                core::Expr::is_last_ref(parameters, value))
        )

        (
            ----------------------------------- ("Panic")
            (lower_expr(surface::Expr::Panic) => core::Expr::Panic)
        )
    }
}

judgment_fn! {
    pub fn lower_exprs(terms: Vec<surface::Expr>) => Vec<core::Expr> {
        debug(terms)

        (
            (let expressions: Vec<core::Expr> = vec![])
            (for_all(expr in terms) with(expressions)
                (lower_expr(expr) => expr)
                (let expressions: Vec<core::Expr> = seq![..&expressions, expr].upcast()))
            ----------------------------------- ("lower_exprs")
            (lower_exprs(terms) => expressions)
        )
    }
}

judgment_fn! {
    pub fn lower_parameters(terms: Vec<surface::Parameter>) => Vec<core::Parameter> {
        debug(terms)

        (
            (let parameters: Vec<core::Parameter> = vec![])
            (for_all(parameter in terms) with(parameters)
                (lower_parameter(parameter) => parameter)
                (let parameters: Vec<core::Parameter> = seq![..&parameters, parameter].upcast()))
            ----------------------------------- ("lower_parameters")
            (lower_parameters(terms) => parameters)
        )
    }
}

judgment_fn! {
    pub fn lower_parameter(term: surface::Parameter) => core::Parameter {
        debug(term)

        (
            (lower_type(ty) => ty)
            ----------------------------------- ("Ty")
            (lower_parameter(ty: surface::Ty) => ty)
        )

        (
            ----------------------------------- ("Perm")
            (lower_parameter(permission: surface::Perm) => permission)
        )
    }
}

judgment_fn! {
    pub fn lower_type(term: surface::Ty) => core::Ty {
        debug(term)

        (
            (lower_named_type(ty) => ty)
            ----------------------------------- ("NamedTy")
            (lower_type(ty: surface::NamedTy) => ty)
        )

        (
            ----------------------------------- ("Var")
            (lower_type(variable: surface::Variable) => variable)
        )

        (
            (lower_type(&**ty) => ty)
            ----------------------------------- ("ApplyPerm")
            (lower_type(surface::Ty::ApplyPerm(permission, ty)) => apply_permission(permission, ty))
        )

        (
            (lower_type(&**ty) => ty)
            ----------------------------------- ("given origins shorthand")
            (lower_type(surface::Ty::GivenFrom(origins, ty)) =>
                apply_permission(core::Perm::given_from(origins), ty))
        )
    }
}

/// Match the core grammar's permission grouping when a surface shorthand
/// interrupts an otherwise contiguous permission prefix.
pub(crate) fn apply_permission(
    permission: impl Upcast<core::Perm>,
    ty: impl Upcast<core::Ty>,
) -> core::Ty {
    let permission = permission.upcast();
    match ty.upcast() {
        core::Ty::ApplyPerm(inner, ty) => {
            apply_permission(concat_permissions(&permission, &inner), &*ty)
        }
        ty => core::Ty::apply_perm(permission, ty),
    }
}

fn concat_permissions(outer: &core::Perm, inner: &core::Perm) -> core::Perm {
    match outer {
        core::Perm::Apply(first, rest) => core::Perm::apply(first, concat_permissions(rest, inner)),
        outer => core::Perm::apply(outer, inner),
    }
}

judgment_fn! {
    pub fn lower_predicates(terms: Vec<surface::Predicate>) => Vec<core::Predicate> {
        debug(terms)

        (
            (let predicates: Vec<core::Predicate> = vec![])
            (for_all(predicate in terms) with(predicates)
                (lower_predicate(predicate) => predicate)
                (let predicates: Vec<core::Predicate> = seq![..&predicates, predicate].upcast()))
            ----------------------------------- ("lower_predicates")
            (lower_predicates(terms) => predicates)
        )
    }
}

judgment_fn! {
    pub fn lower_predicate(term: surface::Predicate) => core::Predicate {
        debug(term)

        (
            (lower_parameter(parameter) => parameter)
            ----------------------------------- ("Parameter")
            (lower_predicate(surface::Predicate::Parameter(kind, parameter)) =>
                core::Predicate::parameter(kind, parameter))
        )

        (
            (lower_parameter(parameter) => parameter)
            ----------------------------------- ("Variance")
            (lower_predicate(surface::Predicate::Variance(kind, parameter)) =>
                core::Predicate::variance(kind, parameter))
        )
    }
}
