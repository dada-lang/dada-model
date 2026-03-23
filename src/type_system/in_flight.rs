use std::sync::Arc;

use formality_core::{seq, Map, Set, Upcast};

use crate::grammar::{
    Ascription, Block, DropBody, Expr, FieldDecl, LocalVariableDecl, MethodBody,
    MethodDeclBoundData, NamedTy, Parameter, Perm, Place, PlaceExpr, Predicate, Statement,
    Projection, ThisDecl, Ty, ValueId, Var,
};

pub trait InFlight: Sized {
    fn with_place_in_flight(&self, place: impl Upcast<Place>) -> Self {
        let place = place.upcast();
        self.with_places_transformed(Transform::Give(&place))
    }

    fn with_in_flight_stored_to(&self, place: impl Upcast<Place>) -> Self {
        let place = place.upcast();
        self.with_places_transformed(Transform::Put(&[Var::InFlight], &[place]))
    }

    fn with_this_stored_to(&self, place: impl Upcast<Place>) -> Self {
        let place = place.upcast();
        self.with_places_transformed(Transform::Put(&[Var::This], &[place]))
    }

    fn with_var_stored_to(&self, input: impl Upcast<Var>, place: impl Upcast<Place>) -> Self {
        self.with_vars_stored_to(vec![input], vec![place])
    }

    fn with_vars_stored_to(
        &self,
        inputs: impl Upcast<Vec<Var>>,
        places: impl Upcast<Vec<Place>>,
    ) -> Self {
        let inputs = inputs.upcast();
        let places = places.upcast();
        self.with_places_transformed(Transform::Put(&inputs, &places))
    }

    fn with_places_transformed(&self, transform: Transform<'_>) -> Self;
}

#[derive(Copy, Clone)]
pub enum Transform<'a> {
    Give(&'a Place),
    Put(&'a [Var], &'a [Place]),
}

impl<T> InFlight for Option<T>
where
    T: InFlight,
{
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        self.as_ref().map(|e| e.with_places_transformed(transform))
    }
}

impl<T> InFlight for Vec<T>
where
    T: InFlight,
{
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        self.iter()
            .map(|e| e.with_places_transformed(transform))
            .collect()
    }
}

impl<T> InFlight for Set<T>
where
    T: InFlight + Ord,
{
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        self.iter()
            .map(|e| e.with_places_transformed(transform))
            .collect()
    }
}

impl<K, V> InFlight for Map<K, V>
where
    K: InFlight + Ord,
    V: InFlight,
{
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        self.iter()
            .map(|(k, v)| {
                (
                    k.with_places_transformed(transform),
                    v.with_places_transformed(transform),
                )
            })
            .collect()
    }
}

impl InFlight for LocalVariableDecl {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        LocalVariableDecl {
            name: rename_value_id(&self.name, transform),
            ty: self.ty.with_places_transformed(transform),
        }
    }
}

impl InFlight for Parameter {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        match self {
            Parameter::Ty(ty) => ty.with_places_transformed(transform).upcast(),
            Parameter::Perm(perm) => perm.with_places_transformed(transform).upcast(),
        }
    }
}

impl InFlight for Ty {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        match self {
            Ty::NamedTy(n) => n.with_places_transformed(transform).upcast(),
            Ty::Var(v) => Ty::Var(v.clone()),
            Ty::ApplyPerm(perm, ty) => Ty::apply_perm(
                perm.with_places_transformed(transform),
                ty.with_places_transformed(transform),
            ),
        }
    }
}

impl InFlight for NamedTy {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        Self {
            name: self.name.clone(),
            parameters: self.parameters.with_places_transformed(transform),
        }
    }
}

impl InFlight for Perm {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        match self {
            Perm::Given => Perm::Given,
            Perm::Shared => Perm::Shared,
            Perm::Mv(places) => Perm::Mv(places.with_places_transformed(transform)),
            Perm::Rf(places) => Perm::Rf(places.with_places_transformed(transform)),
            Perm::Mt(places) => Perm::Mt(places.with_places_transformed(transform)),
            Perm::Var(v) => Perm::Var(v.clone()),
            Perm::Apply(l, r) => Perm::Apply(
                l.with_places_transformed(transform).into(),
                r.with_places_transformed(transform).into(),
            ),
        }
    }
}

impl InFlight for Place {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        match transform {
            Transform::Give(place) => {
                if place.is_prefix_of(self) {
                    Place {
                        var: Var::InFlight,
                        projections: self.projections[place.projections.len()..].to_vec(),
                    }
                } else {
                    self.clone()
                }
            }

            Transform::Put(vars, places) => {
                if let Some(index) = vars.iter().position(|var| self.var == *var) {
                    let place = &places[index];
                    Place::new(&place.var, seq![..&place.projections, ..&self.projections])
                } else {
                    self.clone()
                }
            }
        }
    }
}

impl InFlight for Predicate {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        match self {
            Predicate::Parameter(kind, parameter) => {
                Predicate::Parameter(*kind, parameter.with_places_transformed(transform))
            }
            Predicate::Variance(kind, parameter) => {
                Predicate::Variance(*kind, parameter.with_places_transformed(transform))
            }
        }
    }
}

impl InFlight for Var {
    fn with_places_transformed(&self, _transform: Transform<'_>) -> Self {
        self.clone()
    }
}

impl<A: InFlight, B: InFlight> InFlight for (A, B) {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        (
            self.0.with_places_transformed(transform),
            self.1.with_places_transformed(transform),
        )
    }
}

impl<A: InFlight, B: InFlight, C: InFlight> InFlight for (A, B, C) {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        (
            self.0.with_places_transformed(transform),
            self.1.with_places_transformed(transform),
            self.2.with_places_transformed(transform),
        )
    }
}

impl InFlight for FieldDecl {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        FieldDecl {
            atomic: self.atomic.clone(),
            name: self.name.clone(),
            ty: self.ty.with_places_transformed(transform),
        }
    }
}

impl InFlight for ThisDecl {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        ThisDecl {
            perm: self.perm.with_places_transformed(transform),
        }
    }
}

// ---------------------------------------------------------------
// Arc<T>, ValueId, and AST node impls for expression/statement renaming
// ---------------------------------------------------------------

impl<T: InFlight + Clone> InFlight for Arc<T> {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        Arc::new(T::clone(self).with_places_transformed(transform))
    }
}

/// Rename a `ValueId` according to `Transform::Put` by checking if
/// `Var::Id(value_id)` is in the rename list. If so, extract the new
/// name from the target `Var::Id(new_name)`. Otherwise return unchanged.
///
/// This is used for declaration-site identifiers (e.g., `let x = ...`)
/// and variable-reference identifiers (e.g., `$$clear(x)`) that store
/// a raw `ValueId` instead of a `Var`.
fn rename_value_id(value_id: &ValueId, transform: Transform<'_>) -> ValueId {
    match transform {
        Transform::Give(_) => value_id.clone(),
        Transform::Put(vars, places) => {
            let var = Var::Id(value_id.clone());
            if let Some(index) = vars.iter().position(|v| *v == var) {
                // The target must be a simple Var::Id — extract its ValueId.
                match &places[index].var {
                    Var::Id(new_name) => new_name.clone(),
                    other => panic!(
                        "rename_value_id: expected Var::Id target for {:?}, got {:?}",
                        value_id, other
                    ),
                }
            } else {
                value_id.clone()
            }
        }
    }
}

impl InFlight for Block {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        Block {
            statements: self.statements.with_places_transformed(transform),
        }
    }
}

impl InFlight for Statement {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        match self {
            Statement::Expr(expr) => Statement::Expr(expr.with_places_transformed(transform)),
            Statement::Let(name, ascription, expr) => Statement::Let(
                rename_value_id(name, transform),
                ascription.with_places_transformed(transform),
                expr.with_places_transformed(transform),
            ),
            Statement::Reassign(place, expr) => Statement::Reassign(
                place.with_places_transformed(transform),
                expr.with_places_transformed(transform),
            ),
            Statement::Loop(block) => {
                Statement::Loop(block.with_places_transformed(transform))
            }
            Statement::Break => Statement::Break,
            Statement::Return(expr) => {
                Statement::Return(expr.with_places_transformed(transform))
            }
            Statement::Print(expr) => {
                Statement::Print(expr.with_places_transformed(transform))
            }
        }
    }
}

impl InFlight for Ascription {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        match self {
            Ascription::NoTy => Ascription::NoTy,
            Ascription::Ty(ty) => Ascription::Ty(ty.with_places_transformed(transform)),
        }
    }
}

impl InFlight for Expr {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        match self {
            Expr::Block(block) => Expr::Block(block.with_places_transformed(transform)),
            Expr::Integer(n) => Expr::Integer(*n),
            Expr::True => Expr::True,
            Expr::False => Expr::False,
            Expr::BinaryOp(lhs, op, rhs) => Expr::BinaryOp(
                lhs.with_places_transformed(transform),
                op.clone(),
                rhs.with_places_transformed(transform),
            ),
            Expr::Place(place_expr) => {
                Expr::Place(place_expr.with_places_transformed(transform))
            }
            Expr::Share(expr) => Expr::Share(expr.with_places_transformed(transform)),
            Expr::Tuple(exprs) => Expr::Tuple(exprs.with_places_transformed(transform)),
            Expr::Call(receiver, method_id, params, args) => Expr::Call(
                receiver.with_places_transformed(transform),
                method_id.clone(),
                params.with_places_transformed(transform),
                args.with_places_transformed(transform),
            ),
            Expr::New(class_name, params, args) => Expr::New(
                class_name.clone(), // class name — not a variable, don't rename
                params.with_places_transformed(transform),
                args.with_places_transformed(transform),
            ),
            Expr::Clear(var_name) => Expr::Clear(rename_value_id(var_name, transform)),
            Expr::If(cond, then_branch, else_branch) => Expr::If(
                cond.with_places_transformed(transform),
                then_branch.with_places_transformed(transform),
                else_branch.with_places_transformed(transform),
            ),
            Expr::SizeOf(params) => Expr::SizeOf(params.with_places_transformed(transform)),
            Expr::ArrayNew(params, size) => Expr::ArrayNew(
                params.with_places_transformed(transform),
                size.with_places_transformed(transform),
            ),
            Expr::ArrayCapacity(params, arr) => Expr::ArrayCapacity(
                params.with_places_transformed(transform),
                arr.with_places_transformed(transform),
            ),
            Expr::ArrayGive(params, arr, idx) => Expr::ArrayGive(
                params.with_places_transformed(transform),
                arr.with_places_transformed(transform),
                idx.with_places_transformed(transform),
            ),
            Expr::ArrayDrop(params, arr, start, count) => Expr::ArrayDrop(
                params.with_places_transformed(transform),
                arr.with_places_transformed(transform),
                start.with_places_transformed(transform),
                count.with_places_transformed(transform),
            ),
            Expr::ArrayWrite(params, arr, idx, val) => Expr::ArrayWrite(
                params.with_places_transformed(transform),
                arr.with_places_transformed(transform),
                idx.with_places_transformed(transform),
                val.with_places_transformed(transform),
            ),
            Expr::IsLastRef(params, expr) => Expr::IsLastRef(
                params.with_places_transformed(transform),
                expr.with_places_transformed(transform),
            ),
            Expr::Panic => Expr::Panic,
        }
    }
}

impl InFlight for PlaceExpr {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        PlaceExpr {
            place: self.place.with_places_transformed(transform),
            access: self.access,
        }
    }
}

impl InFlight for MethodBody {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        match self {
            MethodBody::Trusted => MethodBody::Trusted,
            MethodBody::Block(block) => {
                MethodBody::Block(block.with_places_transformed(transform))
            }
        }
    }
}

impl InFlight for DropBody {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        DropBody {
            block: self.block.with_places_transformed(transform),
        }
    }
}

impl InFlight for MethodDeclBoundData {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        MethodDeclBoundData {
            this: self.this.with_places_transformed(transform),
            inputs: self.inputs.with_places_transformed(transform),
            output: self.output.with_places_transformed(transform),
            predicates: self.predicates.with_places_transformed(transform),
            body: self.body.with_places_transformed(transform),
        }
    }
}

// ---------------------------------------------------------------
// Alpha-renaming support for method bodies
// ---------------------------------------------------------------

/// Collect all locally-declared variable names from a method body.
/// Returns the list of `Var`s that need renaming:
/// - `Var::This` (always present)
/// - `Var::Id(name)` for each input parameter
/// - `Var::Id(name)` for each `let`-bound variable in the body
fn collect_bound_vars(method: &MethodDeclBoundData) -> Vec<Var> {
    let mut vars = vec![Var::This];
    for input in &method.inputs {
        vars.push(Var::Id(input.name.clone()));
    }
    if let MethodBody::Block(block) = &method.body {
        collect_let_bound_vars_in_block(block, &mut vars);
    }
    vars
}

/// Recursively collect `Var::Id(name)` for all `let`-bound variables in a block.
fn collect_let_bound_vars_in_block(block: &Block, vars: &mut Vec<Var>) {
    for statement in &block.statements {
        collect_let_bound_vars_in_statement(statement, vars);
    }
}

fn collect_let_bound_vars_in_statement(statement: &Statement, vars: &mut Vec<Var>) {
    match statement {
        Statement::Let(name, _, _) => {
            vars.push(Var::Id(name.clone()));
        }
        Statement::Expr(expr) => collect_let_bound_vars_in_expr(expr, vars),
        Statement::Reassign(_, expr) => collect_let_bound_vars_in_expr(expr, vars),
        Statement::Loop(block) => collect_let_bound_vars_in_block(block, vars),
        Statement::Break => {}
        Statement::Return(expr) => collect_let_bound_vars_in_expr(expr, vars),
        Statement::Print(expr) => collect_let_bound_vars_in_expr(expr, vars),
    }
}

fn collect_let_bound_vars_in_expr(expr: &Expr, vars: &mut Vec<Var>) {
    match expr {
        Expr::Block(block) => collect_let_bound_vars_in_block(block, vars),
        Expr::If(cond, then_branch, else_branch) => {
            collect_let_bound_vars_in_expr(cond, vars);
            collect_let_bound_vars_in_expr(then_branch, vars);
            collect_let_bound_vars_in_expr(else_branch, vars);
        }
        Expr::BinaryOp(lhs, _, rhs) => {
            collect_let_bound_vars_in_expr(lhs, vars);
            collect_let_bound_vars_in_expr(rhs, vars);
        }
        Expr::Share(e)
        | Expr::ArrayNew(_, e)
        | Expr::ArrayCapacity(_, e)
        | Expr::IsLastRef(_, e) => {
            collect_let_bound_vars_in_expr(e, vars);
        }
        Expr::ArrayGive(_, a, b) => {
            collect_let_bound_vars_in_expr(a, vars);
            collect_let_bound_vars_in_expr(b, vars);
        }
        Expr::ArrayDrop(_, a, b, c) | Expr::ArrayWrite(_, a, b, c) => {
            collect_let_bound_vars_in_expr(a, vars);
            collect_let_bound_vars_in_expr(b, vars);
            collect_let_bound_vars_in_expr(c, vars);
        }
        Expr::Call(receiver, _, _, args) => {
            collect_let_bound_vars_in_expr(receiver, vars);
            for arg in args {
                collect_let_bound_vars_in_expr(arg, vars);
            }
        }
        Expr::Tuple(exprs) => {
            for e in exprs {
                collect_let_bound_vars_in_expr(e, vars);
            }
        }
        Expr::New(_, _, args) => {
            for arg in args {
                collect_let_bound_vars_in_expr(arg, vars);
            }
        }
        // Leaf expressions — no nested blocks
        Expr::Integer(_)
        | Expr::True
        | Expr::False
        | Expr::Place(_)
        | Expr::Clear(_)
        | Expr::SizeOf(_)
        | Expr::Panic => {}
    }
}

/// Alpha-rename all locally-declared variables in a method body.
/// `Var::This` becomes `Var::Id("_{depth}_self")`, and each
/// `Var::Id(x)` becomes `Var::Id("_{depth}_{x}")`.
///
/// Returns the renamed method data, the list of original vars,
/// and the list of renamed places (for caller-side use).
pub fn alpha_rename_method(
    method: &MethodDeclBoundData,
    depth: usize,
) -> (MethodDeclBoundData, Vec<Var>, Vec<Place>) {
    let bound_vars = collect_bound_vars(method);

    let renamed_places: Vec<Place> = bound_vars
        .iter()
        .map(|var| {
            let new_name = match var {
                Var::This => format!("_{depth}_self"),
                Var::Id(name) => format!("_{depth}_{name:?}"),
                other => panic!("unexpected var in bound_vars: {other:?}"),
            };
            let new_id: ValueId = crate::dada_lang::term(&new_name);
            Place::new(Var::Id(new_id), Vec::<Projection>::new())
        })
        .collect();

    let renamed = method.with_places_transformed(Transform::Put(&bound_vars, &renamed_places));
    (renamed, bound_vars, renamed_places)
}
