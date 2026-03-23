//! Alpha-renaming support for method bodies.
//!
//! When the interpreter calls a method, it alpha-renames all locally-declared
//! variables to fresh depth-prefixed names (e.g., `x` → `_1_x`, `self` →
//! `_1_self`). This allows the method body to execute in the caller's env
//! so that place references from the caller's scope (e.g., `v` in `mut[v]`)
//! remain resolvable.

use crate::grammar::{
    Block, Expr, MethodBody, MethodDeclBoundData, Statement, ValueId, Var,
};
use crate::type_system::in_flight::{InFlight, Transform};

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
/// and the list of renamed vars.
pub fn alpha_rename_method(
    method: &MethodDeclBoundData,
    depth: usize,
) -> (MethodDeclBoundData, Vec<Var>, Vec<Var>) {
    let bound_vars = collect_bound_vars(method);

    let renamed_vars: Vec<Var> = bound_vars
        .iter()
        .map(|var| {
            let new_name = match var {
                Var::This => format!("_{depth}_self"),
                Var::Id(name) => format!("_{depth}_{name:?}"),
                other => panic!("unexpected var in bound_vars: {other:?}"),
            };
            let new_id: ValueId = crate::dada_lang::term(&new_name);
            Var::Id(new_id)
        })
        .collect();

    let renamed = method.with_places_transformed(Transform::Rename(&bound_vars, &renamed_vars));
    (renamed, bound_vars, renamed_vars)
}
