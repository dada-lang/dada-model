use std::sync::Arc;

use fn_error_context::context;
use formality_core::Fallible;

use crate::grammar::{Decl, Program};

mod cancellation;
mod classes;
mod env;
mod flow;
mod methods;
mod type_expr;
mod type_places;
mod type_rewrite;
mod type_subtype;
mod types;

#[cfg(test)]
mod tests;

mod quantifiers;

#[context("check program `{program:?}`")]
pub fn check_program(program: &Arc<Program>) -> Fallible<()> {
    for decl in &program.decls {
        check_decl(program, decl)?;
    }
    Ok(())
}

fn check_decl(program: &Arc<Program>, decl: &Decl) -> Fallible<()> {
    match decl {
        Decl::ClassDecl(class_decl) => classes::check_class(program, class_decl),
    }
}
