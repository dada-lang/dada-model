use fn_error_context::context;
use formality_core::Fallible;

use crate::grammar::{Decl, Program};

mod classes;
mod env;
mod functions;
mod places;
mod types;

#[cfg(test)]
mod tests;

mod quantifiers;

#[context("check program `{program:?}`")]
pub fn check_program(program: &Program) -> Fallible<()> {
    for decl in &program.decls {
        check_decl(program, decl)?;
    }
    Ok(())
}

fn check_decl(program: &Program, decl: &Decl) -> Fallible<()> {
    match decl {
        Decl::ClassDecl(class_decl) => classes::check_class(program, class_decl),
        Decl::FnDecl(fn_decl) => functions::check_fn(program, fn_decl),
    }
}
