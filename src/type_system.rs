use std::sync::Arc;

use formality_core::judgment_fn;

use crate::grammar::{Decl, Program};

mod accesses;
mod blocks;
mod classes;
mod env;
mod expressions;
mod in_flight;
mod liveness;
mod local_liens;
mod methods;
mod perm_matcher;
mod places;
mod predicates;
mod redperms;
mod statements;
mod subtypes;
mod types;

#[cfg(test)]
mod tests;

mod quantifiers;

// ANCHOR: check_program
judgment_fn! {
    pub fn check_program(
        program: Arc<Program>,
    ) => () {
        debug(program)

        (
            (quantifiers::for_all(program.decls.clone(), &|decl| check_decl(&program, decl)) => ())
            ----------------------- ("check_program")
            (check_program(program) => ())
        )
    }
}

judgment_fn! {
    fn check_decl(
        program: Arc<Program>,
        decl: Decl,
    ) => () {
        debug(decl, program)

        (
            (classes::check_class(&program, &class_decl) => ())
            ----------------------- ("class")
            (check_decl(program, Decl::ClassDecl(class_decl)) => ())
        )
    }
}
// ANCHOR_END: check_program
