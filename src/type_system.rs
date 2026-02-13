use std::sync::Arc;

use fn_error_context::context;
use formality_core::{judgment::ProofTree, Fallible};

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
#[context("check program `{program:?}`")]
pub fn check_program(program: &Arc<Program>) -> Fallible<ProofTree> {
    let mut proof_tree = ProofTree::new("check_program", None, vec![]);
    for decl in &program.decls {
        proof_tree.children.push(check_decl(program, decl)?);
    }
    Ok(proof_tree)
}

fn check_decl(program: &Arc<Program>, decl: &Decl) -> Fallible<ProofTree> {
    match decl {
        Decl::ClassDecl(class_decl) => {
            let ((), proof_tree) = classes::check_class(program, class_decl).into_singleton()?;
            Ok(proof_tree)
        }
    }
}
// ANCHOR_END: check_program
