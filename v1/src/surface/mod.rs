//! Surface syntax and structural lowering into the explicit core language.
//!
//! Declaration sugar introduces explicit core permission binders. Every program
//! entry point lowers before checking or interpretation; calls remain explicit.

pub mod desugar;
pub mod grammar;

/// Shared entry point for CLI input and program assertions. Interpreter-only
/// callers use the same lowering but may deliberately omit core checking.
pub fn parse_program(
    input: &str,
) -> formality_core::Fallible<std::sync::Arc<crate::core::grammar::Program>> {
    let parsed: grammar::Program = crate::dada_lang::try_term(input)?;
    Ok(std::sync::Arc::new(desugar::program(&parsed)?))
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod sugar_tests;
