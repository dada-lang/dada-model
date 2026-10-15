//! Generic-argument diagnostics recovered from a resolved core signature.
//!
//! Generated type and permission variables occur in their originating receiver or input
//! type. Reporting those occurrences also helps explicitly declared generics,
//! without storing surface-only metadata in semantic core terms.

use formality_core::{visit::CoreVisit, Fallible, Upcast};

use super::{MethodDecl, MethodDeclBoundData, Parameter, Variable};

impl MethodDecl {
    /// Instantiate explicit call arguments, explaining failed slots in terms of
    /// the value parameters that use them. Successful instantiation is unchanged.
    pub fn instantiate_for_call(&self, arguments: &[Parameter]) -> Fallible<MethodDeclBoundData> {
        self.binder.instantiate_with(arguments).map_err(|error| {
            let (variables, data) = self.binder.open();
            let slots = variables
                .iter()
                .enumerate()
                .map(|(index, variable)| {
                    let variable: Variable = variable.upcast();
                    let mut uses = vec![];
                    if data.this.perm.free_variables().contains(&variable) {
                        uses.push("receiver `self`".to_owned());
                    }
                    for input in &data.inputs {
                        if input.ty.free_variables().contains(&variable) {
                            uses.push(format!("parameter `{:?}`", input.name));
                        }
                    }
                    if uses.is_empty() && data.output.free_variables().contains(&variable) {
                        uses.push("return type".to_owned());
                    }
                    if uses.is_empty() {
                        uses.push("not used by value inputs".to_owned());
                    }
                    format!("{index}: {:?} for {}", variable.kind(), uses.join(", "))
                })
                .collect::<Vec<_>>()
                .join("; ");

            // Debug syntax remains diagnostic text, not a claimed source-format
            // round trip. Keep the expanded signature and omit the method body.
            let bound = self.binder.peek();
            let mut inputs = vec![format!("{:?}", bound.this)];
            inputs.extend(bound.inputs.iter().map(|input| {
                format!("{:?}: {:?}", input.name, input.ty)
            }));
            let predicates = if bound.predicates.is_empty() {
                String::new()
            } else {
                format!(" where {:?}", bound.predicates)
            };
            anyhow::anyhow!(
                "cannot instantiate method `{:?}`: {}\nexpected {} explicit generic arguments, received {}\ngeneric slots (zero-based): [{}]\nexpanded signature: fn {:?}{:?}({}) → {:?}{}",
                self.name,
                error,
                self.binder.len(),
                arguments.len(),
                slots,
                self.name,
                self.binder.kinds(),
                inputs.join(", "),
                bound.output,
                predicates,
            )
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        core::grammar::{Perm, Ty},
        dada_lang,
    };

    #[test]
    fn failed_generic_slots_name_the_receiver_and_inputs() {
        let method: MethodDecl =
            dada_lang::term("fn target[type T, perm R, perm P](R self, x: P T) → T ...;");
        let error = method.instantiate_for_call(&[]).unwrap_err().to_string();
        assert!(
            error.contains("expected 3 explicit generic arguments, received 0"),
            "{error}"
        );
        assert!(error.contains("0: type for parameter `x`"), "{error}");
        assert!(error.contains("1: perm for receiver `self`"), "{error}");
        assert!(error.contains("2: perm for parameter `x`"), "{error}");
        assert!(error.contains("expanded signature: fn target"), "{error}");
    }

    #[test]
    fn wrong_kinds_keep_the_underlying_error_and_correct_arguments_are_unchanged() {
        let method: MethodDecl =
            dada_lang::term("fn target[type T, perm R](R self, x: given T) ...;");
        let error = method
            .instantiate_for_call(&[Parameter::Perm(Perm::Given), Parameter::Perm(Perm::Shared)])
            .unwrap_err()
            .to_string();
        assert!(
            error.contains("parameter 0 has kind perm but should have kind type"),
            "{error}"
        );
        let arguments = [Parameter::Ty(Ty::int()), Parameter::Perm(Perm::Shared)];
        assert_eq!(
            method.instantiate_for_call(&arguments).unwrap(),
            method.binder.instantiate_with(&arguments).unwrap()
        );
    }
}
