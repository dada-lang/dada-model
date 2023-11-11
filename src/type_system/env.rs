use formality_core::To;

use crate::{
    dada_lang::{
        grammar::{Binder, UniversalVar, VarIndex, Variable},
        Term,
    },
    grammar::{Kind, VariableDecl},
};

#[derive(Clone, Default, Debug)]
pub struct Env {
    in_scope_vars: Vec<Variable>,
    variables: Vec<VariableDecl>,
}

impl Env {
    /// Check that the variable is in the environment.
    /// This should always be true, especially because the
    /// parser is aware of in-scope variable names as it parses,
    /// so an out-of-scope variable name will generally be interpreted
    /// as a class reference or fail to parse.
    pub fn var_in_scope(&self, v: Variable) -> bool {
        match v {
            Variable::UniversalVar(_) | Variable::ExistentialVar(_) => {
                self.in_scope_vars.contains(&v)
            }
            Variable::BoundVar(_) => true,
        }
    }

    fn push_next_universal_var(&mut self, kind: Kind) -> UniversalVar {
        let var_index = VarIndex {
            index: self.in_scope_vars.len(),
        };
        let var = UniversalVar { kind, var_index };
        self.in_scope_vars.push(var.to());
        var
    }

    pub fn open_universally<T: Term>(&mut self, b: &Binder<T>) -> T {
        let universal_vars: Vec<_> = b
            .kinds()
            .iter()
            .map(|&k| self.push_next_universal_var(k))
            .collect();

        b.instantiate_with(&universal_vars).unwrap()
    }
}
