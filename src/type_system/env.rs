use formality_core::{Fallible, To};

use crate::{
    dada_lang::{
        grammar::{Binder, UniversalVar, VarIndex, Variable},
        Term,
    },
    grammar::{Kind, Ty, ValueId, VariableDecl},
};

#[derive(Clone, Default, Debug, Ord, Eq, PartialEq, PartialOrd, Hash)]
pub struct Env {
    in_scope_vars: Vec<Variable>,
    variables: Vec<VariableDecl>,
}

formality_core::cast_impl!(Env);

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

    /// Lookup a program variable named `var` and returns its type (if any).
    pub fn var_ty(&self, var: ValueId) -> Option<&Ty> {
        self.variables
            .iter()
            .rev()
            .filter_map(|vd| if vd.name == var { Some(&vd.ty) } else { None })
            .next()
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
