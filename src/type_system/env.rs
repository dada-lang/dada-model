use crate::{
    dada_lang::{
        grammar::{Binder, UniversalVar, VarIndex},
        Term,
    },
    grammar::{Kind, VariableDecl},
};

#[derive(Clone, Default, Debug)]
pub struct Env {
    universal_vars: Vec<UniversalVar>,
    variables: Vec<VariableDecl>,
}

impl Env {
    fn push_next_universal_var(&mut self, kind: Kind) -> UniversalVar {
        let var_index = VarIndex {
            index: self.universal_vars.len(),
        };
        let var = UniversalVar { kind, var_index };
        self.universal_vars.push(var);
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
