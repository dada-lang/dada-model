use formality_core::{term, To, Upcast};

use crate::{
    dada_lang::{
        grammar::{Binder, ExistentialVar, UniversalVar, VarIndex, Variable},
        Term,
    },
    grammar::{Kind, LocalVariableDecl, Ty, ValueId},
};

#[derive(Clone, Default, Debug, Ord, Eq, PartialEq, PartialOrd, Hash)]
pub struct Env {
    universe: Universe,
    in_scope_vars: Vec<Variable>,
    local_variables: Vec<LocalVariableDecl>,
    existentials: Vec<Existential>,
}

#[term]
#[derive(Copy, Default)]
pub struct Universe(usize);

/// Information about some existential variable `?X`...
#[term]
struct Existential {
    /// Tracks the number of universal variables that were in scope
    /// when this existential is created. It can name those.
    /// It cannot name other universals.
    universe: Universe,

    /// Kind of the variable
    kind: Kind,

    /// ...types `T` where `T <: ?X`
    lower_bounds: Vec<Ty>,

    /// ...types `T` where `?X <: T`
    upper_boounds: Vec<Ty>,
}

formality_core::cast_impl!(Env);

impl Env {
    /// Allows invoking `push` methods on an `&self` environment;
    /// returns the new environment.
    pub fn with(&self, op: impl FnOnce(&mut Env)) -> Env {
        let mut env = self.clone();
        op(&mut env);
        env
    }

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
        self.local_variables
            .iter()
            .rev()
            .filter_map(|vd| if vd.name == var { Some(&vd.ty) } else { None })
            .next()
    }

    /// Create a fresh universal variable of kind `kind`.
    fn push_next_universal_var(&mut self, kind: Kind) -> UniversalVar {
        let var_index = VarIndex {
            index: self.universe.0,
        };
        let var = UniversalVar { kind, var_index };
        self.in_scope_vars.push(var.to());
        self.universe.0 += 1;
        var
    }

    /// Replace all the bound variables in `b` with fresh universal variables
    /// and return the contents.
    pub fn open_universally<T: Term>(&mut self, b: &Binder<T>) -> T {
        let universal_vars: Vec<_> = b
            .kinds()
            .iter()
            .map(|&k| self.push_next_universal_var(k))
            .collect();

        b.instantiate_with(&universal_vars).unwrap()
    }

    /// Introduces a program variable into scope.
    pub fn push_local_variable_decl(&mut self, v: impl Upcast<LocalVariableDecl>) {
        self.local_variables.push(v.upcast());
    }

    /// Introduces a program variable into scope.
    pub fn push_local_variable(&mut self, id: impl Upcast<ValueId>, ty: impl Upcast<Ty>) {
        self.push_local_variable_decl(LocalVariableDecl::new(id, ty))
    }

    /// Creaets a new existential variable of the given kind.
    pub fn push_next_existential_var(&mut self, kind: Kind) -> ExistentialVar {
        let index = self.existentials.len();
        let existential = ExistentialVar {
            kind,
            var_index: VarIndex { index },
        };
        self.existentials.push(Existential {
            universe: self.universe,
            kind,
            lower_bounds: vec![],
            upper_boounds: vec![],
        });
        self.in_scope_vars.push(existential.upcast());
        existential
    }

    /// Creaets a new existential variable of the given kind.
    pub fn push_existential_var_bound(&mut self, kind: Kind) -> ExistentialVar {
        let index = self.existentials.len();
        let existential = ExistentialVar {
            kind,
            var_index: VarIndex { index },
        };
        self.existentials.push(Existential {
            universe: self.universe,
            kind,
            lower_bounds: vec![],
            upper_boounds: vec![],
        });
        self.in_scope_vars.push(existential.upcast());
        existential
    }
}
