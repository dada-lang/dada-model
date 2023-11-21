use std::sync::Arc;

use contracts::requires;
use formality_core::{term, Fallible, To, Upcast};

use crate::{
    dada_lang::{
        grammar::{Binder, ExistentialVar, UniversalVar, VarIndex, Variable},
        Term,
    },
    grammar::{Kind, LocalVariableDecl, Parameter, Program, Ty, ValueId},
    type_system::type_subtype::sub,
};

#[derive(Clone, Debug, Ord, Eq, PartialEq, PartialOrd, Hash)]
pub struct Env {
    program: Arc<Program>,
    universe: Universe,
    in_scope_vars: Vec<Variable>,
    local_variables: Vec<LocalVariableDecl>,
    existentials: Vec<Existential>,
}

#[term]
#[derive(Copy)]
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
    lower_bounds: Vec<Parameter>,

    /// ...types `T` where `?X <: T`
    upper_bounds: Vec<Parameter>,
}

formality_core::cast_impl!(Env);

impl Env {
    pub fn new(program: impl Upcast<Arc<Program>>) -> Self {
        Env {
            program: program.upcast(),
            universe: Universe(0),
            in_scope_vars: vec![],
            local_variables: vec![],
            existentials: vec![],
        }
    }

    pub fn program(&self) -> &Program {
        &self.program
    }

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
    pub fn var_in_scope(&self, v: impl Upcast<Variable>) -> bool {
        let v: Variable = v.upcast();
        match v {
            Variable::UniversalVar(UniversalVar { kind: _, var_index }) => {
                self.in_scope_vars.contains(&v) && var_index.index < self.universe.0
            }

            Variable::ExistentialVar(ExistentialVar { kind, var_index }) => {
                self.in_scope_vars.contains(&v)
                    && var_index.index < self.existentials.len()
                    && kind == self.existentials[var_index.index].kind
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
            upper_bounds: vec![],
        });
        self.in_scope_vars.push(existential.upcast());
        existential
    }

    /// Creaets a new existential variable of the given kind.
    #[requires(self.var_in_scope(var))]
    pub fn push_existential_var_lower_bound(
        &mut self,
        parameter: impl Upcast<Parameter>,
        var: ExistentialVar,
    ) -> Fallible<()> {
        let parameter: Parameter = parameter.upcast();

        // If `parameter` is already on the lits of lower bounds, we are done.
        let existential = self.existential_mut(var);
        if existential.lower_bounds.contains(&parameter) {
            return Ok(());
        }

        // Otherwise, we have to add it to the list, and then make sure that is consistent
        // with each of the existing bounds.
        existential.lower_bounds.push(parameter);
        let lower_bounds = existential.lower_bounds.clone();
        let upper_bounds = existential.upper_bounds.clone();
        for lower_bound in &lower_bounds {
            todo!() // check mutually compatible
        }
        for upper_bound in &upper_bounds {
            self.assignable(&parameter, upper_bound)?;
        }

        Ok(())
    }

    /// Creaets a new existential variable of the given kind.
    #[requires(self.var_in_scope(var))]
    pub fn push_existential_var_upper_bound(
        &mut self,
        var: ExistentialVar,
        parameter: impl Upcast<Parameter>,
    ) -> Fallible<()> {
        let parameter: Parameter = parameter.upcast();

        // If `parameter` is already on the lits of lower bounds, we are done.
        let existential = self.existential_mut(var);
        if existential.upper_bounds.contains(&parameter) {
            return Ok(());
        }

        // Otherwise, we have to add it to the list, and then make sure that is consistent
        // with each of the existing bounds.
        existential.upper_bounds.push(parameter);
        let upper_bounds = existential.upper_bounds.clone();
        let lower_bounds = existential.lower_bounds.clone();
        for upper_bound in &upper_bounds {
            todo!()
        }
        for lower_bound in &lower_bounds {
            self.assignable(lower_bound, &parameter)?;
        }

        Ok(())
    }

    #[requires(self.var_in_scope(var))]
    fn existential_mut(&mut self, var: ExistentialVar) -> &mut Existential {
        &mut self.existentials[var.var_index.index]
    }
}
