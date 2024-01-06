use std::sync::Arc;

use anyhow::bail;
use contracts::requires;
use formality_core::{set, term, visit::CoreVisit, Fallible, Map, Set, To, Upcast};

use crate::{
    dada_lang::{
        grammar::{Binder, ExistentialVar, UniversalVar, VarIndex, Variable},
        Term,
    },
    grammar::{Kind, LocalVariableDecl, Parameter, Predicate, Program, Ty, Var},
};

use super::in_flight::{InFlight, Transform};

#[derive(Clone, Debug, Ord, Eq, PartialEq, PartialOrd, Hash)]
pub struct Env {
    program: Arc<Program>,
    universe: Universe,
    in_scope_vars: Vec<Variable>,
    local_variables: Map<Var, Ty>,
    existentials: Vec<Existential>,
    assumptions: Set<Predicate>,
}

#[term]
#[derive(Copy)]
pub struct Universe(usize);

/// Information about some existential variable `?X`...
#[term]
pub struct Existential {
    /// Tracks the number of universal variables that were in scope
    /// when this existential is created. It can name those.
    /// It cannot name other universals.
    pub universe: Universe,

    /// Kind of the variable
    pub kind: Kind,

    /// ...types `T` where `T <: ?X`
    pub lower_bounds: Set<Parameter>,

    /// ...types `T` where `?X <: T`
    pub upper_bounds: Set<Parameter>,

    /// ...bound on the value this existential may eventually have (and hence on all bounds)
    pub perm_bound: Option<PermBound>,
}

#[term]
#[derive(Copy)]
pub enum PermBound {
    /// Must be `shared(_)`
    Shared,

    /// Must be `leased(_)`
    Leased,

    /// Must be `My`
    Mine,
}

formality_core::cast_impl!(Env);

impl Env {
    pub fn new(program: impl Upcast<Arc<Program>>) -> Self {
        Env {
            program: program.upcast(),
            universe: Universe(0),
            in_scope_vars: vec![],
            local_variables: Default::default(),
            existentials: vec![],
            assumptions: set![],
        }
    }

    pub fn add_assumptions(&mut self, assumptions: impl IntoIterator<Item = Predicate>) {
        self.assumptions.extend(assumptions);
    }

    pub fn contains_assumption(&self, assumption: impl Upcast<Predicate>) -> bool {
        let assumption = assumption.upcast();
        assert!(assumption.references_only_universal_variables());
        self.assumptions.contains(&assumption)
    }

    pub fn assumptions(&self) -> &Set<Predicate> {
        &self.assumptions
    }

    pub fn program(&self) -> &Program {
        &self.program
    }

    /// Allows invoking `push` methods on an `&self` environment;
    /// returns the new environment.
    pub fn with<T>(&self, op: impl FnOnce(&mut Env) -> Fallible<T>) -> Fallible<(Env, T)> {
        let mut env = self.clone();
        let value = op(&mut env)?;
        Ok((env, value))
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
    pub fn var_ty(&self, var: impl Upcast<Var>) -> Option<&Ty> {
        let var: Var = var.upcast();
        self.local_variables.get(&var)
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

    /// Create a fresh universal variable of kind `kind`.
    pub fn mutual_supertype(&mut self, ty1: impl Upcast<Ty>, ty2: impl Upcast<Ty>) -> Ty {
        let ty1: Ty = ty1.upcast();
        let ty2: Ty = ty2.upcast();
        if ty1 == ty2 {
            ty1
        } else {
            let var = self.push_next_existential_var(Kind::Ty);
            self.new_lower_bound(ty1, var).unwrap();
            self.new_lower_bound(ty2, var).unwrap();
            Ty::var(var)
        }
    }

    /// Replace all the bound variables in `b` with fresh universal variables
    /// and return the contents.
    pub fn open_universally<T: Term>(&mut self, b: &Binder<T>) -> (Vec<UniversalVar>, T) {
        let universal_vars: Vec<_> = b
            .kinds()
            .iter()
            .map(|&k| self.push_next_universal_var(k))
            .collect();

        let result = b.instantiate_with(&universal_vars).unwrap();

        (universal_vars, result)
    }

    /// Introduces a program variable into scope, failing if this would introduce shadowing
    /// (we don't support shadowing so as to avoid worry about what local variables are being
    /// named in the `Place` values that appear in types).
    pub fn push_local_variable_decl(&mut self, v: impl Upcast<LocalVariableDecl>) -> Fallible<()> {
        let v: LocalVariableDecl = v.upcast();
        self.push_local_variable(v.name, v.ty)
    }

    /// Introduces a program variable into scope.
    pub fn push_local_variable(
        &mut self,
        var: impl Upcast<Var>,
        ty: impl Upcast<Ty>,
    ) -> Fallible<()> {
        let var = var.upcast();
        let ty = ty.upcast();

        if self.local_variables.contains_key(&var) {
            bail!("cannot push local variable `{var:?}`, it shadows another variable in scope");
        }

        self.local_variables.insert(var, ty);
        Ok(())
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
            lower_bounds: set![],
            upper_bounds: set![],
            perm_bound: None,
        });
        self.in_scope_vars.push(existential.upcast());
        existential
    }

    #[requires(self.var_in_scope(var))]
    pub fn existential(&self, var: ExistentialVar) -> &Existential {
        &self.existentials[var.var_index.index]
    }

    #[requires(self.var_in_scope(var))]
    fn existential_mut(&mut self, var: ExistentialVar) -> &mut Existential {
        &mut self.existentials[var.var_index.index]
    }

    #[requires(self.var_in_scope(var))]
    pub fn has_perm_bound(&self, var: ExistentialVar, perm_bound: PermBound) -> bool {
        let existential = self.existential(var);
        Some(perm_bound) == existential.perm_bound
    }

    #[requires(self.var_in_scope(var))]
    pub fn has_lower_bound(
        &self,
        lower_bound: impl Upcast<Parameter>,
        var: ExistentialVar,
    ) -> bool {
        let lower_bound: Parameter = lower_bound.upcast();
        self.existential(var).lower_bounds.contains(&lower_bound)
    }

    #[requires(self.var_in_scope(var))]
    pub fn has_upper_bound(
        &self,
        var: ExistentialVar,
        upper_bound: impl Upcast<Parameter>,
    ) -> bool {
        let upper_bound: Parameter = upper_bound.upcast();
        self.existential(var).upper_bounds.contains(&upper_bound)
    }

    #[requires(self.var_in_scope(var))]
    pub fn new_perm_bound(&mut self, var: ExistentialVar, perm_bound: PermBound) -> Fallible<()> {
        let existential = self.existential_mut(var);
        if let Some(p) = existential.perm_bound {
            bail!(
                "cannot set perm bound of `{:?}` to `{:?}`: var already has a perm bound `{:?}`",
                var,
                perm_bound,
                p,
            )
        } else {
            existential.perm_bound = Some(perm_bound);
            Ok(())
        }
    }

    #[requires(self.var_in_scope(var))]
    pub fn new_lower_bound(
        &mut self,
        lower_bound: impl Upcast<Parameter>,
        var: ExistentialVar,
    ) -> Fallible<()> {
        // FIXME: universes and other occurs check

        let lower_bound: Parameter = lower_bound.upcast();
        let existential = self.existential_mut(var);
        if existential.lower_bounds.insert(lower_bound) {
            Ok(())
        } else {
            bail!("cannot add new lower bound to `{:?}`: already present", var)
        }
    }

    #[requires(self.var_in_scope(var))]
    pub fn new_upper_bound(
        &mut self,
        var: ExistentialVar,
        upper_bound: impl Upcast<Parameter>,
    ) -> Fallible<()> {
        let upper_bound: Parameter = upper_bound.upcast();
        let existential = self.existential_mut(var);
        if existential.upper_bounds.insert(upper_bound) {
            Ok(())
        } else {
            bail!("cannot add new upper bound to `{:?}`: already present", var)
        }
    }
}

impl InFlight for Env {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        Env {
            program: self.program.clone(),
            universe: self.universe,
            in_scope_vars: self.in_scope_vars.clone(),
            local_variables: self.local_variables.with_places_transformed(transform),
            existentials: self.existentials.with_places_transformed(transform),
            assumptions: self.assumptions.with_places_transformed(transform),
        }
    }
}

impl InFlight for Existential {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        Existential {
            universe: self.universe,
            kind: self.kind,
            lower_bounds: self.lower_bounds.with_places_transformed(transform),
            upper_bounds: self.upper_bounds.with_places_transformed(transform),
            perm_bound: self.perm_bound,
        }
    }
}

impl InFlight for Var {
    fn with_places_transformed(&self, _transform: Transform<'_>) -> Self {
        self.clone()
    }
}

impl std::fmt::Debug for Env {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Env")
            .field("program", &"...")
            .field("universe", &self.universe)
            .field("in_scope_vars", &self.in_scope_vars)
            .field("local_variables", &self.local_variables)
            .field("existentials", &self.existentials)
            .field("assumptions", &self.assumptions)
            .finish()
    }
}
