use std::sync::Arc;

use anyhow::bail;
use formality_core::{set, term, Fallible, Map, Set, To, Upcast};

use crate::{
    dada_lang::{
        grammar::{Binder, ExistentialVar, UniversalVar, VarIndex, Variable},
        Term,
    },
    grammar::{
        IntoPredicate, IsCopy, IsMoved, Kind, LocalVariableDecl, NamedTy, Parameter, Place,
        Predicate, Program, Ty, TypeName, Var, VarianceKind,
    },
};

use super::in_flight::{InFlight, Transform};

#[derive(Clone, Ord, Eq, PartialEq, PartialOrd, Hash)]
pub struct Env {
    program: Arc<Program>,
    universe: Universe,
    in_scope_vars: Vec<Variable>,
    local_variables: Map<Var, Ty>,
    assumptions: Set<Predicate>,
    fresh: usize,
}

#[term]
#[derive(Copy)]
pub struct Universe(usize);

formality_core::cast_impl!(Env);

impl Env {
    pub fn new(program: impl Upcast<Arc<Program>>) -> Self {
        Env {
            program: program.upcast(),
            universe: Universe(0),
            in_scope_vars: vec![],
            local_variables: Default::default(),
            assumptions: set![],
            fresh: 0,
        }
    }

    pub fn variances(&self, type_name: &TypeName) -> Fallible<Vec<Vec<VarianceKind>>> {
        match type_name {
            TypeName::Tuple(n) => Ok(vec![vec![]; *n]),
            TypeName::Int => Ok(vec![]),
            TypeName::Id(name) => Ok(self.program.class_named(name)?.variances()),
        }
    }

    pub fn add_assumptions(&mut self, assumptions: impl Upcast<Vec<Predicate>>) {
        let assumptions: Vec<Predicate> = assumptions.upcast();
        self.assumptions.extend(assumptions);
    }

    /// Test if we have an assumption that `var` satisfies `p`, where `p` is some predicate
    /// struct (e.g., [`IsCopy`][`crate::grammar::IsCopy`]).
    pub fn is(&self, var: &UniversalVar, p: impl IntoPredicate) -> bool {
        self.assumptions.contains(&p.into_predicate(var))
    }

    pub fn assumptions(&self) -> &Set<Predicate> {
        &self.assumptions
    }

    pub fn program(&self) -> &Program {
        &self.program
    }

    /// True if the given type name is a *class* type (versus a *value* type).
    pub fn is_class_ty(&self, name: &TypeName) -> bool {
        match name {
            TypeName::Tuple(_) => false,
            TypeName::Int => false,
            TypeName::Id(n) => self.program.class_named(n).is_ok(),
        }
    }

    /// True if the given type name is a *value* type (versus a *class* type).
    pub fn is_value_ty(&self, name: &TypeName) -> bool {
        match name {
            TypeName::Tuple(_) => true,
            TypeName::Int => true,
            TypeName::Id(_n) => false,
        }
    }

    /// Allows invoking `push` methods on an `&self` environment;
    /// returns the new environment.
    pub fn with<T>(&self, op: impl FnOnce(&mut Env) -> Fallible<T>) -> Fallible<(Env, T)> {
        let mut env = self.clone();
        let value = op(&mut env)?;
        Ok((env, value))
    }

    pub fn is_copy(&self, p: impl Upcast<Parameter>) -> Fallible<bool> {
        let p: Parameter = p.upcast();
        match p {
            Parameter::Ty(ty) => match ty {
                Ty::NamedTy(named_ty) => self.named_ty_is_copy(&named_ty),
                Ty::Var(Variable::UniversalVar(v)) => Ok(self.is(&v, IsCopy)),
                Ty::Var(Variable::ExistentialVar(_)) | Ty::Var(Variable::BoundVar(_)) => {
                    panic!("unexpected variable: {ty:?}")
                }
                Ty::ApplyPerm(perm, ty) => Ok(self.is_copy(perm)? || self.is_copy(&*ty)?),
                Ty::Or(ty, ty1) => Ok(self.is_copy(&*ty)? || self.is_copy(&*ty1)?),
            },
            Parameter::Perm(perm) => match perm {
                crate::grammar::Perm::My => Ok(false),
                crate::grammar::Perm::Our => Ok(true),
                crate::grammar::Perm::Given(places) => self.any_place_is_copy(&places),
                crate::grammar::Perm::Shared(_) => Ok(true),
                crate::grammar::Perm::Leased(places) => self.any_place_is_copy(&places),
                crate::grammar::Perm::Var(Variable::UniversalVar(v)) => Ok(self.is(&v, IsCopy)),
                crate::grammar::Perm::Var(Variable::ExistentialVar(_))
                | crate::grammar::Perm::Var(Variable::BoundVar(_)) => {
                    panic!("unexpected variable: {perm:?}")
                }
                crate::grammar::Perm::Apply(perm, perm1) => {
                    Ok(self.is_copy(&*perm)? || self.is_copy(&*perm1)?)
                }
                crate::grammar::Perm::Or(perm, perm1) => {
                    Ok(self.is_copy(&*perm)? || self.is_copy(&*perm1)?)
                }
            },
        }
    }

    pub fn named_ty_is_copy(&self, named_ty: &NamedTy) -> Fallible<bool> {
        if self.is_value_ty(&named_ty.name) {
            self.any_is_copy(&named_ty.parameters)
        } else {
            Ok(false)
        }
    }

    fn any_is_copy(&self, p: impl IntoIterator<Item = impl Upcast<Parameter>>) -> Fallible<bool> {
        for p in p {
            if self.is_copy(p)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn any_place_is_copy(&self, places: &Set<Place>) -> Fallible<bool> {
        for place in places {
            if self.is_copy(self.place_ty(place)?)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub fn is_moved(&self, p: impl Upcast<Parameter>) -> Fallible<bool> {
        let p: Parameter = p.upcast();
        match p {
            Parameter::Ty(ty) => match ty {
                Ty::NamedTy(named_ty) => self.named_ty_is_moved(&named_ty),
                Ty::Var(Variable::UniversalVar(v)) => Ok(self.is(&v, IsMoved)),
                Ty::Var(Variable::ExistentialVar(_)) | Ty::Var(Variable::BoundVar(_)) => {
                    panic!("unexpected variable: {ty:?}")
                }
                Ty::ApplyPerm(perm, ty) => Ok(self.is_moved(perm)? && self.is_moved(&*ty)?),
                Ty::Or(ty, ty1) => Ok(self.is_moved(&*ty)? && self.is_moved(&*ty1)?),
            },
            Parameter::Perm(perm) => match perm {
                crate::grammar::Perm::My => Ok(true),
                crate::grammar::Perm::Our => Ok(false),
                crate::grammar::Perm::Given(places) => self.all_places_are_moved(&places),
                crate::grammar::Perm::Shared(_) => Ok(false),
                crate::grammar::Perm::Leased(places) => self.all_places_are_moved(&places),
                crate::grammar::Perm::Var(Variable::UniversalVar(v)) => Ok(self.is(&v, IsMoved)),
                crate::grammar::Perm::Var(Variable::ExistentialVar(_))
                | crate::grammar::Perm::Var(Variable::BoundVar(_)) => {
                    panic!("unexpected variable: {perm:?}")
                }
                crate::grammar::Perm::Apply(perm, perm1) => {
                    Ok(self.is_moved(&*perm)? && self.is_moved(&*perm1)?)
                }
                crate::grammar::Perm::Or(perm, perm1) => {
                    Ok(self.is_moved(&*perm)? || self.is_moved(&*perm1)?)
                }
            },
        }
    }

    fn named_ty_is_moved(&self, named_ty: &NamedTy) -> Fallible<bool> {
        if self.is_value_ty(&named_ty.name) {
            self.all_are_moved(&named_ty.parameters)
        } else {
            Ok(false)
        }
    }

    fn all_are_moved(&self, p: impl IntoIterator<Item = impl Upcast<Parameter>>) -> Fallible<bool> {
        for p in p {
            if !self.is_moved(p)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn all_places_are_moved(&self, places: &Set<Place>) -> Fallible<bool> {
        for place in places {
            if !self.is_moved(self.place_ty(place)?)? {
                return Ok(false);
            }
        }
        Ok(true)
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

            Variable::ExistentialVar(ExistentialVar { .. }) => false,

            Variable::BoundVar(_) => true,
        }
    }

    /// Lookup a program variable named `var` and returns its type (if any).
    pub fn var_ty(&self, var: impl Upcast<Var>) -> Fallible<&Ty> {
        let var: Var = var.upcast();
        match self.local_variables.get(&var) {
            Some(ty) => Ok(ty),
            None => bail!("no variable named `{var:?}`"),
        }
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

    pub fn push_fresh_variable_with_in_flight(&self, ty: impl Upcast<Ty>) -> (Self, Var) {
        let (mut env, var) = self.push_fresh_variable(ty);
        env = env.with_in_flight_stored_to(&var);
        (env, var)
    }

    pub fn push_fresh_variable(&self, ty: impl Upcast<Ty>) -> (Env, Var) {
        let mut env = self.clone();
        let fresh = env.fresh;
        env.push_local_variable(Var::Fresh(fresh), ty).unwrap();
        env.fresh += 1;
        (env, Var::Fresh(fresh))
    }

    pub fn pop_fresh_variable(&self, var: impl Upcast<Var>) -> Env {
        self.pop_fresh_variables(vec![var])
    }

    pub fn pop_fresh_variables(&self, vars: impl Upcast<Vec<Var>>) -> Env {
        let vars: Vec<Var> = vars.upcast();
        let mut env = self.clone();
        for var in vars.into_iter().rev() {
            assert_eq!(var, Var::Fresh(env.fresh - 1));
            env.pop_local_variables(vec![var]).unwrap();
            env.fresh -= 1;
        }
        env
    }

    pub fn pop_local_variables(&mut self, vars: impl Upcast<Vec<Var>>) -> Fallible<()> {
        let vars: Vec<Var> = vars.upcast();
        for var in vars {
            if self.local_variables.remove(&var).is_none() {
                bail!("local variable `{var:?}` not found in environment");
            }
        }

        Ok(())
    }
}

impl InFlight for Env {
    fn with_places_transformed(&self, transform: Transform<'_>) -> Self {
        Env {
            program: self.program.clone(),
            universe: self.universe,
            in_scope_vars: self.in_scope_vars.clone(),
            local_variables: self.local_variables.with_places_transformed(transform),
            assumptions: self.assumptions.with_places_transformed(transform),
            fresh: self.fresh,
        }
    }
}

impl std::fmt::Debug for Env {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Env")
            .field("program", &"...")
            .field("universe", &self.universe)
            .field("in_scope_vars", &self.in_scope_vars)
            .field("local_variables", &self.local_variables)
            .field("assumptions", &self.assumptions)
            .field("fresh", &self.fresh)
            .finish()
    }
}
