//! We do something really dumb and brute force to manage liveness.
//! Basically, in between every statement, we have the option of making
//! initialized variables be considered moved. Note that this could cause
//! type check errors later on if that variable is used again. In "real life"
//! we would use a liveness check to detect that possibility, but to keep
//! these rules simple, we let the judgments just explore all possibilities.

use std::sync::Arc;

use formality_core::{cast_impl, Set, SetExt, Upcast};

use crate::grammar::{Block, Expr, Place, PlaceExpr, Statement, Var};

/// Tracks the set of live variables at a given point in execution.
/// The `Default` impl returns an empty set.
#[derive(Clone, Default, Debug, Ord, Eq, PartialEq, PartialOrd, Hash)]
pub struct LivePlaces {
    /// A place `p` is read if it is read from or accessed (e.g., `p.share`)
    accessed: Set<Place>,

    /// A place `p` is traversed if some subpart of it is assigned to (e.g., `p.f = q`)
    traversed: Set<Place>,
}

cast_impl!(LivePlaces);

impl LivePlaces {
    /// True if `v` is live -- i.e., it or some part of it may be accessed after this point.
    pub fn is_live(&self, place: impl Upcast<Place>) -> bool {
        let place: Place = place.upcast();
        self.accessed.iter().any(|p| p.is_overlapping_with(&place))
            || self.traversed.iter().any(|p| place.is_prefix_of(&p))
    }

    /// True if `v` is live -- i.e., it or some part of it may be accessed after this point.
    pub fn any_live(&self, places: impl Upcast<Set<Place>>) -> bool {
        let places: Set<Place> = places.upcast();
        places.iter().all(|place| self.is_live(place))
    }

    /// Compute a new set of live-vars just before `term` has been evaluated.
    pub fn before(&self, term: &impl AdjustLiveVars) -> Self {
        term.adjust_live_vars(self.clone())
    }

    /// Compute a new set of live-vars just before `terms` have been evaluated.
    pub fn before_all(&self, terms: impl IntoIterator<Item = impl AdjustLiveVars>) -> Self {
        terms
            .into_iter()
            .fold(Self::default(), |live_places, term| {
                live_places.union(term.adjust_live_vars(self.clone()))
            })
    }

    /// Compute a new set of live-vars that doesn't include var
    pub fn overwritten(mut self, place: impl Upcast<Place>) -> Self {
        let place: Place = place.upcast();
        self.accessed.retain(|p| !place.is_prefix_of(p));
        self.traversed.retain(|p| !place.is_prefix_of(p));
        if let Some(owner) = place.owner() {
            self.traversed.insert(owner);
        }
        self
    }

    pub fn accessed(mut self, place: impl Upcast<Place>) -> Self {
        let place: Place = place.upcast();
        self.accessed.insert(place);
        self
    }

    pub fn union(self, other: LivePlaces) -> Self {
        let accessed = self.accessed.union_with(other.accessed);
        let traversed = self.traversed.union_with(other.traversed);
        Self {
            accessed,
            traversed,
        }
    }

    pub fn vars(&self) -> Set<&Var> {
        self.accessed
            .iter()
            .chain(&self.traversed)
            .map(|place| &place.var)
            .collect()
    }
}

pub trait AdjustLiveVars: std::fmt::Debug {
    fn adjust_live_vars(&self, vars: LivePlaces) -> LivePlaces;
}

impl<T: AdjustLiveVars> AdjustLiveVars for &T {
    fn adjust_live_vars(&self, vars: LivePlaces) -> LivePlaces {
        T::adjust_live_vars(self, vars)
    }
}

impl<T: AdjustLiveVars> AdjustLiveVars for Arc<T> {
    fn adjust_live_vars(&self, vars: LivePlaces) -> LivePlaces {
        T::adjust_live_vars(self, vars)
    }
}

impl AdjustLiveVars for Vec<Statement> {
    fn adjust_live_vars(&self, vars: LivePlaces) -> LivePlaces {
        self.iter()
            .rev()
            .fold(vars, |vars, stmt| stmt.adjust_live_vars(vars))
    }
}

impl AdjustLiveVars for Statement {
    fn adjust_live_vars(&self, live: LivePlaces) -> LivePlaces {
        match self {
            Statement::Expr(expr) => expr.adjust_live_vars(live),
            Statement::Let(var, _ty, expr) => expr.adjust_live_vars(live.overwritten(var)),
            Statement::Reassign(place, expr) => {
                // x.f.g will be assigned...
                let live = live.overwritten(place);

                // ...and computing the expression
                expr.adjust_live_vars(live)
            }
            Statement::Loop(expr) => expr.adjust_live_vars(live),
            Statement::Break => live,
            Statement::Return(expr) => expr.adjust_live_vars(live),
        }
    }
}

impl AdjustLiveVars for Vec<Expr> {
    fn adjust_live_vars(&self, vars: LivePlaces) -> LivePlaces {
        self.iter()
            .rev()
            .fold(vars, |vars, expr| expr.adjust_live_vars(vars))
    }
}

impl AdjustLiveVars for Expr {
    fn adjust_live_vars(&self, vars: LivePlaces) -> LivePlaces {
        match self {
            Expr::Block(block) => block.adjust_live_vars(vars),
            Expr::Integer(_) => vars,
            Expr::Add(lhs, rhs) => {
                let vars = rhs.adjust_live_vars(vars);
                lhs.adjust_live_vars(vars)
            }
            Expr::Place(place) => place.adjust_live_vars(vars),
            Expr::Tuple(exprs) => exprs.adjust_live_vars(vars),
            Expr::Call(func, _method_name, _parameters, args) => {
                let vars = args.adjust_live_vars(vars);
                func.adjust_live_vars(vars)
            }
            Expr::New(_ty, _parameters, args) => args.adjust_live_vars(vars),
            Expr::Clear(_) => vars,
            Expr::If(cond, if_true, if_false) => {
                let if_true_vars = if_true.adjust_live_vars(vars.clone());
                let if_false_vars = if_false.adjust_live_vars(vars);
                cond.adjust_live_vars(if_true_vars.union(if_false_vars))
            }
            Expr::Panic => vars,
        }
    }
}

impl AdjustLiveVars for Block {
    fn adjust_live_vars(&self, vars: LivePlaces) -> LivePlaces {
        let Block { statements } = self;
        statements.adjust_live_vars(vars)
    }
}

impl AdjustLiveVars for PlaceExpr {
    fn adjust_live_vars(&self, vars: LivePlaces) -> LivePlaces {
        self.place.adjust_live_vars(vars)
    }
}

impl AdjustLiveVars for Set<Place> {
    fn adjust_live_vars(&self, vars: LivePlaces) -> LivePlaces {
        self.iter()
            .fold(vars, |vars, place| place.adjust_live_vars(vars))
    }
}

impl AdjustLiveVars for Place {
    fn adjust_live_vars(&self, vars: LivePlaces) -> LivePlaces {
        vars.accessed(self)
    }
}
