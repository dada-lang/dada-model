use std::sync::Arc;

use formality_core::{
    fold::CoreFold,
    parse::{CoreParse, Parser, Precedence},
    Downcast,
};

use crate::dada_lang::FormalityLang;

use super::{Kind, Perm, Place, Variable};

impl CoreFold<FormalityLang> for Perm {
    fn substitute(
        &self,
        substitution_fn: formality_core::fold::SubstitutionFn<'_, FormalityLang>,
    ) -> Self {
        match self {
            Perm::Owned => Perm::Owned,
            Perm::Shared(places, tree) => Perm::Shared(
                places.substitute(substitution_fn),
                tree.substitute(substitution_fn),
            ),
            Perm::Leased(places, tree) => Perm::Leased(
                places.substitute(substitution_fn),
                tree.substitute(substitution_fn),
            ),
            Perm::Var(var, tree) => {
                let tree = Perm::substitute(tree, substitution_fn);
                if let Some(p) = substitution_fn(*var) {
                    let var_tree: Perm = p.downcast().expect("ill-kinded substitution");
                    var_tree.rebase(tree)
                } else {
                    Perm::Var(*var, Arc::new(tree))
                }
            }
        }
    }
}

impl Perm {
    /// Return a new perm equivalent to `self` but with the "owned" at the root of self
    /// replaced by `root`.
    pub fn rebase(&self, root: Perm) -> Perm {
        match self {
            Perm::Owned => root,
            Perm::Shared(places, subtree) => Perm::shared(places, subtree.rebase(root)),
            Perm::Leased(places, subtree) => Perm::leased(places, subtree.rebase(root)),
            Perm::Var(var, subtree) => Perm::var(var, subtree.rebase(root)),
        }
    }

    pub fn is_owned(&self) -> bool {
        match self {
            Perm::Owned => true,
            _ => false,
        }
    }
}

impl CoreParse<FormalityLang> for Perm {
    fn parse<'t>(
        scope: &formality_core::parse::Scope<FormalityLang>,
        text: &'t str,
    ) -> formality_core::parse::ParseResult<'t, Self> {
        Parser::multi_variant(scope, text, "permission", |p| {
            p.parse_variant("owned", Precedence::default(), |p| {
                p.expect_keyword("owned")?;
                Ok(Perm::Owned)
            });

            p.parse_variant("shared", Precedence::default(), |p| {
                p.expect_keyword("shared")?;
                let places: Vec<Place> = p.delimited_nonterminal('(', true, ')')?;
                let tree: Arc<Self> = p.opt_nonterminal()?.unwrap_or_default();
                Ok(Perm::Shared(places, tree))
            });

            p.parse_variant("leased", Precedence::default(), |p| {
                p.expect_keyword("leased")?;
                let places: Vec<Place> = p.delimited_nonterminal('(', false, ')')?;
                let tree: Arc<Self> = p.opt_nonterminal()?.unwrap_or_default();
                Ok(Perm::Leased(places, tree))
            });

            p.parse_variant("var", Precedence::default(), |p| {
                let v: Variable = p.variable_of_kind(Kind::Perm)?;
                let tree: Arc<Self> = p.opt_nonterminal()?.unwrap_or_default();
                Ok(Perm::Var(v, tree))
            });
        })
    }
}
