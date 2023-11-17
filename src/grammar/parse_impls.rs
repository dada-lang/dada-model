use std::sync::Arc;

use formality_core::parse::{CoreParse, Parser, Precedence};
use formality_core::Upcast;

use crate::dada_lang::FormalityLang;

use super::perm_tree_impls::{PermTreeRoot, PermTreeRootParse};
use super::{ClassName, ClassTy, Kind, Owned, Perm, PermTree, Place, Ty, TyAtom, Variable};

// Customized parse of ty to accept tuples like `()` or `(a, b)` etc.
impl CoreParse<FormalityLang> for TyAtom {
    fn parse<'t>(
        scope: &formality_core::parse::Scope<FormalityLang>,
        text: &'t str,
    ) -> formality_core::parse::ParseResult<'t, Self> {
        Parser::multi_variant(scope, text, "type", |p| {
            p.parse_variant("variable", Precedence::default(), |p| {
                let ty: Ty = p.variable()?;
                Ok(ty)
            });

            p.parse_variant("tuple", Precedence::default(), |p| {
                p.expect_char('(')?;
                let types: Vec<Ty> = p.comma_nonterminal()?;
                p.expect_char(')')?;
                let name = ClassName::Tuple(types.len());
                Ok(ClassTy::new(name, types).upcast())
            });

            p.parse_variant("class", Precedence::default(), |p| {
                p.mark_as_cast_variant();
                p.reject_variable()?;
                let c: ClassTy = p.nonterminal()?;
                Ok(c.upcast())
            });
        })
    }
}

impl<R> CoreParse<FormalityLang> for PermTree<R>
where
    R: PermTreeRoot,
{
    fn parse<'t>(
        scope: &formality_core::parse::Scope<FormalityLang>,
        text: &'t str,
    ) -> formality_core::parse::ParseResult<'t, Self> {
        Parser::multi_variant(scope, text, "perm-tree", |p| {
            p.parse_variant("root", Precedence::default(), |p| p.nonterminal());

            p.parse_variant("shared", Precedence::default(), |p| {
                p.expect_keyword("shared")?;
                let places: Vec<Place> = p.delimited_nonterminal('(', false, ')')?;
                let tree: Arc<Self> = R::parse_subtree(p)?;
                Ok(PermTree::Shared(places, tree))
            });

            p.parse_variant("leased", Precedence::default(), |p| {
                p.expect_keyword("leased")?;
                let places: Vec<Place> = p.delimited_nonterminal('(', false, ')')?;
                let tree: Arc<Self> = R::parse_subtree(p)?;
                Ok(PermTree::Leased(places, tree))
            });

            p.parse_variant("var", Precedence::default(), |p| {
                let v: Variable = p.variable_of_kind(Kind::Perm)?;
                let tree: Arc<Self> = R::parse_subtree(p)?;
                Ok(PermTree::Var(v, tree))
            });
        })
    }
}

impl PermTreeRootParse for Owned {
    fn parse_subtree<'t>(
        p: &mut formality_core::parse::ActiveVariant<'_, 't, FormalityLang>,
    ) -> Result<Arc<PermTree<Self>>, formality_core::Set<formality_core::parse::ParseError<'t>>>
    {
        p.opt_nonterminal()
            .unwrap_or_else(|| Arc::new(Owned.upcast()))
    }
}

impl PermTreeRootParse for TyAtom {
    fn parse_subtree<'t>(
        p: &mut formality_core::parse::ActiveVariant<'_, 't, FormalityLang>,
    ) -> Result<Arc<PermTree<Self>>, formality_core::Set<formality_core::parse::ParseError<'t>>>
    {
        p.nonterminal()
    }
}
