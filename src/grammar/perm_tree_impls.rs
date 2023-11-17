use std::sync::Arc;

use formality_core::{
    fold::CoreFold,
    parse::{ActiveVariant, ParseError},
    term::CoreTerm,
    visit::CoreVisit,
    Downcast, DowncastTo, Set, UpcastFrom,
};

use super::{Owned, Perm, PermTree, TyAtom};
use crate::dada_lang::{FormalityLang, Term};

pub trait PermTreeRoot: Term + PermTreeRootParse {}

pub trait PermTreeRootParse: Sized {
    fn parse_subtree<'t>(
        p: &mut ActiveVariant<'_, 't, FormalityLang>,
    ) -> Result<Arc<PermTree<Self>>, Set<ParseError<'t>>>
    where
        Self: PermTreeRoot;
}

impl<R> CoreFold<FormalityLang> for PermTree<R>
where
    R: PermTreeRoot,
{
    fn substitute(
        &self,
        substitution_fn: formality_core::fold::SubstitutionFn<'_, FormalityLang>,
    ) -> Self {
        match self {
            PermTree::Root(root) => PermTree::Root(root.substitute(substitution_fn)),
            PermTree::Shared(places, tree) => PermTree::Shared(
                places.substitute(substitution_fn),
                tree.substitute(substitution_fn),
            ),
            PermTree::Leased(places, tree) => PermTree::Leased(
                places.substitute(substitution_fn),
                tree.substitute(substitution_fn),
            ),
            PermTree::Var(var, tree) => {
                let tree = PermTree::substitute(tree, substitution_fn);
                if let Some(p) = substitution_fn(*var) {
                    let var_tree: Perm = p.downcast().expect("ill-kinded substitution");
                    var_tree.tree.rebase(tree)
                } else {
                    PermTree::Var(*var, Arc::new(tree))
                }
            }
        }
    }
}

impl<R> CoreVisit<FormalityLang> for PermTree<R>
where
    R: PermTreeRoot,
{
    fn free_variables(&self) -> Vec<formality_core::variable::CoreVariable<FormalityLang>> {
        todo!()
    }

    fn size(&self) -> usize {
        todo!()
    }

    fn assert_valid(&self) {
        todo!()
    }
}

impl<R> DowncastTo<PermTree<R>> for PermTree<R>
where
    R: PermTreeRoot,
{
    fn downcast_to(&self) -> Option<PermTree<R>> {
        Some(self.clone())
    }
}

impl<R> UpcastFrom<PermTree<R>> for PermTree<R>
where
    R: PermTreeRoot,
{
    fn upcast_from(term: PermTree<R>) -> Self {
        term
    }
}

impl<R> CoreTerm<FormalityLang> for PermTree<R> where R: PermTreeRoot {}

impl PermTree<Owned> {
    pub fn rebase<R>(self, root: PermTree<R>) -> PermTree<R>
    where
        R: PermTreeRoot,
    {
        match self {
            PermTree::Root(Owned) => root,
            PermTree::Shared(places, subtree) => {
                PermTree::Shared(places, Arc::new(subtree.rebase(root)))
            }
            PermTree::Leased(places, subtree) => {
                PermTree::Leased(places, Arc::new(subtree.rebase(root)))
            }
            PermTree::Var(var, subtree) => PermTree::Var(var, Arc::new(subtree.rebase(root))),
        }
    }
}

impl UpcastFrom<Owned> for PermTree<Owned> {
    fn upcast_from(term: Owned) -> Self {
        PermTree::Root(term)
    }
}

impl UpcastFrom<TyAtom> for PermTree<TyAtom> {
    fn upcast_from(term: TyAtom) -> Self {
        PermTree::Root(term)
    }
}

impl PermTreeRoot for Owned {}

impl PermTreeRoot for TyAtom {}
