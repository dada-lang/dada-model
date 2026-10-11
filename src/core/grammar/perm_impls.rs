use super::{Kind, Parameter, Perm, Place, Ty};
use crate::dada_lang::FormalityLang;
use formality_core::parse::{CoreParse, ParseError, ParseResult, Parser, Precedence, Scope};
use formality_core::{cast_impl, Cons, DowncastFrom, Set, Upcast, UpcastFrom};
use std::sync::Arc;

// Parse each permission prefix in one branch. Separate `^` and `^[...]`
// alternatives let formality-core select the shorter prefix prematurely.
impl CoreParse<FormalityLang> for Perm {
    fn parse<'t>(scope: &Scope<FormalityLang>, text: &'t str) -> ParseResult<'t, Self> {
        Parser::multi_variant(scope, text, "Perm", |parser| {
            parser.parse_variant("Perm::GivenOrMoved", Precedence::default(), |p| {
                p.expect_char('^')?;
                let origins: Set<Place> = p.delimited_nonterminal('[', true, ']')?;
                Ok(if origins.is_empty() {
                    Perm::Given
                } else {
                    Perm::Mv(origins)
                })
            });
            parser.parse_variant("Perm::Shared", Precedence::default(), |p| {
                p.expect_keyword("shared")?;
                Ok(Perm::share_from(
                    p.delimited_nonterminal::<Place, Set<Place>>('[', true, ']')?,
                ))
            });
            parser.parse_variant("Perm::Mt", Precedence::default(), |p| {
                p.expect_char('!')?;
                let origins: Set<Place> = p.delimited_nonterminal('[', false, ']')?;
                if origins.is_empty() {
                    return Err(ParseError::at(
                        text,
                        "mutable permissions require at least one origin".into(),
                    ));
                }
                Ok(Perm::Mt(origins))
            });
            parser.parse_variant_variable("Perm::Var", Precedence::default(), Kind::Perm);
            parser.parse_variant("Perm::Apply", Precedence::default(), |p| {
                Ok(Perm::Apply(p.nonterminal()?, p.nonterminal()?))
            });
            parser.parse_variant("Perm::Or", Precedence::default(), |p| {
                p.expect_keyword("or")?;
                Ok(Perm::Or(p.delimited_nonterminal('(', false, ')')?))
            });
        })
    }
}

impl Perm {
    /// Share independently when there are no origins; otherwise share places.
    pub fn share_from(places: impl Upcast<Set<Place>>) -> Self {
        let places = places.upcast();
        if places.is_empty() {
            Self::Shared
        } else {
            Self::SharedFrom(places)
        }
    }

    pub fn apply_to_parameter(&self, p: &Parameter) -> Parameter {
        match p {
            Parameter::Ty(ty) => Ty::apply_perm(self, ty).upcast(),
            Parameter::Perm(perm) => Perm::apply(self, perm).upcast(),
        }
    }

    /// Returns a new permission that is the conjunction of this permission and the given
    /// permission.
    pub fn apply_to(&self, perm: impl Upcast<Arc<Perm>>) -> Perm {
        Perm::apply(self, perm)
    }
}

/// "LeafPerms"
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct LeafPerms {
    leaves: Vec<Perm>,
}

cast_impl!(LeafPerms);
cast_impl!((LeafPerms) <: (Perm) <: (Parameter));

impl IntoIterator for LeafPerms {
    type Item = Perm;
    type IntoIter = std::vec::IntoIter<Perm>;

    fn into_iter(self) -> Self::IntoIter {
        self.leaves.into_iter()
    }
}

impl Perm {
    /// Create a Perm from an iterator of leaves.
    /// It has the shape `Apply(leaf, Apply(leaf, ...))`
    fn from_leaves(leaves: impl DoubleEndedIterator<Item = Perm>) -> Self {
        let mut leaves = leaves.into_iter().rev();
        let Some(leaf_n) = leaves.next() else {
            return Perm::Given;
        };
        leaves.fold(leaf_n.upcast(), |n_1, n_0| Perm::apply(n_0, n_1))
    }

    fn push_leaves(&self, output: &mut Vec<Perm>) {
        match self {
            Perm::Given => (),
            Perm::Shared
            | Perm::Mv(_)
            | Perm::SharedFrom(_)
            | Perm::Mt(_)
            | Perm::Var(_)
            | Perm::Or(_) => output.push(self.clone()),
            Perm::Apply(perm, perm1) => {
                perm.push_leaves(output);
                perm1.push_leaves(output);
            }
        }
    }
}

impl UpcastFrom<Perm> for LeafPerms {
    fn upcast_from(t: Perm) -> Self {
        let mut leaves = vec![];
        t.push_leaves(&mut leaves);
        LeafPerms { leaves }
    }
}

impl DowncastFrom<Perm> for LeafPerms {
    fn downcast_from(p: &Perm) -> Option<Self> {
        Some(p.upcast())
    }
}

impl UpcastFrom<LeafPerms> for Perm {
    fn upcast_from(t: LeafPerms) -> Self {
        Perm::from_leaves(t.leaves.into_iter())
    }
}

impl DowncastFrom<LeafPerms> for Perm {
    fn downcast_from(p: &LeafPerms) -> Option<Self> {
        Some(Perm::from_leaves(p.leaves.iter().cloned()))
    }
}

impl<C: PermCar> DowncastFrom<LeafPerms> for Cons<C, Perm> {
    fn downcast_from(perm: &LeafPerms) -> Option<Self> {
        let mut leaves = perm.leaves.iter().cloned();
        let array = C::take(&mut leaves)?;
        Some(Cons(array, Perm::from_leaves(leaves)))
    }
}

impl<C: PermCar, D: Upcast<LeafPerms>> UpcastFrom<Cons<C, D>> for LeafPerms {
    fn upcast_from(term: Cons<C, D>) -> Self {
        let Cons(car, cdr) = term;
        let cdr: LeafPerms = cdr.upcast();
        let mut leaves = vec![];
        leaves.extend(car.into_perms());
        leaves.extend(cdr.leaves);
        LeafPerms { leaves }
    }
}

trait PermCar: Sized + Clone {
    fn take(leaves: &mut impl Iterator<Item = Perm>) -> Option<Self>;
    fn into_perms(self) -> impl IntoIterator<Item = Perm>;
}

impl PermCar for Perm {
    fn take(leaves: &mut impl Iterator<Item = Perm>) -> Option<Self> {
        leaves.next()
    }

    fn into_perms(self) -> impl IntoIterator<Item = Perm> {
        Some(self)
    }
}

impl PermCar for (Perm, Perm) {
    fn take(leaves: &mut impl Iterator<Item = Perm>) -> Option<Self> {
        let car = leaves.next()?;
        let cdr = leaves.next()?;
        Some((car, cdr))
    }

    fn into_perms(self) -> impl IntoIterator<Item = Perm> {
        [self.0, self.1]
    }
}

#[cfg(test)]
mod parse_tests {
    use super::*;
    use crate::dada_lang::{term, try_term};

    #[test]
    fn independent_ownership_accepts_empty_origins() {
        assert_eq!(term::<Perm>("^"), Perm::Given);
        assert_eq!(term::<Perm>("^[]"), Perm::Given);
        assert_eq!(term::<Perm>("^ [ ]"), Perm::Given);
        assert_eq!(format!("{:?}", term::<Perm>("^[]")), "^");
    }

    #[test]
    fn moved_ownership_preserves_projected_origins() {
        let origins = [term::<Place>("x.field"), term::<Place>("self")]
            .into_iter()
            .collect();
        assert_eq!(term::<Perm>("^[x.field, self]"), Perm::Mv(origins));
    }

    #[test]
    fn ownership_sigils_compose_and_form_disjunctions() {
        let moved = term::<Perm>("^[x]");
        assert_eq!(
            term::<Perm>("^[x] shared"),
            Perm::Apply(Arc::new(moved.clone()), Arc::new(Perm::Shared)),
        );
        assert_eq!(
            term::<Perm>("or(^, ^[x])"),
            Perm::Or([Perm::Given, moved].into_iter().collect()),
        );
        assert_eq!(term::<Perm>("^[] shared[x]"), term::<Perm>("^ shared[x]"));
    }

    #[test]
    fn ownership_permission_old_spellings_and_malformed_origins_are_rejected() {
        for text in ["given", "given_from[x]", "^[", "^[x", "^[x,,y]"] {
            assert!(try_term::<Perm>(text).is_err(), "accepted {text:?}");
        }
    }
}

#[cfg(test)]
mod mutable_parse_tests {
    use super::*;
    #[test]
    fn mutable_permission_requires_an_origin() {
        assert_eq!(
            crate::dada_lang::term::<Perm>("![x]"),
            Perm::Mt([crate::dada_lang::term::<Place>("x")].into_iter().collect())
        );
        for text in ["![]", "!", "mut[x]"] {
            assert!(
                crate::dada_lang::try_term::<Perm>(text).is_err(),
                "accepted {text}"
            );
        }
    }
}

#[cfg(test)]
mod sharing_parse_tests {
    use super::*;
    #[test]
    fn empty_sharing_origins_are_independent() {
        for text in ["shared", "shared[]", "shared [ ]"] {
            assert_eq!(crate::dada_lang::term::<Perm>(text), Perm::Shared);
        }
        assert_eq!(Perm::share_from(Set::<Place>::new()), Perm::Shared);
        assert!(matches!(
            crate::dada_lang::term::<Perm>("shared[x]"),
            Perm::SharedFrom(_)
        ));
        assert!(crate::dada_lang::try_term::<Perm>("ref[x]").is_err());
    }
}
