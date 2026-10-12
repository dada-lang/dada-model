use formality_core::parse::{CoreParse, ParseResult, Parser, Scope};

use crate::dada_lang::FormalityLang;

use super::{
    LocalVariableDecl, MethodBody, MethodDeclBoundData, Predicate, ReceiverMethodDeclBoundData,
    ThisDecl, Ty,
};

impl CoreParse<FormalityLang> for ReceiverMethodDeclBoundData {
    fn parse<'t>(scope: &Scope<FormalityLang>, text: &'t str) -> ParseResult<'t, Self> {
        Parser::single_variant(scope, text, "ReceiverMethodDeclBoundData", |parser| {
            let inputs: Vec<LocalVariableDecl> = parser.delimited_nonterminal('(', false, ')')?;

            let output: Ty = if parser.expect_char('-').is_ok() {
                parser.expect_char('>')?;
                parser.nonterminal()?
            } else {
                Ty::unit()
            };

            let predicates: Vec<Predicate> = if let Ok(()) = parser.expect_keyword("where") {
                parser.comma_nonterminal()?
            } else {
                Default::default()
            };

            let body: MethodBody = parser.nonterminal()?;

            Ok(Self::new(inputs, output, predicates, body))
        })
    }
}

impl CoreParse<FormalityLang> for MethodDeclBoundData {
    fn parse<'t>(scope: &Scope<FormalityLang>, text: &'t str) -> ParseResult<'t, Self> {
        Parser::single_variant(scope, text, "MethodDeclBoundData", |parser| {
            parser.expect_char('(')?;
            let this: ThisDecl = parser.nonterminal()?;
            let inputs: Vec<LocalVariableDecl> = if parser.expect_char(',').is_ok() {
                parser.comma_nonterminal()?
            } else {
                vec![]
            };
            parser.expect_char(')')?;

            let output: Ty = if parser.expect_char('-').is_ok() {
                parser.expect_char('>')?;
                parser.nonterminal()?
            } else {
                Ty::unit()
            };

            let predicates: Vec<Predicate> = if let Ok(()) = parser.expect_keyword("where") {
                parser.comma_nonterminal()?
            } else {
                Default::default()
            };

            let body = parser.nonterminal()?;

            Ok(MethodDeclBoundData {
                this,
                inputs,
                output,
                predicates,
                body,
            })
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::core::grammar as core;
    use crate::dada_lang::{term, try_term};
    use crate::surface::{desugar::lower_method, grammar::MethodDecl};

    #[test]
    fn receiver_headers_lower_to_explicit_signatures() {
        crate::assert_desugars!({
            struct Worker {
                fn self.scan() ...;
                fn self!edit[ty T](value: !T) { (); }
                fn self->take[ty T](value: given T) -> given T { return value->; }
            }
        } => {
            struct Worker {
                fn scan[perm Receiver](Receiver self) ...;
                fn edit[ty T, perm Receiver, perm Input](Receiver self, value: Input T)
                    where Receiver is mut, Input is mut { (); }
                fn take[ty T](given self, value: given T) -> given T { return value->; }
            }
        });
    }

    #[test]
    fn header_receiver_preserves_generic_scope_and_generated_suffix_order() {
        crate::assert_desugars!({
            struct Container[ty T, perm P] where T is struct {
                field: P T;
                fn self!edit[ty T, perm P](x: T, y: !T, z: P T) -> P T
                    where P is owned { self!other[T, P](x->, y->, z->); }
                fn self.read[ty U](x: U, y: P T) -> P T ...;
                fn self->take[ty U](x: U) -> P T ...;
            }
        } => {
            struct Container[ty T, perm P] where T is struct {
                field: P T;
                fn edit[ty T, perm P, perm Receiver, perm Y](Receiver self, x: T, y: Y T, z: P T) -> P T
                    where P is owned, Receiver is mut, Y is mut { self!.other[T, P](x->, y->, z->); }
                fn read[ty U, perm Receiver](Receiver self, x: U, y: P T) -> P T ...;
                fn take[ty U](given self, x: U) -> P T ...;
            }
        });
    }

    #[test]
    fn header_methods_accept_trailing_parameters_and_whitespace() {
        for (source, expected) in [
            (
                "fn self // receiver\n . // sigil\n inspect[ty T](value: given T,) -> given T { value->; }",
                "fn self.inspect[ty T](value: given T) -> given T { value->; }",
            ),
            (
                "fn self // receiver\n ! // sigil\n edit[perm P](value: P Data) where P is owned ...;",
                "fn self!edit[perm P](value: P Data) where P is owned ...;",
            ),
            (
                "fn self // receiver\n - // arrow\n > // sigil\n take() {}",
                "fn self->take() {}",
            ),
        ] {
            assert_eq!(term::<MethodDecl>(source), term::<MethodDecl>(expected));
        }
    }

    #[test]
    fn explicit_signatures_remain_valid_alongside_receiver_headers() {
        for source in [
            "fn method[perm P](P self, x: P Data) ...;",
            "fn method(shared self) {}",
            "fn method(given[x] self, x: given Data) ...;",
            "fn method(![x] self, x: given Data) ...;",
        ] {
            let lowered = lower_method(term::<MethodDecl>(source))
                .into_singleton()
                .unwrap()
                .0;
            assert_eq!(lowered, term::<core::MethodDecl>(source));
        }
    }

    #[test]
    fn header_methods_reject_another_receiver_or_misplaced_generics() {
        for source in [
            "fn self.foo(self) {}",
            "fn self.foo(any self) {}",
            "fn self!foo(self!) {}",
            "fn self->foo(self->) {}",
            "fn self->foo(given self) {}",
            "fn self.foo[perm P](P self) {}",
            "fn self!foo(shared self, value: given Data) {}",
            "fn self foo() {}",
            "fn self.!foo() {}",
            "fn self!->foo() {}",
            "fn self->!foo() {}",
            "fn self[perm P].foo() {}",
            "fn self.foo()[perm P] {}",
        ] {
            assert!(try_term::<MethodDecl>(source).is_err(), "accepted {source}");
        }
    }

    #[test]
    fn receiver_headers_are_surface_syntax() {
        for source in [
            "fn self.foo() {}",
            "fn self!foo[ty T](x: !T) ...;",
            "fn self->foo[ty T](x: given T) -> given T { x->; }",
        ] {
            assert!(try_term::<MethodDecl>(source).is_ok(), "rejected {source}");
            assert!(
                try_term::<core::MethodDecl>(source).is_err(),
                "accepted {source}"
            );
        }
    }
}
