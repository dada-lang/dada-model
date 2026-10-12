use std::fmt::{self, Debug};

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

            let output: Ty = if parser.expect_char('→').is_ok() {
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

            let output: Ty = if parser.expect_char('→').is_ok() {
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

impl Debug for MethodDeclBoundData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            return f
                .debug_struct("MethodDeclBoundData")
                .field("this", &self.this)
                .field("inputs", &self.inputs)
                .field("output", &self.output)
                .field("predicates", &self.predicates)
                .field("body", &self.body)
                .finish();
        }
        write!(f, "({:?}", self.this)?;
        // Preserve the existing diagnostic layout; source::program supplies the
        // explicit comma after the receiver when rendering parsable source.
        for (index, input) in self.inputs.iter().enumerate() {
            write!(f, "{}{:?}", if index == 0 { " " } else { ", " }, input)?;
        }
        write!(f, ") → {:?}", self.output)?;
        for (index, predicate) in self.predicates.iter().enumerate() {
            write!(
                f,
                "{}{:?}",
                if index == 0 { " where " } else { ", " },
                predicate
            )?;
        }
        write!(f, " {:?}", self.body)
    }
}

impl Debug for ReceiverMethodDeclBoundData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            return f
                .debug_struct("ReceiverMethodDeclBoundData")
                .field("inputs", &self.inputs)
                .field("output", &self.output)
                .field("predicates", &self.predicates)
                .field("body", &self.body)
                .finish();
        }
        write!(f, "(")?;
        for (index, input) in self.inputs.iter().enumerate() {
            write!(f, "{}{:?}", if index == 0 { "" } else { ", " }, input)?;
        }
        write!(f, ") → {:?}", self.output)?;
        for (index, predicate) in self.predicates.iter().enumerate() {
            write!(
                f,
                "{}{:?}",
                if index == 0 { " where " } else { ", " },
                predicate
            )?;
        }
        write!(f, " {:?}", self.body)
    }
}

#[cfg(test)]
mod tests {
    use crate::core::grammar as core;
    use crate::dada_lang::{term, try_term};
    use crate::surface::{desugar::lower_method, grammar::MethodDecl};

    #[test]
    fn receiver_headers_lower_to_explicit_signatures() {
        crate::assert_desugars!(r#"
            struct Worker {
                fn self.scan() ...;
                fn self!edit[type T](value: !T) { (); }
                fn self→take[type T](value: given T) → given T { return value→; }
            }
        "# => r#"
            struct Worker {
                fn scan[perm Receiver](Receiver self) ...;
                fn edit[type T, perm Receiver, perm Input](Receiver self, value: Input T)
                    where Receiver is mut, Input is mut { (); }
                fn take[type T](given self, value: given T) → given T { return value→; }
            }
        "#);
    }

    #[test]
    fn header_receiver_preserves_generic_scope_and_generated_suffix_order() {
        crate::assert_desugars!(r#"
            struct Container[type T, perm P] where T is struct {
                field: P T;
                fn self!edit[type T, perm P](x: T, y: !T, z: P T) → P T
                    where P is owned { self!other[T, P](x→, y→, z→); }
                fn self.read[type U](x: U, y: P T) → P T ...;
                fn self→take[type U](x: U) → P T ...;
            }
        "# => r#"
            struct Container[type T, perm P] where T is struct {
                field: P T;
                fn edit[type T, perm P, perm Receiver, perm Y](Receiver self, x: T, y: Y T, z: P T) → P T
                    where P is owned, Receiver is mut, Y is mut { self!.other[T, P](x→, y→, z→); }
                fn read[type U, perm Receiver](Receiver self, x: U, y: P T) → P T ...;
                fn take[type U](given self, x: U) → P T ...;
            }
        "#);
    }

    #[test]
    fn header_methods_accept_trailing_parameters_and_whitespace() {
        for (source, expected) in [
            (
                "fn self // receiver\n . // sigil\n inspect[type T](value: given T,) → given T { value→; }",
                "fn self.inspect[type T](value: given T) → given T { value→; }",
            ),
            (
                "fn self // receiver\n ! // sigil\n edit[perm P](value: P Data) where P is owned ...;",
                "fn self!edit[perm P](value: P Data) where P is owned ...;",
            ),
            (
                "fn self // receiver\n → // sigil\n take() {}",
                "fn self→take() {}",
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
            "fn self→foo(self→) {}",
            "fn self→foo(given self) {}",
            "fn self.foo[perm P](P self) {}",
            "fn self!foo(shared self, value: given Data) {}",
            "fn self foo() {}",
            "fn self.!foo() {}",
            "fn self!→foo() {}",
            "fn self→!foo() {}",
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
            "fn self!foo[type T](x: !T) ...;",
            "fn self→foo[type T](x: given T) → given T { x→; }",
        ] {
            assert!(try_term::<MethodDecl>(source).is_ok(), "rejected {source}");
            assert!(
                try_term::<core::MethodDecl>(source).is_err(),
                "accepted {source}"
            );
        }
    }
}
