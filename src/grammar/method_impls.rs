use formality_core::parse::{
    ActiveVariant, CoreParse, ParseResult, ParseSuccessType, Parser, Scope,
};

use crate::dada_lang::FormalityLang;

use super::{LocalVariableDecl, MethodDeclBoundData, Predicate, ThisDecl, Ty};

fn each_parse_inputs<'s, 't, R: ParseSuccessType>(
    p: &mut ActiveVariant<'s, 't, FormalityLang>,
    op: impl Fn(
        Vec<LocalVariableDecl>,
        &mut ActiveVariant<'s, 't, FormalityLang>,
    ) -> ParseResult<'t, R>,
) -> ParseResult<'t, R> {
    if p.expect_char(',').is_ok() {
        p.each_comma_nonterminal(|inputs: Vec<LocalVariableDecl>, p| op(inputs, p))
    } else {
        op(vec![], p)
    }
}

fn each_parse_output<'s, 't, R: ParseSuccessType>(
    p: &mut ActiveVariant<'s, 't, FormalityLang>,
    op: impl Fn(Ty, &mut ActiveVariant<'s, 't, FormalityLang>) -> ParseResult<'t, R>,
) -> ParseResult<'t, R> {
    if p.expect_char('-').is_ok() {
        p.expect_char('>')?;
        p.each_nonterminal(|output: Ty, p| op(output, p))
    } else {
        op(Ty::unit(), p)
    }
}

fn each_parse_predicates<'s, 't, R: ParseSuccessType>(
    p: &mut ActiveVariant<'s, 't, FormalityLang>,
    op: impl Fn(Vec<Predicate>, &mut ActiveVariant<'s, 't, FormalityLang>) -> ParseResult<'t, R>,
) -> ParseResult<'t, R> {
    if p.expect_keyword("where").is_ok() {
        p.each_comma_nonterminal(|predicates: Vec<Predicate>, p| op(predicates, p))
    } else {
        op(vec![], p)
    }
}

impl CoreParse<FormalityLang> for MethodDeclBoundData {
    fn parse<'t>(scope: &Scope<FormalityLang>, text: &'t str) -> ParseResult<'t, Self> {
        Parser::single_variant(scope, text, "MethodDeclBoundData", |p| {
            p.expect_char('(')?;
            p.each_nonterminal(|this: ThisDecl, p| {
                each_parse_inputs(p, |inputs, p| {
                    p.expect_char(')')?;
                    each_parse_output(p, |output, p| {
                        each_parse_predicates(p, |predicates, p| {
                            let this = this.clone();
                            let inputs = inputs.clone();
                            let output = output.clone();
                            let predicates = predicates.clone();
                            p.each_nonterminal(|body, p| {
                                p.ok(MethodDeclBoundData {
                                    this: this.clone(),
                                    inputs: inputs.clone(),
                                    output: output.clone(),
                                    predicates: predicates.clone(),
                                    body,
                                })
                            })
                        })
                    })
                })
            })
        })
    }
}
