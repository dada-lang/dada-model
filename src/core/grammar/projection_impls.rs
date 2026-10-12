use super::Projection;
use crate::dada_lang::FormalityLang;
use formality_core::parse::{
    skip_whitespace, CoreParse, ParseError, ParseResult, Parser, Precedence, Scope,
};

impl CoreParse<FormalityLang> for Projection {
    fn parse<'t>(scope: &Scope<FormalityLang>, text: &'t str) -> ParseResult<'t, Self> {
        Parser::multi_variant(scope, text, "Projection", |parser| {
            parser.parse_variant("Projection::Field", Precedence::default(), |p| {
                // A failed projection must let the enclosing expression parse a call.
                p.set_committed(false);
                p.expect_char('.')?;
                let field = p.nonterminal()?;
                if starts_call_suffix(p.text()) {
                    return Err(ParseError::at(
                        p.text(),
                        "method call starts here".to_owned(),
                    ));
                }
                p.set_committed(true);
                Ok(Projection::Field(field))
            });
            parser.parse_variant("Projection::Index", Precedence::default(), |p| {
                p.set_committed(false);
                p.expect_char('[')?;
                let index = p.nonterminal()?;
                p.expect_char(']')?;
                p.set_committed(true);
                Ok(Projection::Index(index))
            });
        })
    }
}

/// Look ahead without parsing generic arguments: the place grammar is shared by
/// surface and core, but surface generic arguments may contain extra shorthand.
fn starts_call_suffix(mut text: &str) -> bool {
    text = skip_whitespace(text);
    if text.starts_with('(') {
        return true;
    }
    if !text.starts_with('[') {
        return false;
    }
    let mut depth = 0;
    loop {
        text = skip_whitespace(text);
        let Some(ch) = text.chars().next() else {
            return false;
        };
        text = &text[ch.len_utf8()..];
        match ch {
            '[' => depth += 1,
            ']' => {
                depth -= 1;
                if depth == 0 {
                    return skip_whitespace(text).starts_with('(');
                }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::starts_call_suffix;

    #[test]
    fn call_lookahead_handles_nested_brackets_and_comments() {
        for text in [
            "(x)",
            "[given](x)",
            "[Array[shared[x] String], given] (x)",
            "[[] String](x)",
            "[ // ] ignored in comment\n ^] // [ ignored too\n (x)",
        ] {
            assert!(starts_call_suffix(text), "{text}");
        }
        for text in ["", ".field", "[0]", "[0].field", "[Array[Int]"] {
            assert!(!starts_call_suffix(text), "{text}");
        }
    }
}
