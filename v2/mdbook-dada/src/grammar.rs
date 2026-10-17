//! Descriptive data definitions, independent of a proof language or heap semantics.
use crate::escape;
use anyhow::{bail, ensure, Context, Result};
use std::collections::BTreeSet;

#[derive(Debug, PartialEq)]
enum Token {
    Name(String),
    Symbol(char),
    Comment(String),
}

fn tokenize(source: &str) -> Result<Vec<Token>> {
    let mut tokens = Vec::new();
    for (line, text) in source.lines().enumerate() {
        let mut chars = text.chars().peekable();
        while let Some(c) = chars.next() {
            if c.is_whitespace() {
                continue;
            }
            if c == '/' && chars.peek() == Some(&'/') {
                chars.next();
                tokens.push(Token::Comment(chars.collect::<String>().trim().to_owned()));
                break;
            }
            if c.is_alphabetic() || c == '_' {
                let mut name = c.to_string();
                while chars
                    .peek()
                    .is_some_and(|c| c.is_alphanumeric() || *c == '_')
                {
                    name.push(chars.next().context("identifier ended unexpectedly")?);
                }
                tokens.push(Token::Name(name));
            } else {
                ensure!(
                    "<>=|(),:;".contains(c),
                    "grammar line {}: unexpected character `{c}`",
                    line + 1
                );
                tokens.push(Token::Symbol(c));
            }
        }
    }
    Ok(tokens)
}

struct Parser {
    tokens: std::collections::VecDeque<Token>,
}

impl Parser {
    fn symbol(&mut self, c: char) -> bool {
        if self.tokens.front() == Some(&Token::Symbol(c)) {
            self.tokens.pop_front();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, c: char) -> Result<()> {
        ensure!(
            self.symbol(c),
            "expected `{c}`, found {:?}",
            self.tokens.front()
        );
        Ok(())
    }

    fn name(&mut self) -> Result<String> {
        match self.tokens.pop_front() {
            Some(Token::Name(name)) => Ok(name),
            token => bail!("expected an identifier, found {token:?}"),
        }
    }

    fn ty(&mut self) -> Result<String> {
        let mut ty = self.name()?;
        if self.symbol('<') {
            let mut args = vec![self.ty()?];
            while self.symbol(',') {
                args.push(self.ty()?);
            }
            self.expect('>')?;
            ty.push_str(&format!("<{}>", args.join(", ")));
        }
        Ok(ty)
    }

    fn fields(&mut self, end: char) -> Result<Vec<(String, String)>> {
        let mut fields = Vec::new();
        let mut names = BTreeSet::new();
        if self.symbol(end) {
            return Ok(fields);
        }
        loop {
            let name = self.name()?;
            ensure!(names.insert(name.clone()), "duplicate field `{name}`");
            self.expect(':')?;
            fields.push((name, self.ty()?));
            if self.symbol(end) {
                break;
            }
            self.expect(',')?;
            if self.symbol(end) {
                break;
            }
        }
        Ok(fields)
    }
}

fn field_text(fields: &[(String, String)]) -> String {
    fields
        .iter()
        .map(|(n, t)| format!("{n}: {t}"))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Parse complete declarations before rendering; malformed notation fails the book build.
pub fn render(source: &str) -> Result<String> {
    let mut parser = Parser {
        tokens: tokenize(source)?.into(),
    };
    let mut names = BTreeSet::new();
    let mut html = String::from(
        "<div class=\"grammar-definitions\" role=\"group\" aria-label=\"Data definitions\">",
    );
    while !parser.tokens.is_empty() {
        let mut comments = Vec::new();
        while let Some(Token::Comment(_)) = parser.tokens.front() {
            if let Some(Token::Comment(text)) = parser.tokens.pop_front() {
                comments.push(text);
            }
        }
        let name = parser
            .name()
            .context("expected a declaration after any comments")?;
        ensure!(names.insert(name.clone()), "duplicate definition `{name}`");
        let mut heading = name.clone();
        if parser.symbol('<') {
            let mut params = vec![parser.name()?];
            while parser.symbol(',') {
                let param = parser.name()?;
                ensure!(!params.contains(&param), "duplicate parameter `{param}`");
                params.push(param);
            }
            parser.expect('>')?;
            heading.push_str(&format!("<{}>", params.join(", ")));
        }
        parser.expect('=')?;
        for comment in comments {
            html.push_str(&format!(
                "<div class=\"grammar-comment\">// {}</div>",
                escape(&comment)
            ));
        }
        let mut alternatives = Vec::new();
        let mut variants = BTreeSet::new();
        loop {
            let variant = parser.name()?;
            ensure!(
                variants.insert(variant.clone()),
                "duplicate variant `{variant}`"
            );
            let text = if parser.symbol('(') {
                format!("{variant}({})", field_text(&parser.fields(')')?))
            } else {
                variant
            };
            alternatives.push(text);
            if !parser.symbol('|') {
                break;
            }
        }
        html.push_str(&format!("<div class=\"grammar-definition\"><code class=\"grammar-name\">{}</code><span class=\"grammar-equals\">=</span><div class=\"grammar-body\">", escape(&heading)));
        for (i, alternative) in alternatives.iter().enumerate() {
            let separator = if i == 0 { "" } else { "| " };
            html.push_str(&format!(
                "<div><code>{separator}{}</code></div>",
                escape(alternative)
            ));
        }
        parser
            .expect(';')
            .with_context(|| format!("definition {name}"))?;
        html.push_str("</div></div>");
    }
    ensure!(!names.is_empty(), "grammar block must contain a definition");
    html.push_str(&format!(
        "<details><summary>Definition source</summary><pre><code>{}</code></pre></details></div>",
        escape(source).replace('\n', "&#10;")
    ));
    Ok(html)
}

#[cfg(test)]
mod tests {
    use super::render;

    // Covers meta.syntax.grammar.declarations, .types, .comments, .rendering.
    #[test]
    fn constructors_nested_types_and_comments() {
        let source = "// Opaque <payload> & documentation\nObject<P> = Primitive(value: P) | Array(elements: Sequence<Slot>);\nState<P> = State(objects: Map<Id, Object<P>>,);";
        let html = render(source).unwrap();
        assert!(html.contains("Map&lt;Id, Object&lt;P&gt;&gt;"));
        assert!(html.contains("Opaque &lt;payload&gt; &amp; documentation"));
        assert!(html.contains("grammar-comment"));
        assert!(html.contains("Definition source"));
    }

    // Covers meta.syntax.grammar.validation and .comments.
    #[test]
    fn rejects_malformed_and_ambiguous_definitions() {
        for source in [
            "",
            "A = V",
            "A = V; A = W;",
            "A<T,T> = V;",
            "A = V | V;",
            "A = V(x: X, x: Y);",
            "A = V(x: Map<X,>);",
            "A = { x: X };",
            "A = V(x);",
            "A = V; garbage",
            "// orphan",
            "A = V(// misplaced\nx: X);",
            "A = V; @",
        ] {
            assert!(render(source).is_err(), "accepted {source}");
        }
    }
}
