# Dada Formal Model

This book documents the formal model for the [Dada](https://dada-lang.org/) programming language.
The model is implemented in Rust using [formality-core](https://rust-lang.github.io/a-mir-formality/formality_core.html)
and defines Dada's type system, including its permission-based ownership model.

The code examples in this book are extracted from **executable tests**.
`cargo test --all --workspace` checks their expected outcomes, including programs
that should be rejected. Interpreter-only tests deliberately bypass type checking.
The book build extracts examples and formal rules; it does not run the tests.

Throughout the book, we will also reference the formal rules from the model's source code using anchors like `ClassDecl`.
