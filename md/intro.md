# Dada Formal Model

This book documents the formal model for the [Dada](https://dada-lang.org/) programming language.
The model is implemented in Rust using [formality-core](https://rust-lang.github.io/a-mir-formality/formality_core.html)
and defines Dada's type system, including its permission-based ownership model.

The code examples in this book are **executable tests** --
they are compiled and checked as part of the build.
When you see a Dada program in this book, it has been verified by the model.

Throughout the book, we will also reference the formal rules from the model's source code using anchors like `ClassDecl`.
