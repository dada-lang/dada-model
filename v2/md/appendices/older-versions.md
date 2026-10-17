# Older versions of the semantics

This book is the current v2 exploration of Dada's semantics. Earlier versions
remain available as references while we explore new approaches to describing and
checking the language.

## v1: Rust and a-mir-formality

[Read the v1 semantics book](../../v1/index.html).

The original model implements Dada's type system and interpreter in Rust, using
`formality-core` from `a-mir-formality` to express syntax and inference rules.
Its book connects explanations to the executable implementation and tests. The
model and its documentation are preserved in the repository's `v1/` directory.

Version 2 explores an alternative: a literate specification combining prose,
mathematical notation, examples, and Lean formalization. The Markdown can be read
on its own, while links to Lean declarations and rules let readers inspect how
the formalization corresponds to the mathematical presentation.

V2 is still a partial heap-model draft. The v1 implementation remains a useful
working reference as we develop it; the behavior and evidence documented in v1
apply to that version and do not establish the claims proposed in v2.
