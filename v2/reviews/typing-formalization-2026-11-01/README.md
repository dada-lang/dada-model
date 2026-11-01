# First Given typing formalization — 2026-11-01

The reviewed Markdown foundation was committed first as `1d11b1a`. This pass
adds Lean definitions and checked examples without admissions. It does not
complete the general static soundness proof.

## Implemented and checked

- `Unique/Views` defines typed declarations, signed views, observations,
  normalization, focus, emptying, and view weakening. `ViewChecks` covers the
  chapter's view table, normalization boundaries, input permutations, recursive
  declarations, and unknown-versus-empty fields.
- `Unique/Unpacking` extends the machine with flat binding patterns. It proves
  structural well-formedness preservation and embedding/reflection of the base
  fragment. `UnpackingChecks` covers the complete Pair example, reordered fields,
  empty classes and freshness rejection.
- `Unique/Typing` defines environments, taking, expression and argument typing,
  bindings, statements and programs. `TypingEffects` proves that expression
  typing preserves variable keys, as well as its static admissibility properties.
- `Unique/TypingRealization` connects types with storage and pending owners.
  Weakening preserves satisfaction for normalized types. `TypedConfigurations`
  defines machine typing and proves its initial and finished cases.
- `TypingChecks` and `TypingExecutionChecks` cover the nested Box program's
  intermediate types, exact runtime execution, final heap, completion, and
  rejection of subsequent gives from empty bindings.

The parent ran `just test-lean`: all 34 build jobs passed with `--wfail`.
`just book-v2` and `git diff --check` passed. Browser inspection verified the
Lean selector and found no MathJax errors; [preview.png](preview.png) shows the
associated source in the book. No Rust implementation changed.

## Correspondence review and findings

Fresh subagents `/root/review_formal_views`, `/root/review_formal_typing`, and
`/root/review_formal_unpacking` independently compared immutable packets with
the authored units. The `*-bundles.json` manifests identify their inputs; the
`views/`, `typing/`, and `unpacking/` directories retain detailed decisions and
examined input keys. [recorded.json](recorded.json) identifies all 21 recorded
positive decisions. These are comparisons of statements and definitions, not
substitutes for Lean proof checking.

Two initial findings were addressed before recording:

1. The weakening explanation used Pair without recording the authored example
   that defines it. Its explicit dependency now includes that example.
2. The nested move example's first citation proved only static typing, while
   its prose also described runtime object consumption. The replacement anchor
   includes the exact four-step Box execution and final heap, all intermediate
   type rows, completion, and universal rejection of repeated left/p gives.

The initial inconclusive/mismatch decisions remain in `initial-review/`. After
the fixes, reviewers compared replacement packets, read the changed inputs,
and recorded new provenance. No obsolete hashes were refreshed to manufacture
approval.

## Remaining work

General normalization observation preservation, well-formedness preservation,
idempotence, and permutation invariance still need proofs. Concrete examples
and source review do not establish those universal results.

Static progress and preservation need ownership-separation lemmas: moving
through one variable must preserve the descriptions of all other variables and
pending roots. Focus, emptying, constructor and binding realization lemmas must
then connect the executable view operations with heap transitions. The four
soundness claims remain Draft. The broader rejection example also remains Draft
until all of its scenarios have a complete corresponding formal case.

[workspace-tests.log](workspace-tests.log) records 37 library tests and 39 book
tests passing, then the required evidence test failing. The final
[evidence status](final-status.txt) has 21 current decisions, 41 older stale
decisions, and 7 draft units (including future extensions). This pass did not
re-review the older foundation or approve unfinished claims. The workspace
evidence gate remains red, as intended while those inputs are incomplete.
