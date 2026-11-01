# Adversarial tooling review

Inspected the actual renderer/parser and inventory/evidence implementation, including `units.rs`, `lean.rs`, `rust_source.rs`, `inventory.rs`, and `evidence.rs`. Read repository/v2 AGENTS and Rust skill. No production files, tracked tests, or repository evidence were changed. Synthetic approvals below exist only in clearly labeled temporary fixtures and establish no semantic claim.

Verified binaries match current source with `cd v2 && cargo build --offline -p mdbook-dada --bins` (no rebuild necessary). Run all reproductions with `python3 /tmp/dada-review-harness.py`. It creates fresh fixtures beneath the system temporary directory; latest run used `/var/folders/_p/2k16wz5j1fxc1dfrv6ch460m0000gn/T/dada-review-7q4m986z`. That directory preserves selected bundles, synthetic records, and rendered outputs. The script uses the public CLI and preprocessor executable, and the include case runs an actual `mdbook build`.

## 1. [P1] Fingerprint mdBook include contents, or reject includes in reviewed units

Location: `v2/mdbook-dada/src/inventory.rs:256-260` (raw unit snapshot), with input assembly at `316-359`.

The inventory snapshots `unit.raw` and selected declarations, but never discovers or resolves mdBook include directives. The renderer receives/produces content subject to mdBook's links preprocessor, so the exact authored prose being shown is not necessarily present in the bundle. This affects existing configuration, without changing `book.toml`.

Minimal unit:

````markdown
```{definition} model.value
:lean: Fixture:value

{{#include details.txt}}
```
````

`lean/Fixture.lean` defines `def value : Nat := 1`. `md/details.txt` initially contains “The value is one.” Prepare/record a synthetic fixture review; run actual `mdbook build`; then change only `md/details.txt` to “The value is two, not one.” and build again. The generated `book/model.html` contains the changed claim, yet `dada-spec check` still prints:

```
model.value: inputs=current, correspondence=corresponds, mechanical=not recorded
```

The bundle does not contain `md/details.txt` or its expanded content. The same mechanism could bring in new structured units that the raw Markdown inventory never sees. Source selection and strict coverage are therefore based on a different document from the published page.

Suggested fix: either reject mdBook include/playground/rustdoc-include directives inside reviewed content (with an explicit diagnostic) or resolve all supported includes identically to the book pipeline and fingerprint the recursively included inputs, while retaining original raw authoring. Add an actual mdBook integration fixture proving included prose changes cannot keep an approval current.

## 2. [P1/P2] Use the configured Lean source root for both rendering and evidence

Location: `v2/mdbook-dada/src/inventory.rs:263-265`; context enumeration hardcodes the same root at `344-355`. The renderer instead derives it from configuration at `v2/mdbook-dada/src/main.rs:20-23`.

Inventory always selects from `root/lean`, while the renderer uses `preprocessor.dada.lean-source`. `book.toml` is also missing from tool inputs (`inventory.rs:319-324`). A review can remain current for the old declaration when the actual book shows another one.

Reproduction: approve a unit citing `Fixture:value`, with `lean/Fixture.lean` containing `def value : Nat := 1`. Change `book.toml` to `lean-source = "lean-alt"` and add `lean-alt/Fixture.lean` containing `def value : Nat := 2`. Invoke the actual preprocessor with the configured context. Its source view changes to `:= 2`; `dada-spec check` still returns current/corresponds. The script confirms `book.toml` is absent from the bundle.

Suggested fix: load and validate one shared source-root configuration and include it in freshness inputs. If the evidence system intentionally permits only `lean/`, enforce that constraint at the renderer/configuration boundary and fail when the book configuration disagrees. Merely hashing book.toml is insufficient to prevent new bundles from reviewing `lean/` while rendering another root.

## 3. [P2] Include nested legacy source citations in a unit's evidence inputs

Location: `v2/mdbook-dada/src/inventory.rs:263-275` (only options are selected) and `304-310` (only linked units are followed). Rendering recursively processes the body at `v2/mdbook-dada/src/lib.rs:340-345` and renders legacy grammar/judgment/rule directives around `597-620`.

Supported legacy grammar/judgment/rule directives can nest within a structured Markdown unit. The inventory does not traverse these nested citations. For a Rust-backed parent this also means the Lean tree is not captured at all, because the full-source branch runs only when a `lean:` input already exists.

Minimal unit:

`````markdown
````{definition} model.value
:rust: mdbook-dada/src/lib.rs:validate

The renderer displays this grammar.

```{grammar} Fixture:Thing
t ::= Nat
```
````
`````

`pub fn validate() {}` is an ordinary implementation citation; `lean/Fixture.lean` initially has `abbrev Thing := Nat`. Record the synthetic fixture review, then change `Thing` to `Bool`. The Lean selector in the rendered unit changes, but check remains current/corresponds. The bundle has zero paths under `lean/`.

This also violates the required-input rule for nested citations in Lean-backed units: a conservative full-file context exists, but the nested exact declaration is not a mandatory examined input.

Suggested fix: either reject all legacy citation directives nested within structured units and require separate units with `:uses:`, or recursively discover them with the same parser used for rendering and add exact cited selections plus context. If mixed Lean/Rust units are intentionally disallowed, check nested citations too.

## 4. [P2] Reject indented sibling commands before selecting a rule constructor

Location: `v2/mdbook-dada/src/lean.rs:318-335`, specifically the `selection != Selection::Type` guard. Rules call `extract` using `Selection::Type` (`421-443`), so this guard skips the sibling-command rejection for rule/judgment/grammar extraction.

This valid Lean source compiles with `lake env lean /tmp/dada-indented-sibling.lean`:

```lean
inductive First where
  | first
  inductive Second where
  | second
#check First.first
#check Second.second
```

A rule unit citing `Fixture:First.second` is accepted and both the renderer and bundle select:

```lean
inductive First where
  | second
```

There is no `First.second`. `extract_declaration` absorbs the indented sibling `Second` as part of `First`, and `extract_case` then picks its same-indent constructor. The fixture renders and successfully completes syntactic evidence validation.

Suggested fix: enforce the no-indented-sibling-command rule for all selected declaration kinds, including the type selector, with the existing structure-field exception where needed. Add a regression test where a nonexistent constructor name belongs to an indented sibling type.

## 5. [P2] Retain literal tokens at the end of selected constructors

Location: `v2/mdbook-dada/src/lean.rs:772-774`.

`extract_case` determines the source end with `masked[..end].trim_end().len()`. The mask replaces literals and quoted identifiers with spaces, so trimming it removes real final tokens rather than just trailing comments. The top-level declaration extractor already has a `scan(...).content_end` mechanism that retains literals, but rule selection does not use it.

This source compiles with `lake env lean /tmp/dada-string-index.lean`:

```lean
inductive Indexed : String → Type where
  | zero : Indexed "zero"
#check Indexed.zero
```

A unit citing `Fixture:Indexed.zero` selects (and displays):

```lean
inductive Indexed : String → Type where
  | zero : Indexed
```

The index `"zero"` disappears from the exact declaration required for review. This changes the constructor's proposition/type and can mislead review even though full-file context still contains the real source.

Suggested fix: determine the per-case extent with the scanner's literal-aware `content_end`, preserving comments that belong to the selected constructor and dropping only following standalone comments. Cover strings, raw strings, character literals, and quoted identifiers at a case's final token.

## Other inspection results

The existing record checks do reject missing mandatory inputs, altered snapshots, stale active decisions, and independent negative decisions. Superseded records are retained; the current stale-active check avoids silently falling back to an unrelated positive record. I did not find an additional concrete record/supersession bug during this pass. No broad test suite was run solely to claim correctness; the isolated counterexamples directly exercise current executable behavior.
