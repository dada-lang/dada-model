# dada-model

The original Rust model and mdBook are preserved in `v1/` as a working reference.
Read `v1/AGENTS.md` before changing that model. Its paths and commands are relative
to `v1/`. The v2 design draft is an mdBook in `v2/md/`, configured by `v2/book.toml`.
The book separates repository methods and specification-system requirements
(`v2/md/repo/`), Dada language goals (`v2/md/dada/`), and the Given/Shared language layers.
`v2/mdbook-dada` is a shared Rust library in the v2 Cargo workspace, with the
`mdbook-dada` renderer and `dada-spec` evidence CLI. Read `v2/AGENTS.md` before
changing structured units, evidence, or the tooling. `v2/spec.json` explicitly
selects strict chapters and review policies. Every new-style unit under `md/`
requires evidence; legacy paragraphs outside strict chapters are not implicitly
covered by evidence checks. Structured directives put a stable
unit ID on the opening line, then `:lean:` source citations and `:uses:` context
IDs in options before the body. Meta definitions cite `:rust:` implementation
symbols and `:tests:` test symbols. Do not mix Lean and Rust targets in one unit.
Definitions introduce concepts and judgments; they do not require proofs.
`:status: draft` preserves a unit's intended kind while separately marking unfinished formalization. Drafts
may omit source citations; supplied citations remain checked by kind. Drafts
fail evidence validation and cannot receive affirmative correspondence records.
All semantic prose in
strict chapters belongs in unit bodies, including explanatory examples.
The complete raw unit and exact cited declarations are required evidence inputs.
Structured units reject mdBook expansion directives (including literal samples)
and nested legacy citation blocks; separate units and `:uses:` make related
sources explicit. Renderer and evidence share the source-root configuration in
`book.toml`, which is itself a freshness input. The original chapter sources are
validated before processing mdBook's expanded input.
Content-hashed bundles and decisions live under `v2/evidence/`; preparing a packet
never approves it. `cargo test --workspace` from `v2/` includes deterministic
syntactic evidence validation, using `annotate-snippets` diagnostics and no agent,
network, or Lean invocation. Review compares theorem statements with intent;
Lean checks proofs. Current conservative context hashing can invalidate reviews
after proof-only edits. See `v2/md/repo/authoring.md`,
`v2/md/repo/correspondence-review.md`, and `v2/md/repo/layer-extension.md` for the
workflow and incremental models. Follow `v2/md/repo/writing-style.md` for
intent-first explanations, concrete examples, and notation introduced before
use. Build independently understandable layers from
the Given/Shared foundation; the earlier monolithic heap draft and its Lean modules
have been removed and must not serve as an implicit specification for later layers.
Render give syntax as `p→` and
`p→share`. The table of contents groups Operational semantics and Type system
under Given and Shared, followed by CFlow. Navigation pages are
`v2/md/given-overview.md` and `v2/md/shared-overview.md`; `v2/md/shared-typing.md`
and `v2/md/cflow.md` are editorial placeholders, with no semantic units yet.
The existing chapter paths remain unchanged. `v2/md/given-typing.md` contains
strictly covered units for signed views, typing rules, and storage realization,
with formal definitions and examples in `Unique/Views`, `Unique/Typing`,
`Unique/TypingRealization`, and their checks. `Unique/TypingSafety` proves
expression soundness for arbitrary pending values, machine progress and
preservation, and completion after exactly one step per statement. `Unique/Unpacking` adds `Class → { fields }` patterns with structural
preservation and embedding/reflection of the base machine. Shared correspondence
still covers the base fragment. See `v2/AGENTS.md` for the formalization boundary.
View omissions mean unknown and inaccessible, not empty. Positive entries expose
whole declared subtrees; negative entries describe existing empty slots.
View entries are prefix-incomparable. Expanded views are valid and normalize
by collapsing complete positive subtrees. Bare `C` is shorthand for `C.{ε}`,
not a separate type constructor; emptying is written `T[-ρ]`.
Constructor arguments still require their whole declared class types.
`v2/md/dada/future-extensions.md` records generic views as a proposal to revisit,
not part of the current rules.
The strict operational chapters live in `v2/md/given.md` and
`v2/md/shared.md`, with standalone Lean modules under `v2/lean/Unique/` and
`v2/lean/Shared/`. `Common/Rooted` supplies shared graph reasoning;
`Correspondence/UniqueShared` proves forward and backward execution
correspondence, including arbitrary successors, completion, and stuckness.
Both layers prove structural well-formedness preservation and rooted liveness.
See `v2/AGENTS.md` for their deliberately limited language scope. Ownership modes
belong to references, not objects. Copying through shared access can change the
final stored reference to shared. `Shared/Liveness` proves that no well-formed
state admits both an entirely unique path and a shared path to the same object.

The renderer also supports the following legacy authoring forms during migration.
It indexes MyST-style `{anchor}`, `{definition}`, and `{anchor-ref}` roles and renders `{heap}` fenced directives as SVG from declarative facts, with a Rendered/Facts selector.
Fenced `{grammar} File:Type ...`, `{judgment} File:Name`, and
`{rule} File:Judgment.constructor` directives pair authored LaTeX bodies with
cited Lean declarations or cases through a Rendered/Lean selector. Fenced
`{definition} File:Name ...`, `{theorem} File:Name`, and `{lemma} File:Name`
instead contain Markdown statements and explicitly delimited mathematics;
proof blocks may include high-level proof outlines. A definition takes one or
more citations to named `def`, `abbrev`, `structure`, or `inductive` declarations
and shows their complete bodies. It rejects theorem, axiom, example, and
constructor-only citations. Definition extraction supports the documented
line-oriented equation, `:=`, and `where` bodies, including qualified names.
Top-level `mutual` groups of named inductives are supported when their headers
and the `mutual`/`end` delimiters start at column zero and each header ends in
`where` on its first line. A citation selects one complete member; evidence
retains the enclosing source. Nested groups and other mutual declaration kinds
are rejected.
Semantic Definition labels should have this citation-backed selector; modeling
conventions and commentary remain ordinary prose or neutral anchors. Theorem and lemma blocks
select exactly one named Lean `theorem`, including its complete proof, and reject
definitions, axioms, and anonymous examples. Definitions introduce concepts;
theorems and lemmas state results.
Structured draft status distinguishes proposed results from established ones
without changing their semantic kind. The inline `{definition}` role remains a compatibility spelling for a
label, not a Lean citation; use a fenced definition for semantic definitions.
Generic `{anchor}` markers
are neutral outside definition/proof blocks and inherit the surrounding
Definition, Theorem, or Lemma label within them. No label establishes prose/proof correspondence.
Leading identifying anchors in Markdown blocks move into the header as shields,
replacing the plain kind label without duplicating IDs. Later anchors stay with
their prose. A leading example anchor uses the Example label; later example
anchors remain neutral. All block headers place the view controls on the right, including
grammar/judgment/rule and Rendered/Facts diagram selectors; the identity stays
visible in either view. Unanchored blocks show their kind as a plain label.
Definition and theorem names may contain dots when that exact name is written in the declaration;
the extractor does not infer qualification from enclosing namespaces. Grammar blocks accept
one or more whitespace-separated citations on the opening line; judgment and rule
blocks take one. Fenced `{example} File:anchor` directives pair authored Markdown
with an anchored anonymous Lean `example` proof through the same selector.
Standalone `-- ANCHOR: name` and `-- ANCHOR_END: name` comments delimit exactly
one top-level example; they are not Lean declaration names. The selected Lean
`example` starts at column zero, continuation lines are indented, and the next
command after the closing marker starts at column zero. The authored body supports
Markdown and the book's roles and other block directives. Definitions, examples,
theorems, and lemmas cannot nest inside one another; other supported directives may occur
inside their Markdown bodies.
Use a longer enclosing fence for bodies with code fences. The `.lean` extension
is optional in citations. Missing, duplicate, malformed, or wrong-kind targets and
paths escaping `lean-source` fail the book build. The Markdown mathematics and notation explanations stand on
their own, with Lean as an associated formalization. `src/lean.rs` handles textual
source selection and HTML, not mathematical derivation or Lean elaboration. The
`lean-source` book setting locates Lean files. `v2/theme/mathjax.js` loads pinned
MathJax 4.1.3 from a CDN with CommonHTML output and New Computer Modern fonts;
mdBook's built-in MathJax 2 loader is disabled. Authored display line breaks are
preserved, with horizontal scrolling for wide equations. Explicit Markdown
math delimiters use doubled backslashes (`\\[`/`\\]`, `\\(`/`\\)`). Their
contents are protected from Markdown escapes and smart punctuation, including
TeX row breaks and primes; literal code samples are excluded.
Always group overbar expressions, as in `{\overline f}`. The command must be
immediately preceded by an opening brace and immediately followed by a literal
ASCII space. The preprocessor rejects a violation of either condition with
a source path and line number. This source lint also applies to literal TeX
samples; a test scans every Markdown file under `v2/md/`, including files absent
from the book's table of contents. Longer TeX command names are not matches.
The former `{lean.type}`, `{lean.judgment}`, and `{lean.rule}` directives are
rejected with migration diagnostics. The old grammar DSL/parser and automatic
Lean-to-LaTeX translator have been removed; Lean notation comments have no
rendering effect. The build checks citations and supported declaration or example
forms, not Lean proofs or correspondence between prose, mathematics, and Lean.
Run `just test-lean` to compile all modules, including every cited example and theorem.
Its `lake build --wfail` command rejects warnings, including those emitted by Lean `sorry`.
Do not introduce admissions, suppress `warn.sorry`, or disable this check; any future allowance must require
an explicit opt-in. Review still establishes that the test covers the prose. Every semantic example
must cite its intended Lean test. Unfinished semantic scenarios are explicitly
proposed or pending. Authoring-syntax illustrations remain ordinary prose and
literal code. Structured units additionally participate in the configured review
inventory; legacy inline anchors do not establish review boundaries. The syntax,
notation conventions, and review requirements are documented in `v2/md/repo/spec-system.md`;
theme CSS lives in `v2/theme/dada.css`.
`{informational}` at the start of a paragraph labels nonnormative commentary.
The former `{example}` paragraph prefix is rejected; use the fenced directive.
`src/routing.rs` routes diagram edges orthogonally around boxes.
Anchor IDs must be globally unique, and unresolved references fail the build.
The `{heap}` directive remains a diagram-rendering facility; its fact syntax
and validation are tooling features, not a specification of future language layers.
Graph structure checks do not establish language invariants.

The active semantic foundation is `v2/lean/Unique/`, `v2/lean/Shared/`, and their
correspondence, with supporting graph reasoning in `v2/lean/Common/`.
`Common/FiniteMap` and `Common/FiniteMapExamples` retain the utility and example
used by the evidence pilot. Renderer source-selection tests use the isolated
`v2/mdbook-dada/tests/fixtures/lean/` tree; those fixtures are not a language model.
The book
introduces Given and Shared before contributor methods. Extend these languages
one step at a time, stating and reviewing new behavior before formalizing it.
Definitions expose Lean bodies; proved results expose proofs. Semantic chapters
describe the current model; historical investigations belong in review records.
Source selection and syntactic evidence validation do not establish correspondence
or prove that a review was actually performed. Keep candidate claims distinct
from established proofs and executable examples.

## Build and test

- `just test` runs the v1 Cargo and mdBook example tests, v2 preprocessor tests,
  and the Lean project.
- `just test-lean` runs `cd v2/lean && lake build --wfail` with pinned Lean 4.35.0.
- From `v1/`, run `cargo test --all --workspace` and `mdbook build`.
- From `v2/`, run `cargo fmt --all`, `cargo clippy --workspace --all-targets -- -D warnings`,
  and `cargo test --workspace` for changes to the Rust tooling; the workspace test
  includes required evidence validation.
- From `v2/`, `cargo run -p mdbook-dada --bin dada-spec -- status --explain`
  explains evidence status; `check` enforces the configured requirements.
  `prepare UNIT_ID` writes an immutable comparison bundle, and
  `record BUNDLE_PATH REVIEW_JSON_PATH` records a completed review only when its
  inputs are still current. See `v2/AGENTS.md` for the review loop.
- `just book-v2` builds the v2 draft; `cd v2 && mdbook serve` previews it.
- `just book-tools` installs pinned mdBook 0.5.4 and mdbook-mermaid 0.17.1;
  the custom preprocessors are built from the two Cargo workspaces.
- `just site` builds both books and the root redirect into the ignored `_site/`
  directory, using the same script as CI. Stable Rust is required.

## Publishing

GitHub Actions workflows remain in `.github/workflows/`. The Pages workflow
tests v1 book examples, checks the pinned Lean project, and builds both books on pull requests and pushes to
`main`; only `main` deploys. It installs tools using `pages/install-tools.sh`
and assembles the site with `pages/build.sh`: `pages/index.html` at the root,
the older book under `/dada-model/v1/`, and the new book under `/dada-model/v2/`.
The root redirects to v2. Its older versions appendix
(`v2/md/appendices/older-versions.md`) explains the a-mir-formality-based v1
model and links back to its book using the assembled site's relative paths.
Each book's `site-url` matches its published prefix for 404 asset resolution.
Keep generated v1 source links pointed at the repository's `v1/` directory.
The checked-in v1 Mermaid initializer must match mdBook's theme menu IDs.
See `pages/README.md` for preview commands, dependencies, and the required
GitHub Actions source setting in repository Pages settings.

Keep this file and `v1/AGENTS.md` current when changing the repository layout.
