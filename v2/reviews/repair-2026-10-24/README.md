# Review repairs — 24 October 2026

This repair addresses the [adversarial review](../adversarial-2026-10-24/README.md).
That report, its counterexamples, and its negative evidence records remain
unchanged. New decisions supersede them explicitly after reviewing the repairs.

## Tooling findings

| Finding | Repair | Regression coverage |
| --- | --- | --- |
| Included prose could change without invalidating evidence | Structured units reject mdBook expansion directives, including literal samples. The production preprocessor compares each received chapter's units with its original source before rendering. | `structured_units_reject_includes_and_nested_legacy_citations`, `preexpanded_includes_cannot_bypass_original_source_validation`, and `actual_mdbook_pipeline_rejects_includes_in_reviewed_content` |
| Rendering and evidence could select different Lean roots | Both use `SourceConfiguration` from `book.toml`; the effective mdBook context must agree. The configuration is a freshness input. Rust citations retain the project root even with a nested Lean root. | `configured_lean_root_is_shared_by_rendering_and_evidence` |
| Nested legacy citations escaped evidence discovery | Structured units reject nested legacy source citations. Related declarations belong in the unit's explicit citations or a separate dependency unit. | `authored_includes_and_nested_citations_cannot_acquire_evidence` |
| A rule could select another inductive's constructor | All selection kinds reject unsupported indented sibling commands. | `rule_citations_cannot_select_an_indented_siblings_constructor` |
| Rule selection dropped final literal tokens | Constructor extents use the literal-aware source scanner. | `rule_selections_preserve_final_literal_tokens` |

The actual-mdBook regression requires the installed executable, so ordinary Cargo
tests leave it ignored. The Pages workflow runs it explicitly after installing
the book tools. It also passed locally; see [the retained test output](tooling-checks.txt).

Five source-linked contracts now cover closed unit bodies, source configuration,
exact selection, active review decisions, and required review inputs. An
independent reviewer checked their implementation and regression cases and
provided specific comparison rationales. During that review, a whole-chapter
omission experiment exposed an overbroad sentence; the contract now states its
actual boundary. It protects units within chapters received by this preprocessor,
not the complete publication or later output transformations.

## Narrative findings

| Finding | Revision |
| --- | --- |
| Contributor machinery preceded the language | The main reading order is Dada, Given, Shared, then the separate heap draft. Contributor methods follow the semantics. |
| Representation preceded behavior | Given and Shared introduce their operations and complete small examples before the state representation. |
| Operation completion claims contradicted each other | The heap chapter bridges distinguish supported effects from pending complete path operations. |
| Failed checks, faults, and undefined behavior were conflated | The heap introduction establishes one status convention, and the affected examples and summaries use it. |
| Preservation preceded transitions; transitions occupied the state chapter | Lease allocation, invalidation, and cleanup moved to operations; preservation follows the transition chapters. |
| Shared-to-heap conventions changed without orientation | The heap introduction now has a compact comparison table and identifies the heap as a separate draft. |
| Borrow metadata obscured its purpose | The state chapter explains owners, borrowed access, and revocation before lease-graph details. |
| Routine proof and checking commentary competed with semantics | Repetitive proof paraphrases and implementation details were removed from semantic prose. |
| Notation and scope labels drifted | Access-path notation, shared-owner/borrow terms, layer names, and the historical appendix were made consistent. |

## Sharing and evidence

The [sharing decision](sharing-decision.md) retains the user's confirmation of
changing a field reference to shared when copying it, and the subsequent
clarification that objects themselves carry no ownership mode. The Shared
chapter now says which reference changes and separates stored-reference modes
from effective path permissions.

`Shared/Liveness:WellFormed.path_mode_exclusive` proves the requested path
property: no well-formed state admits both an entirely unique path and a shared
path to the same object. It follows from the existing representation invariants;
it does not change the operations or add an ownership mode to objects.

Fresh independent reviewers compared the Given, Shared, finite-map, and meta
units with frozen inputs. They checked theorem statements and assumptions rather
than auditing Lean proofs. Earlier adverse decisions remain recoverable; a new
positive decision is accepted only with explicit supersession and current inputs.

The full heap draft and remaining legacy renderer requirements have not silently
acquired evidence coverage. `meta.system.remaining_coverage` is an explicit
pending obligation. The evidence gate also does not record or certify Lean or
test execution; those mechanical checks run separately.

## Final validation

- `cargo test --locked --workspace`: 111 tests passed, including the current
  evidence gate; the actual-mdBook integration test is ignored in this ordinary
  run and passed in its separate explicit invocation.
- `dada-spec check`: all 35 required reviews are current and conclude
  correspondence; the legacy-coverage obligation remains visibly pending.
- `cargo fmt --all --check` and Clippy with warnings denied passed.
- `lake build --wfail`: all 57 jobs passed, including path exclusivity.
- `mdbook build` and `git diff --check` passed. The Given and Shared pages were
  inspected in the browser; the new path statement uses two display lines.

Retained outputs: [workspace tests](final-tests.txt),
[evidence status](final-evidence-status.txt), and
[targeted tooling checks](tooling-checks.txt).
