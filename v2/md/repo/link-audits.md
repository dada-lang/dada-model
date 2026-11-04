# Reviewing links and reading order

A definition link should save the reader a search. The plugin extracts links
from existing units; reviewers check whether any are missing and whether their
destinations explain the right subject. No extra Markdown annotations are needed.

## Inspect the inventory

From `v2/`, run:

```sh
cargo run -p mdbook-dada --bin dada-spec -- links
cargo run -p mdbook-dada --bin dada-spec -- links --json
```

The output lists occurrences, destinations, reading order, candidate cycles, and
required audit subjects. The JSON is useful for preparing review work; it is a
derived inventory, not another source file to maintain.

```{definition} meta.links.inventory
:rust: mdbook-dada/src/links.rs:LinkInventory::build
:tests: mdbook-dada/tests/links.rs:inventory_reads_markdown_reference_roles_and_math_with_exact_ranges mdbook-dada/tests/links.rs:reference_definitions_outside_unit_and_bare_math_directives_are_inventoried mdbook-dada/tests/links.rs:relative_paths_preserve_target_chapter_and_wrong_path_does_not_match_global_id mdbook-dada/tests/links.rs:order_comes_from_summary_and_byte_position_not_filename_or_unit_id mdbook-dada/tests/evidence_validation.rs:configured_renderer_rejects_a_correct_claim_in_the_wrong_chapter

The *link inventory* records each authored link in a structured unit: its source
range, destination, label, syntax, and position in the book. It recognizes
Markdown links, including reference-style links, anchor-reference roles, and
MathJax `\href` commands. Literal code and comments do not introduce links. Authored HTML links and
unsupported local URL forms are rejected rather than silently omitted. A
published chapter cannot link to a chapter absent from `SUMMARY.md`.

An internal destination must resolve to the specified chapter and anchor;
finding the same ID in another chapter is insufficient. Reading order follows
`SUMMARY.md`, then source position within each chapter. A link into its own
containing definition is classified as local, pending review of the actual
defining passage. Chapters absent from the table of contents have unknown
relative order; repair the table of contents before treating such a dependency
as backward. Candidate cycles are reported without treating them as justified
forward references.

Future notes receive the same link audits: proposals need readable explanations
too. These editorial reviews do not claim that a proposal has a formalization.
```

## Review three questions

```{definition} meta.links.coverage
:rust: mdbook-dada/src/link_audit.rs:AuditInventory::build mdbook-dada/src/link_audit.rs:validate_review
:tests: mdbook-dada/tests/link_audit.rs:coverage_requires_each_occurrence_once_and_both_prose_and_math_rationales mdbook-dada/tests/link_audit.rs:complete_link_audits_pass_but_preparation_alone_does_not mdbook-dada/tests/link_audit.rs:conceptual_external_links_require_an_inspectable_local_definition

A *link-coverage review* examines one complete unit, including prose, inline math,
and display math. Every referenced concept, operation, judgment, and equation
must have a definition link. The defining occurrence needs no self-link, and
locally bound variables need an introduction and scope rather than links.

The review explains coverage separately for prose and mathematics and classifies
every occurrence in the [link inventory](#claim-meta.links.inventory) as conceptual or navigation, with a reason. A
navigation link offers optional further reading; it cannot stand in for a
definition the passage needs. Reviewers must also look for unlinked uses: the
extractor cannot discover a missing link by examining existing links alone.

The validator requires exactly the extracted occurrence set, including repeated
links. Missing, extra, or duplicate assessments fail. It checks the existence
and freshness of the review, not whether its coverage judgment is correct.
```

```{definition} meta.links.targets
:rust: mdbook-dada/src/link_audit.rs:validate_review
:tests: mdbook-dada/tests/link_audit.rs:target_spans_cannot_escape_or_select_empty_text mdbook-dada/tests/link_audit.rs:independent_positive_reviews_cannot_disagree_on_backward_links_or_target_spans

A *target-clarity review* names a subject in the
[link inventory](#claim-meta.links.inventory) and selects its defining
passage in the retained source. It explains why the landing immediately
identifies that subject and why the definition is independently understandable.
A precise source span does not excuse a buried destination: split the block or
retarget the link when a reader would still have to search.

The validator checks that the selected span is nonempty UTF-8 text within the
resolved destination. Review supplies the judgment that it is the relevant
definition. A chapter or section link used only for navigation is reviewed as
such; it must not be presented as a precise concept definition.
```

```{definition} meta.links.order
:rust: mdbook-dada/src/link_audit.rs:AuditInventory::build mdbook-dada/src/link_audit.rs:validate_review mdbook-dada/src/link_audit.rs:cross_validate
:tests: mdbook-dada/tests/link_audit.rs:forward_exceptions_require_all_three_reasons_and_a_real_source_span mdbook-dada/tests/link_audit.rs:a_local_link_before_its_actual_definition_cannot_be_called_backward mdbook-dada/tests/link_audit.rs:navigation_exemption_must_agree_with_current_coverage mdbook-dada/tests/link_audit.rs:source_movement_summary_order_and_reference_definitions_invalidate_inputs

A *reference-order review* resolves each forward, local, or unordered internal
occurrence in the [link inventory](#claim-meta.links.inventory). It agrees with
the [coverage classification](#claim-meta.links.coverage) and uses the
[reviewed defining passage](#claim-meta.links.targets), not merely the block's
header, to establish whether a concept has already been introduced.

Prefer moving the definition earlier, moving its use later, or splitting a
multi-part explanation. Retaining a forward conceptual reference requires all
three explanations:

- **Necessity:** which rearrangements were considered and why they would prevent
  a coherent introduction.
- **Signposting:** the exact source passage that explicitly tells the reader the
  definition comes later, and where to find it.
- **Minimal use:** the facts needed at this point, where the text states them,
  and which details it defers.

A motivating example may justify a forward reference; being an example is not
an automatic exemption. A dependency cycle is not an exemption either.
Navigation-only links need an explicit classification, and a local backward
reference must point to a defining passage before its use. Conflicting active
reviews block validation.
```

## Prepare and record evidence

Use the subject IDs printed by `dada-spec links` with the existing
[preparation and recording workflow](correspondence-review.md#prepare-the-comparison):

```sh
dada-spec prepare links.coverage/UNIT_ID
dada-spec prepare links.target/TARGET_HASH
dada-spec prepare links.forward/OCCURRENCE_HASH
dada-spec record BUNDLE_PATH REVIEW_JSON_PATH
```

Each decision retains the ordinary reviewer, provenance, examined inputs,
conclusion, rationale, limitations, and superseded decisions. Its `audit` field
adds the question-specific assessment. See the Rust `Assessment` schema in
`mdbook-dada/src/link_audit.rs` for the exact JSON fields. Preparation never
creates an affirmative decision.

Coverage packets retain the complete source unit, its explicit context, and
linked destinations. Target packets retain the destination. Order packets
retain both ends. All three also retain relevant complete chapters, a serialized
position/order inventory, `SUMMARY.md`, policy, and tool/rendering inputs.
Reviewers examine the required `audit:` inputs and consult the retained chapter
context to assess landing clarity and possible rearrangements. Byte positions
participate in freshness, so moving unchanged text can invalidate an audit.
Whole-chapter snapshots conservatively invalidate affected audits after other
edits in those chapters too.
Evidence outputs are not inputs to other evidence; current active decisions are
cross-checked for consistency instead.

`dada-spec check` and `cargo test --workspace` require these reviews alongside
formal correspondence evidence. Draft units still receive editorial audits;
their unfinished formalization separately blocks correspondence. The checker
never invokes an agent, fetches a website, or decides whether a rationale is
persuasive. An independent reader can inspect the retained inputs and reasoning.
