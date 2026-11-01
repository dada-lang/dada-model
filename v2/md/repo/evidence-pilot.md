# Implementation contracts and evidence

## Implementation contracts

```{definition} meta.units.closed_body
:rust: mdbook-dada/src/units.rs:parse_block mdbook-dada/src/configuration.rs:SourceConfiguration::validate_chapters
:tests: mdbook-dada/tests/units.rs:structured_units_reject_includes_and_nested_legacy_citations mdbook-dada/tests/evidence_validation.rs:authored_includes_and_nested_citations_cannot_acquire_evidence mdbook-dada/tests/evidence_validation.rs:preexpanded_includes_cannot_bypass_original_source_validation mdbook-dada/tests/evidence_validation.rs:actual_mdbook_pipeline_rejects_includes_in_reviewed_content

A structured unit contains its reviewed text directly. It rejects mdBook include,
playground, and rustdoc-include directives, including those in literal samples.
It also rejects nested legacy source-citation blocks. Related source selections
belong in separate units connected by explicit dependencies.

For each chapter received by the Dada preprocessor, the ordered unit IDs and raw
structured-unit text must match that chapter's original source. Earlier content
preprocessing may not add, remove, or change units within that chapter. This
rejects an include even if mdBook has already expanded it before this boundary.

The comparison covers received chapters at this preprocessing stage. It does not
check whether a whole chapter was omitted or whether later output processing
changes the generated page.
```

```{definition} meta.sources.configuration
:rust: mdbook-dada/src/configuration.rs:SourceConfiguration::load mdbook-dada/src/configuration.rs:SourceConfiguration::lean_root mdbook-dada/src/configuration.rs:SourceConfiguration::markdown_root mdbook-dada/src/configuration.rs:SourceConfiguration::check_context mdbook-dada/src/lib.rs:process_configured mdbook-dada/src/inventory.rs:Inventory::inputs
:tests: mdbook-dada/tests/evidence_validation.rs:configured_lean_root_is_shared_by_rendering_and_evidence

Rendering and evidence read the same book and Lean source roots from `book.toml`.
Runtime overrides that disagree with those roots are rejected. Roots remain
inside the project. Rust citations use the project root, even when the Lean root
is nested several directories below it.

The configuration is a review input. Changing it makes existing evidence stale;
a new packet selects declarations and context from the newly configured root.
```

```{definition} meta.sources.exact_selection
:rust: mdbook-dada/src/lean.rs:select mdbook-dada/src/lean.rs:extract_declaration mdbook-dada/src/lean.rs:validate_mutual_groups mdbook-dada/src/lean.rs:extract_case mdbook-dada/src/lean.rs:scan
:tests: mdbook-dada/tests/units.rs:rule_citations_cannot_select_an_indented_siblings_constructor mdbook-dada/tests/units.rs:rule_selections_preserve_final_literal_tokens mdbook-dada/src/lean.rs:tests::selects_mutual_inductive_members_and_surrounding_declarations mdbook-dada/src/lean.rs:tests::mutual_validation_ignores_comment_and_literal_decoys mdbook-dada/src/lean.rs:tests::rejects_unsupported_or_incomplete_mutual_groups_before_any_selection

A rule citation selects one constructor of its named inductive declaration.
Unsupported indented sibling commands are rejected rather than treated as part
of that declaration. A constructor from a sibling type cannot satisfy the citation.

Top-level `mutual` groups of named inductives are supported in the documented
column-zero form. A citation selects the complete named member; the full enclosing
source remains an evidence input. Nested, malformed, or other kinds of mutual
groups are rejected.

Selection preserves literal tokens, including a final string or character index
and quoted identifiers. It may omit a following standalone comment; it may not
truncate the constructor's type. These are textual source-selection checks, not
Lean elaboration or a proof that the authored mathematical rule has the same meaning.
```

```{definition} meta.evidence.active_decisions
:rust: mdbook-dada/src/evidence.rs:record mdbook-dada/src/evidence.rs:check
:tests: mdbook-dada/tests/evidence_validation.rs:recording_rechecks_sources_even_with_an_existing_inventory mdbook-dada/tests/evidence_validation.rs:mismatch_and_inconclusive_reviews_never_count_as_correspondence mdbook-dada/tests/evidence_validation.rs:revised_review_can_supersede_same_unit_after_consulting_more_context mdbook-dada/tests/evidence_validation.rs:stale_supersession_cannot_fall_back_to_an_independent_positive_review

Recording a review rechecks its inputs against current sources. A later decision
may explicitly supersede an earlier decision for the same unit; the earlier
record remains available. Every active decision must concern current inputs and
conclude correspondence for that unit's check to pass.

An independent positive decision cannot conceal an active mismatch, inconclusive
review, or stale decision. If a replacement becomes stale, checking fails rather
than falling back to the old positive review. Draft units fail validation and
cannot receive affirmative correspondence decisions.
```

## Required inputs

```{definition} meta.evidence.required_inputs
:rust: mdbook-dada/src/evidence.rs:validate_bundle mdbook-dada/src/inventory.rs:Inventory::inputs
:tests: mdbook-dada/tests/evidence_validation.rs:rejects_missing_or_substituted_required_inputs mdbook-dada/tests/evidence_validation.rs:renderer_lean_fixtures_are_required_freshness_inputs
:uses: meta.units.closed_body meta.sources.configuration meta.sources.exact_selection

For a review bundle, validation derives its required inputs from the current
specification inventory. The bundle must contain the complete authored unit and
every exact cited Lean declaration, together with required context, policy,
and tooling snapshots. Tooling snapshots include the renderer's Lean test
fixtures, so fixture edits invalidate existing reviews. A complete Lean source file does not substitute for a
missing exact declaration selection.

Validation reports missing required inputs, changed or substituted input
contents or paths, and inconsistent snapshot hashes. Additional consulted files
are included as explicit extra inputs and checked against their current
contents. This is a check of input identity and completeness; it does not decide
whether the mathematical explanation corresponds to Lean.
```

## Finite maps

```{definition} evidence.map
:lean: Common/FiniteMap:FiniteMap Common/FiniteMap:FiniteMap.empty

A finite map associates a key with at most one value. Write
\\(M : K \rightharpoonup T\\) for a finite map from keys in \\(K\\) to values
in \\(T\\). Its finite list of entries contains pairs \\((k,v)\\), and no key
occurs twice. The list records an order; the unique-key condition does not impose
an order on the keys themselves.

The empty map \\(\varnothing\\) has no entries.
```

```{lemma} evidence.map.value_unique
:lean: Common/FiniteMap:FiniteMap.value_unique
:uses: evidence.map

For any {anchor-ref}`evidence.map` \\(M\\), key \\(k\\), and values
\\(v,w\\), if both \\((k,v)\\) and \\((k,w)\\) are entries of \\(M\\),
then \\(v=w\\). This holds for any key and value types; no ordering or
decidable equality on keys is assumed.
```

```{example} evidence.map.empty
:lean: Common/FiniteMapExamples:empty_map
:uses: evidence.map

Choose natural numbers as both keys and values. The empty
{anchor-ref}`evidence.map` has the empty entry list \\([]\\).
There is no key-value pair stored in this example.
```

