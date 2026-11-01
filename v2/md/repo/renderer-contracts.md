# Renderer contracts

## Identities and blocks

```{definition} meta.syntax.anchors.identity
:rust: mdbook-dada/src/lib.rs:roles mdbook-dada/src/lib.rs:chapter_roles mdbook-dada/src/lib.rs:process_with_roots mdbook-dada/src/lib.rs:relative_html mdbook-dada/src/lib.rs:render_role
:tests: mdbook-dada/tests/book.rs:indexes_forward_references_and_nested_chapters mdbook-dada/tests/book.rs:cross_references_traverse_to_parent_and_bad_references_fail mdbook-dada/tests/book.rs:literal_examples_are_not_anchors mdbook-dada/tests/book.rs:typed_anchor_roles_share_ids_and_references_without_implying_proofs

An *identity* names one location in the book. IDs begin with an ASCII letter or
digit and otherwise contain ASCII letters, digits, dots, underscores, or hyphens.
Structured unit IDs and legacy defining roles share one global namespace.
Malformed IDs, duplicate definitions, and unresolved references fail rendering.
Forward references and references between nested chapter directories work.

{anchor}`meta.syntax.anchors.roles`
Legacy `{anchor}` and `{definition}` roles define locations; `{anchor-ref}`
links to them. A neutral anchor inherits the surrounding definition, theorem,
or lemma label. A role's label does not establish correspondence or a proof.

{anchor}`meta.syntax.anchors.inline`
A defining role stays in its paragraph. Put it immediately before the text to
show the shield inline with that text.

{anchor}`meta.syntax.anchors.rendering`
Definitions become local HTML shields. References become **ref** shields linking
to the defining chapter and fragment. Shields require no external badge service.

{anchor}`meta.syntax.anchors.literal`
Roles inside fenced or indented code, links, or HTML blocks remain literal.
Escaped role prefixes and double-backtick demonstrations also remain literal.
These are the supported custom roles, not a general MyST parser.
```

```{definition} meta.syntax.inline_and_block
:rust: mdbook-dada/src/units.rs:parse_block mdbook-dada/src/lib.rs:directive_blocks mdbook-dada/src/lib.rs:render
:tests: mdbook-dada/tests/book.rs:block_directives_are_distinct_from_literal_code_and_inline_roles mdbook-dada/tests/book.rs:informational_paragraphs_preserve_markdown_and_literal_examples mdbook-dada/tests/book.rs:generated_grammar_directives_require_migration mdbook-dada/tests/book.rs:inferred_judgment_and_rule_directives_require_migration mdbook-dada/tests/units.rs:drafts_keep_their_semantic_kind_without_claiming_a_formalization mdbook-dada/tests/units.rs:draft_status_is_explicit_and_does_not_relax_citation_checks mdbook-dada/tests/units.rs:removed_obligation_syntax_is_rejected_at_every_authoring_entry_point
:uses: meta.units.closed_body

Inline roles label or refer to locations. Fenced directives create blocks:
`{definition}`, `{grammar}`, `{judgment}`, `{rule}`, `{theorem}`, `{lemma}`,
`{example}`, and `{heap}`. Ordinary language fences such as `lean`, `heap`,
`grammar`, and `text` remain literal code.

A structured block starts with its kind and stable ID, followed by options and
an authored body. `:status: draft` marks unfinished formalization without
changing the kind. It permits omitted citations; supplied citations keep their
kind checks. A draft without citations has no source selector.

The former `{lean.type}`, `{lean.judgment}`, `{lean.rule}`, and `{obligation}`
forms are rejected with migration diagnostics. An `{example}` paragraph prefix
is also rejected: examples use fenced blocks.

{anchor}`meta.syntax.informational`
A paragraph starting with `{informational}` and a space receives an inline
**Informational** label. Its remaining text keeps normal Markdown formatting.
The marker creates no identity and remains literal in code samples.
```

```{definition} meta.math.source_view
:rust: mdbook-dada/src/lib.rs:selector_header mdbook-dada/src/lib.rs:markdown_heading mdbook-dada/src/lib.rs:render_unit mdbook-dada/src/lib.rs:render
:tests: mdbook-dada/tests/book.rs:leading_declaration_shields_move_to_headers_without_losing_ids_or_body_markup mdbook-dada/tests/book.rs:nonheading_roles_and_nested_diagrams_stay_in_the_markdown_body mdbook-dada/tests/book.rs:unanchored_rendered_blocks_share_named_headers_and_grouped_choices mdbook-dada/tests/units.rs:structured_units_render_identified_headers_and_exact_lean_views mdbook-dada/tests/units.rs:meta_units_show_named_rust_implementation_and_test mdbook-dada/tests/renderer_contracts.rs:view_styles_keep_headers_and_nested_choices_independent

A block's header keeps its identity on the left and its view controls on the
right. Rendered is selected initially. Lean-backed blocks offer Rendered/Lean;
Rust-backed blocks offer Rendered/Rust; diagrams offer Rendered/Facts. Each
selector controls its own block, including when blocks are nested.

A structured unit's ID appears once, as a shield in its header. Draft status
remains visible in both views. In legacy Markdown blocks, leading defining
anchors move to the header; later anchors stay in the body. An unanchored
legacy block shows its kind as a plain label. The source view identifies every
citation and shows its selected text.

The selector supports comparison. It does not judge correspondence or check a
proof. Header arrangement and visibility use the checked-in CSS; the cited
asset test checks those rules without executing a browser.
```

## Authored mathematics

```{definition} meta.math.typesetting
:rust: mdbook-dada/src/lib.rs:protect_math mdbook-dada/src/lib.rs:render_unit mdbook-dada/src/lean.rs:render_authored mdbook-dada/src/lib.rs:escape
:tests: mdbook-dada/tests/book.rs:authored_grammar_keeps_math_and_groups_citations_in_order mdbook-dada/tests/book.rs:authored_math_escapes_html_without_interpreting_placeholders mdbook-dada/tests/book.rs:explicit_math_survives_markdown_and_smart_punctuation_in_prose_and_proof_bodies mdbook-dada/tests/book.rs:explicit_math_is_literal_in_code_links_and_html_and_does_not_define_roles

The renderer preserves authored mathematics. Grammar, judgment, and rule bodies
are raw LaTeX; the renderer supplies display delimiters and does not interpret
Markdown within them. Definition, theorem, lemma, and example bodies are
Markdown and use explicit `\\[` / `\\]` or `\\(` / `\\)` delimiters.

The preprocessor protects explicit math from Markdown escaping and smart
punctuation, retaining TeX row breaks, primes, braces, and underscores. Code,
links, and HTML literal contexts are excluded. Both mathematical text and source
selections are escaped for HTML. MathJax typesets the result in the browser;
the renderer does not translate Lean into mathematics or validate LaTeX as Lean.

{anchor}`meta.syntax.grammar.rendering`
A grammar's ordered citations share one Rendered/Lean selector. Judgment and
rule blocks use the same presentation, with their own authored notation.
```

```{definition} meta.math.runtime
:rust: mdbook-dada/src/lib.rs:protect_math mdbook-dada/src/lean.rs:render_authored
:tests: mdbook-dada/tests/renderer_contracts.rs:pinned_mathjax_configuration_uses_one_loader mdbook-dada/tests/renderer_contracts.rs:view_styles_keep_headers_and_nested_choices_independent
:uses: meta.math.typesetting meta.math.source_view

The renderer emits MathJax delimiters for the runtime configured by
`book.toml` and `theme/mathjax.js`. The bundled loader selects MathJax 4.1.3's
CommonHTML build; mdBook's built-in MathJax loader is disabled. Local previews
and published pages load that same script. Authored display breaks are retained,
and wide mathematical blocks can scroll horizontally.

The loader uses a CDN, so browser typesetting requires network access. The
source text and selectors remain available independently. The tests inspect
configuration and emitted HTML/CSS; they do not guarantee CDN availability or
verify the appearance of every possible formula.
```

```{definition} meta.math.overline.braces
:rust: mdbook-dada/src/lint.rs:check_latex
:tests: mdbook-dada/tests/latex.rs:overbars_require_a_preceding_brace_and_following_literal_space mdbook-dada/tests/latex.rs:grouped_overbars_and_other_control_words_are_allowed mdbook-dada/tests/latex.rs:diagnostics_count_source_lines_including_unicode_and_crlf mdbook-dada/tests/latex.rs:book_build_checks_math_directives_examples_and_literal_tex mdbook-dada/tests/latex.rs:all_book_markdown_follows_latex_conventions

Write an overbar inside a group, as in `{\overline f}`. The command must have an
opening brace immediately before it and a literal ASCII space immediately after
it. A tab or newline does not satisfy the space requirement. Longer command
names are not matches.

The lint checks raw Markdown, including literal TeX samples, and reports a
source path and line number for either violation. A repository test checks all
Markdown below `v2/md/`, including files outside the table of contents. This is
an adjacency check; it does not parse the TeX expression or balance its braces.
```

## Lean selections

```{definition} meta.math.definition.selection
:rust: mdbook-dada/src/lean.rs:select mdbook-dada/src/lean.rs:extract_declaration mdbook-dada/src/lean.rs:has_named_definition_body mdbook-dada/src/lean.rs:definition_source
:tests: mdbook-dada/tests/book.rs:definition_blocks_select_multiple_complete_declarations_and_preserve_markdown mdbook-dada/tests/book.rs:definition_blocks_reject_missing_wrong_kind_and_malformed_citations mdbook-dada/src/lean.rs:tests::definitions_select_complete_equations_structure_literals_and_multiline_bodies mdbook-dada/src/lean.rs:tests::definition_selection_ignores_comment_and_literal_decoys mdbook-dada/src/lean.rs:tests::definitions_reject_unsupported_incomplete_and_ambiguous_sources
:uses: meta.sources.exact_selection

A completed definition selects one or more named `def`, `abbrev`, `structure`,
or `inductive` declarations, in citation order, including their bodies.
Theorems, axioms, anonymous examples, and constructor-only citations are not
valid definition targets.

{anchor}`meta.lean.definitions.extraction`
Extraction recognizes column-zero declarations with indented continuations.
Structures and inductives put `where` on their first line. Definitions may have
multiline signatures and a `:=` body, a `where` body, or indented equation clauses.
Definition abbreviations may have an indented signature and `:=` body.
The scanner masks comments and literal contents to find boundaries, then retains
the original source tokens. A matching word in a comment is not a declaration.

{anchor}`meta.lean.definitions.selection`
A grammar selects `inductive`, `structure`, or `abbrev` declarations. Its type
names are unqualified; type abbreviations put `:=` on their first line. Supported
column-zero mutual inductives can be selected individually, as specified by
{anchor-ref}`meta.sources.exact_selection`.

{anchor}`meta.syntax.grammar.declarations`
A structured grammar has an ID, one or more `:lean:` citations, and authored
LaTeX. Surrounding prose defines its mathematical categories and notation.

{anchor}`meta.syntax.grammar.validation`
Citation lookup checks existence and supported declaration kinds. It does not
parse an independent grammar language, resolve mathematical symbols, or establish
correspondence with Lean.
```

```{definition} meta.math.judgment.selection
:rust: mdbook-dada/src/lean.rs:select mdbook-dada/src/lean.rs:extract_case mdbook-dada/src/lean.rs:render_authored
:tests: mdbook-dada/tests/book.rs:authored_judgments_and_rules_keep_tex_and_show_cited_source mdbook-dada/tests/book.rs:authored_math_requires_one_opening_argument_and_a_body mdbook-dada/tests/book.rs:authored_math_rejects_missing_or_wrong_kind_source_selections mdbook-dada/src/lean.rs:tests::selects_a_case_without_interpreting_its_binders
:uses: meta.sources.exact_selection

A judgment selects one named inductive declaration. Its authored LaTeX presents
the judgment; selecting it does not generate mathematical rules automatically.

{anchor}`meta.math.rule.selection`
A rule selects one `Judgment.constructor` and displays the inductive header and
that constructor's complete source. It does not include sibling constructors.
The author supplies the mathematical premises, conclusion, and rule label.

The selector checks declaration kinds and constructor names. It does not
interpret binder types, classify premises, or require that the declaration's
result is `Prop`.
```

```{definition} meta.math.theorem.selection
:rust: mdbook-dada/src/lean.rs:select mdbook-dada/src/lean.rs:extract_declaration mdbook-dada/src/lean.rs:theorem_source mdbook-dada/src/lib.rs:chapter_roles
:tests: mdbook-dada/tests/book.rs:authored_theorems_show_the_exact_named_statement_and_proof mdbook-dada/tests/book.rs:authored_theorems_select_literal_qualified_names mdbook-dada/tests/book.rs:authored_theorems_reject_wrong_kinds_and_malformed_directives mdbook-dada/tests/book.rs:markdown_proof_blocks_reject_invalid_targets_and_all_nested_proof_kinds mdbook-dada/src/lean.rs:tests::selects_complete_named_theorems_without_comment_or_string_decoys mdbook-dada/src/lean.rs:tests::rejects_wrong_kind_ambiguous_and_incomplete_theorem_selections

A theorem or lemma selects exactly one named Lean `theorem`, including its
statement and `:=` proof body. Definitions, axioms, and anonymous examples are
rejected as targets. Multiline statements use indented continuations; neighboring
declarations are excluded. The distinction between theorem and lemma is the
author's presentation choice.

{anchor}`meta.math.theorem.validation`
The renderer checks source selection, not the proof. Lean compilation and
correspondence review are separate: Lean checks the proof; review compares the
statement's assumptions, quantifiers, and conclusion with the authored claim.
Definition, theorem, lemma, and example bodies cannot nest any of those four
block kinds.
```

```{definition} meta.examples.selection
:rust: mdbook-dada/src/lean.rs:extract_example mdbook-dada/src/lean.rs:example_source mdbook-dada/src/lib.rs:render mdbook-dada/src/lib.rs:chapter_roles
:tests: mdbook-dada/tests/book.rs:linked_examples_preserve_native_markdown_and_select_one_lean_test mdbook-dada/tests/book.rs:linked_example_bodies_index_anchors_and_scope_nested_selectors mdbook-dada/tests/book.rs:linked_examples_fail_on_invalid_citations_bodies_or_nesting mdbook-dada/src/lean.rs:tests::ignores_anchor_decoys_in_strings_block_comments_and_inline_comments mdbook-dada/src/lean.rs:tests::requires_one_complete_anonymous_example mdbook-dada/src/lean.rs:tests::rejects_end_markers_that_cut_off_a_proof_continuation

An example citation selects a region between standalone Lean comments
`-- ANCHOR: name` and `-- ANCHOR_END: name`. That region contains exactly one
anonymous `example` proof, with optional comments and whitespace. The `example`
and following command start at column zero; proof continuations are indented.
The closing marker cannot truncate the proof or hide another command. Markers
are excluded from displayed source. Their name is local to the file, not a
Lean declaration name or a book ID.

{anchor}`meta.syntax.example`
A structured example has an ID, one `:lean:` citation, and an authored Markdown
body. Its header says Example and initially displays the rendered body.

{anchor}`meta.examples.markdown`
The body supports paragraphs, lists, links, code, explicit math, roles, and heap
diagrams. Longer enclosing fences permit literal fenced examples inside it.
The nesting restrictions in {anchor-ref}`meta.math.theorem.selection` still apply.

{anchor}`meta.examples.validation`
Missing, duplicate, or malformed regions, unsupported proof forms, malformed
citations, and empty bodies fail the build. Selecting the test does not elaborate
or run it.
```

```{definition} meta.lean.definitions.navigation
:rust: mdbook-dada/src/lean.rs:read_source mdbook-dada/src/lean.rs:extract_declaration mdbook-dada/src/lean.rs:select mdbook-dada/src/lean.rs:highlighted
:tests: mdbook-dada/tests/book.rs:authored_grammar_rejects_invalid_citations_and_missing_bodies mdbook-dada/tests/book.rs:linked_examples_fail_on_invalid_citations_bodies_or_nesting mdbook-dada/tests/book.rs:authored_theorems_select_literal_qualified_names mdbook-dada/src/lean.rs:tests::qualified_theorem_names_match_only_the_literal_declaration_name mdbook-dada/src/lean.rs:tests::definitions_reject_unsupported_incomplete_and_ambiguous_sources mdbook-dada/tests/renderer_contracts.rs:lean_citations_accept_subdirectories_but_reject_source_root_escapes
:uses: meta.sources.configuration meta.sources.exact_selection

Citations name files relative to the configured Lean source root and may omit
`.lean`. Subdirectories are allowed; escaping the root, including through a
symlink, is rejected. Source views identify each citation and retain its selected
text. Imports, namespaces, and section variables remain in the retained source
context; an excerpt is not a standalone Lean file.

Definition and theorem names may contain dots when that exact name is written
in the declaration. The selector does not infer namespace qualification.

{anchor}`meta.lean.definitions.errors`
Missing files, missing or ambiguous declarations, unsupported extraction forms,
and wrong kinds fail with the citation and target identified. A failed selection
is not silently omitted or presented as complete.

{anchor}`meta.math.citations.validation`
Directive argument counts and nonempty bodies are also checked. These are
syntactic checks; they establish neither mathematical correspondence nor proofs.

{anchor}`meta.math.unsupported`
Unsupported source forms need an extractor extension or a source change before
citation. Attributes, declaration modifiers, nested mutual groups, and nested
commands within a selected declaration are unsupported. New authored LaTeX needs
no corresponding Lean-to-LaTeX translation rule.
```

## Diagrams

```{definition} meta.syntax.heap.nodes
:rust: mdbook-dada/src/graph.rs:identifier mdbook-dada/src/graph.rs:args mdbook-dada/src/graph.rs:label mdbook-dada/src/graph.rs:parse
:tests: mdbook-dada/src/graph.rs:tests::facts_render_unicode_fields_and_reference_kinds mdbook-dada/src/graph.rs:tests::arrays_materialize_uninitialized_slots_and_validate_indices mdbook-dada/src/graph.rs:tests::variable_store_groups_slots_without_becoming_a_reference_target mdbook-dada/src/graph.rs:tests::labels_are_escaped_and_quoted_commas_are_preserved mdbook-dada/tests/renderer_contracts.rs:diagram_forward_references_and_aliases_preserve_distinct_edges

{anchor}`meta.syntax.heap.state`
A heap diagram describes one graph using node declarations and slot assignments.
It does not execute operations. Blank lines and lines beginning with `#` are
ignored; forward references are allowed. Identifiers accept Unicode letters and
digits, with a letter or underscore first. Quoted labels use JSON string escaping,
and quoted arguments may contain commas.

{anchor}`meta.syntax.heap.constructors`
The supported node constructors are `variables()` or `variables("name")`,
`object(Type)` or `object(Type,"name")`, `primitive(value)` or
`primitive(value,"name")`, and `array(length)` or `array(length,"name")`.
There is at most one variable-store group. It is a presentation aid, not an object.

Assignments use `node.field` or `array[index]`. A slot contains `owned(target)`,
`showned(target)`, `shlease(target)`, `lease(edge)`, or `uninitialized()`.
`leased` aliases `lease`; `shared` aliases `shlease`, never `showned`.
Arrays begin with all slots empty.

The legacy borrow, primitive, and array forms are diagram syntax. Their
availability does not introduce them into Given or Shared.
```

```{definition} meta.syntax.heap.validation
:rust: mdbook-dada/src/graph.rs:parse mdbook-dada/src/graph.rs:edge_target
:tests: mdbook-dada/src/graph.rs:tests::bad_facts_fail_instead_of_silently_changing_the_graph mdbook-dada/src/graph.rs:tests::arrays_materialize_uninitialized_slots_and_validate_indices mdbook-dada/src/graph.rs:lease_tests::leases_join_edges_and_shleases_target_objects mdbook-dada/src/graph.rs:cycle_tests::cycles_self_loops_and_disconnected_cycles_render_deterministically mdbook-dada/tests/renderer_contracts.rs:diagram_array_size_boundary_preserves_all_slots
:uses: meta.syntax.heap.nodes

Each node and explicitly assigned slot is declared once. Unknown targets,
duplicate nodes or assignments, invalid projections, multiple variable stores,
and out-of-bounds indices are rejected. Diagram arrays have at most 64 slots;
that is a presentation limit, not a language bound.

Owned, showned, and shlease edges target objects, primitives, or arrays, never
the variable-store group. A lease names an initialized owned or leased edge,
such as `α.f`, `vars.p`, or `items[0]`. Its target may be declared later.

These checks validate diagram structure. Ownership cycles and conflicting owners
are accepted so malformed language states can be illustrated. The parser does
not establish language invariants or infer support edges.
```

```{definition} meta.syntax.heap.rendering
:rust: mdbook-dada/src/graph.rs:render mdbook-dada/src/lib.rs:render mdbook-dada/src/lib.rs:selector_header
:tests: mdbook-dada/tests/book.rs:heap_fences_render_and_preserve_source mdbook-dada/src/graph.rs:tests::facts_render_unicode_fields_and_reference_kinds mdbook-dada/src/graph.rs:lease_tests::leases_join_edges_and_shleases_target_objects mdbook-dada/src/graph.rs:cycle_tests::cycles_self_loops_and_disconnected_cycles_render_deterministically
:uses: meta.math.source_view meta.syntax.heap.validation

A diagram renders each stored reference as a labeled SVG edge. Explicit leases
join their named supporting edge at a junction; object-targeting edges end at the
target's left boundary. Node and edge labels are HTML-escaped. The SVG description
and Facts view retain the input facts.

Layout is deterministic for the same input. It places the variable group to the
left of reachable objects when the graph allows it. It does not add graph edges
or infer lease provenance.
```

```{definition} meta.syntax.heap.routing
:rust: mdbook-dada/src/routing.rs:route mdbook-dada/src/routing.rs:clear mdbook-dada/src/graph.rs:render
:tests: mdbook-dada/src/routing.rs:tests::routes_around_boxes_and_through_column_gaps mdbook-dada/src/graph.rs:cycle_tests::cycles_self_loops_and_disconnected_cycles_render_deterministically mdbook-dada/src/graph.rs:lease_tests::leases_join_edges_and_shleases_target_objects
:uses: meta.syntax.heap.rendering

Diagram edges use horizontal and vertical segments ending in dots. Routing
searches corridors around node rectangles, including gaps within a column, and
penalizes distance and bends. It avoids box interiors; a missing route is an
error. It does not guarantee that distinct edges or their labels never overlap.
Lease junctions identify the explicitly named supporting edge.
```
