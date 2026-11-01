# Adversarial narrative review of v2

Reviewer stance: a PL-semantics expert encountering Dada for the first time. Read the root and v2 AGENTS instructions and every Markdown chapter listed in v2/md/SUMMARY.md. Reviewed the current workspace, including uncommitted files. This is a narrative and specification-clarity review, not a Lean/prose correspondence verdict or proof audit. No reviewed inputs were changed; no build or proof check was run.

## Overall judgment

The Given and Shared chapters have a substantially clearer account than the older heap draft: their syntax, operational cases, examples, and invariant statements are mostly intelligible without opening Lean. The Shared give table is especially useful. Nevertheless, the book's default reading path is organized around maintaining the repository rather than understanding the language. Within the semantic material, the reader repeatedly receives representation details and qualifications before being told what behavior those details explain. The older draft then repeats basic consequences and verification commentary until the genuinely interesting ownership and borrowing choices are hard to distinguish from routine implementation facts.

The most useful revision is structural, not a sentence-by-sentence polishing pass: give the semantics its own primary reading path, introduce each feature through its intended result and one small example, and move verification machinery and supporting lemmas out of that path. Preserve explicit scope distinctions and pending claims, but state each limitation once at the point where it changes the reader's interpretation.

## Ranked findings

### 1. The default reading path makes the reader learn the specification infrastructure before the language

Severity: high narrative/architecture issue; not a semantic error.

Locations: v2/md/SUMMARY.md:3–14; v2/md/introduction.md:14–26,43–64; v2/md/repo/spec-system.md:1–799.

The first chapter is “About this repository,” followed by seven repository-method chapters before “About Dada.” The system-design chapter alone is 799 source lines; those seven method chapters total 1,372 source lines. The opening chapter prioritizes the AI-assisted process and explains the distinct roles of proof, review, and rendering twice before “Where to begin” first directs the reader toward more repository methods. This is a very large answer to “how was this document made?” before an answer to “what does Dada do?” A new PL expert has no reason yet to care about the evidence system, and the named-unit grammar looks like a prerequisite for reading the semantics.

Suggestion: make “Dada and the scope of this model” the entry point, then Given, Shared, and the separately marked heap draft. Put “Contributing to this specification” after the semantics or in an appendix. The entry point needs only one short statement that the English/math account stands alone and source selectors expose Lean. Link the workflow for readers who want it. Keep the language goals near the introduction; they explain design choices rather than author procedure.

### 2. Neither incremental chapter opens by stating the behavior it exists to explain

Severity: high narrative issue, with a terminology consequence.

Locations: v2/md/given.md:3–51,61–64,112–129,138–183; v2/md/shared.md:3–39,49–65,83–127,160–212.

Given opens with class-field ordering, a full state triple, natural-number identities, freshness, and storage-place lookup. Only at line 118 does it plainly explain that giving transfers the reference and empties the source; the first execution starts at line 151. “Owning reference” is used at lines 28–29 without first explaining the reader-facing property that makes ownership important. Shared likewise restates the state representation before explaining its genuinely new choice: the same give syntax moves on a unique route and copies on a route containing sharing, promoting the final slot if necessary. A reader can learn the data structures while still lacking the question they answer.

Suggestion: open Given with a short definition of ownership and give, then the existing Token/Box execution (or its first two steps), then introduce slots/state and formal rules to explain the example. Open Shared with the contrast in behavior: multiple shared owners can refer to the same object; giving through shared access preserves the source; a shared link anywhere in a path changes what a later give can do. Put the existing three-row give table early. The complete standalone class/state definitions can follow without being deleted.

Candidate concise opening for Given, subject to normal correspondence review if adopted: “This fragment studies transfer of ownership. Every object has one owning reference, stored in a variable or another object's field. Giving a place, `p→`, moves its reference to the result and leaves that place empty. Construction moves its arguments into the new object's fields.” Qualify the universal property as a property of reachable/well-formed states in the formal statement, rather than silently asserting it for arbitrary states.

Candidate concise opening for Shared: “Sharing allows several owning references to the same object. Giving through unique access moves a reference; giving through shared access returns a shared copy and leaves the source initialized. A shared reference anywhere along a path makes the whole access shared.” Then explain that `p→share` gives first and converts the resulting value; it does not preserve a unique source.

### 3. The full heap's claimed operation status contradicts the chapter it introduces

Severity: high specification/status inconsistency.

Locations: v2/md/operations.md:416–419; compare v2/md/place-operations.md:17–22,45–50,252–256 and v2/md/state.md:314–380.

The end of Operations says the next chapter “defines transitions for give, lease, share, and drop” and that “Borrow invalidation ... remain[s] to be specified.” The next chapter explicitly says the complete path operations remain to be defined; it provides supporting storage and lease effects. Borrow invalidation was already defined, illustrated, and cited in the state chapter. These claims are not just overlong caveats: they disagree about what exists. A reader cannot tell which statements are definitive semantics, which are proved helper relations, and which are plans.

Suggestion: replace this bridge with the exact current boundary: “The next chapter defines reference movement, direct borrowing, invalidation, and release effects. Their composition into complete path operations and scope cleanup is still pending.” Distinguish invalidation policy, which exists, from its integration with writes and destruction, which is pending. Audit other “checked”/“remaining” summaries against this single boundary.

### 4. Full-heap ‘undefined behavior’, ‘fault’, and failed resolution are not given one consistent reader-facing contract

Severity: high semantic ambiguity; do not fix merely by substituting synonyms.

Locations: v2/md/state.md:353–359,372–379,483–490; v2/md/operations.md:52–57; v2/md/properties.md:197–202,264–274; v2/md/place-operations.md:180–184; v2/md/examples.md:132–150,163–172; contrast v2/md/given.md:132–135 and v2/md/shared.md:155–157.

The small languages explicitly define stuckness. The heap says invalid lease use is “undefined behavior,” gives examples whose resolution check fails, and elsewhere says the same access “must fault.” But Operations explicitly leaves the fault representation and observable state unspecified, and says absence of a transition is not itself a definition of fault. In PL semantics these are materially different contracts: UB can remove guarantees, a fault can be an explicit observable result, and stuckness can indicate missing or rejected rules. The current text lets the reader substitute their own interpretation.

Suggestion: state a single failure-status convention at the start of the heap draft. Separate (a) successful effects currently formalized, (b) checks that fail, and (c) intended source-level fault/UB policy still awaiting execution semantics. Keep “must fault” only for an explicitly proposed contract until its meaning is fixed. If invalid-use UB is already a chosen policy, say what that classification does and does not entail for the current relational model; do not present a failed resolve judgment as an established fault transition.

### 5. The full heap puts metatheory before the transitions and transitions inside the state chapter

Severity: high narrative/order issue.

Locations: v2/md/SUMMARY.md:15–21; v2/md/heap.md:23–39; v2/md/state.md:235–437,439–573; v2/md/properties.md:49–120,140–175; v2/md/operations.md:10–27; v2/md/place-operations.md:82–256.

The advertised sequence is state, invariants/proofs, operations, examples. The invariants chapter states preservation for Heap.Step and MachineStep, defines execution reachability, and proves move preservation before those relations are introduced in the normal reading order. Meanwhile State spends roughly 200 lines on lease allocation, invalidation, cleanup, their examples, and lemmas before completing well-formedness. This is neither consistently state-first nor behavior-first; it makes the reader carry several unnamed future mechanisms while moving back and forth between levels.

Suggestion: state vocabulary and the intended ownership/borrow behavior first; explain successful operations next; put well-formedness and preservation after the operations they quantify over. Move lease allocation/invalidation/cleanup together into the operations part, leaving the state chapter with what a lease node records. Give readers one small complete supported execution near the beginning; keep explicitly proposed executions in a separate section. A compact local invariant may precede a rule when needed to state it, but full metatheory should follow the transition definition.

### 6. The transition from Shared to the heap draft silently resets several semantic conventions

Severity: medium-to-high semantic orientation issue; the book does say the models are separate, so this is not a claim that it falsely proves their correspondence.

Locations: v2/md/heap.md:3–21; v2/md/given.md:37–41,74–83; v2/md/shared.md:24–39,67–74,250–264; v2/md/state.md:11–16,76–87,154–167,183–193; v2/md/operations.md:259–270,408–414.

The single disclaimer that this is a separate model is necessary but insufficient after two chapters presented as incremental layers. Fresh-variable let bindings become explicit slot allocation/deallocation; class-tagged initialized constructors become untyped aggregate shapes with empty fields; monotonically increasing object IDs become identities absent only from the current map; shared/unique ownership modes become access modes orthogonal to leasing. Even `p` changes from a source route to a selected runtime slot. An expert naturally tries to reuse the prior definitions and theorem hypotheses, but must reverse-engineer what changed.

Suggestion: a short bridge table at heap.md should identify these deliberate differences and say that the heap is a design reference for later layers, not the next proved language extension. It should tell readers precisely which previous intuitions remain useful and which state/syntax conventions are being replaced. Do not repeat the complete definitions there.

### 7. Borrowing is introduced through its metadata before its operational purpose; ‘unique’ invites the wrong intuition

Severity: medium conceptual/terminology issue.

Locations: v2/md/state.md:5–16,76–87,195–233,235–276,294–311,314–359,524–525.

The reader encounters a lease store, optional LeaseId, roots/subleases, multiple parents, and validity before receiving a compact explanation of the distinguishing Dada behavior. “Unique borrowing” may suggest exclusive existence or Rust's exclusivity discipline, but the direct-borrow example retains the unique owner and unique borrow, and later writes revoke dependents dynamically. The text eventually says unique owners may coexist with borrows, but that observation arrives at line 525. A multi-parent graph example demonstrates reachability mechanics without saying what source access would require those dependencies; complete path composition is pending.

Suggestion: start borrowing with three short points: owners keep objects alive; borrows permit access while a lease remains valid; writes can revoke dependent borrows without removing their stored handles. Explain at first use that unique mode supplies write authority, not the absence of all other handles. Show the supported owner → unique borrow → shared reborrow example, then derive root/parent/validity metadata from it. Mark the need for multiple parents as a representation intended for composed paths whose rule remains open; do not invent a complete source scenario to make the graph feel justified.

### 8. Verification commentary and trivial proof outlines swamp the semantic signal

Severity: medium editorial issue, widespread.

Locations: v2/md/introduction.md:22–26,43–53; v2/md/repo/how-it-works.md:18–46; v2/md/repo/spec-system.md:17–21,72–93,128–180,378–386,510–533,670–677; v2/md/operations.md:133–149,177–213,386–414; v2/md/state.md:170–181,600–610; v2/md/place-operations.md:72–79,106–111,129–154; v2/md/examples.md:3–7,15–18,52–61.

Important distinctions between citations, Lean checking, and review are repeatedly restated instead of explained once and then relied on. The semantic chapters also recite helper theorem names, Lean Array.replicate, hidden proof arguments, “the Lean case checks complete successor states,” and proofs that allocation pushes or that an empty slot contains no reference. These are not wrong; they are poor competition for the actual design choices. The reader can easily mistake supporting implementation lemmas for the main results because they receive similar visual weight.

Suggestion: one “How to read this specification” paragraph and one contributor reference explain the trust boundary. Keep implementation/test names in source views or contributor documentation. In the semantic narrative, keep proofs/theorems that teach a nontrivial property (rooted reachability, uniqueness, preservation, correspondence), and collapse direct restatements of a rule into one sentence. Preserve local limitations where they change the claim, such as incomplete destruction integration. This should shorten the book while increasing precision, not hide evidence gaps.

### 9. Some immediate terminology/notation mismatches interrupt an otherwise self-contained account

Severity: lower, concrete clarity fixes.

Locations: v2/md/state.md:618–625 versus v2/md/place-operations.md:7–14; v2/md/examples.md:119–127,153–154; v2/md/SUMMARY.md:13–14 versus v2/md/shared.md:297–305; v2/md/appendices/older-versions.md:21–23.

The state chapter defines `a` as an access path and `π` as one projection, then the operation grammar uses `π` as the whole path without introducing that change. The proposed-execution table abruptly uses `showned`, and a later paragraph uses `shlease`; these renderer/internal abbreviations have no advantage over “shared owner” and “shared borrow” in the semantic prose. The layer alternates between “Share” and “Shared,” while the old appendix still describes all of v2 as a “partial heap-model draft,” omitting the new complete small-language fragments. None alone is fatal, but together they encourage the reader to search for distinctions that are probably accidental.

Suggestion: use one path metavariable consistently within the heap model, expand ownership abbreviations in prose/tables, choose one chapter/layer name, and update the appendix's scope sentence. This is a cleanup after the structural revision, not a substitute for it.

## Proposed concise outline

1. **Dada and this model.** One paragraph of language motivation; one compact scope statement listing the two established fragments and the separate incomplete heap draft. One optional link explains source selectors and checking.
2. **Given: transferring ownership.** Intended ownership property → a three-statement Token/Box program → objects/references/slots → places and give → construction/execution/failure → the formal state → invariants and preservation. Keep fresh-ID representation where its invariant first needs it.
3. **Shared: copying ownership.** Why copies matter → value sharing versus borrowing → give's three cases and one concrete execution → route-sensitive access and promotion → state/syntax/rules → ownership preservation → concise conservative-extension theorem, with embedding detail available after it.
4. **Full heap draft: design reference for later layers.** A bridge table of differences and a single status key. Owners/borrowers and dynamic invalidation first. Then state vocabulary; supported allocation/move/direct-borrow/invalidation/cleanup operations; meaningful invariant results; proposed composition/destruction/fault scenarios; open choices. Avoid presenting helper storage relations as completed source-language operations.
5. **Contributing to the specification.** How claims relate to Lean and review; short authoring guide; review procedure; layer-extension protocol. The detailed renderer/evidence specification and pilot are reference subsections/appendices, not the language introduction.
6. **Historical appendix.** v1 and its relation to current work.

## Definition-writing pattern

For each concept, prefer: purpose (one sentence), behavior (one or two sentences), then notation/rule. For an operation: input/preconditions, result, exact state changes, failure status. Put representation/proof mechanics after the reader can predict a concrete example.

Examples of desired concise definitions, not edits or established new claims:

- “A slot is a variable or object field that is either empty or holds one reference.”
- “A place expression follows fields from a variable to select a slot.”
- “Giving transfers a reference on a unique route. On a shared route it returns a shared copy; if the selected reference is still unique, that slot is promoted before copying.”
- “A lease records the dependencies under which a borrow may be used. Revoking a lease also revokes dependent leases; stored handles may remain after revocation.”
- “An object is live when an owning path reaches it from a variable.” Follow with the actual invariant and theorem rather than immediate implementation details.

Keep the late-bound distinctions that are genuinely valuable: a selected slot is not its target object; ownership occurrences are not entire access paths; shared ownership is not a shared borrow; preserving ownership counts is weaker than rooted liveness; successful transition rules do not automatically define fault behavior. These should be taught once with examples, then used consistently.
