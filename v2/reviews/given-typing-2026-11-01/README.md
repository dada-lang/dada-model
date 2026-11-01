# Given typing annotation review — 2026-11-01

This records a review of a Markdown design draft. It is not a Lean proof or an
affirmative correspondence decision. [inputs.json](inputs.json) identifies the
examined inputs, their hashes, and retained source snapshots. Editing those
sources makes this review historical; changing hashes alone cannot renew it.

## Intent and scope

The user's nine browser comments requested whole-class shorthand, nonoverlapping
views, normalization, clearer move notation and examples, writing-style tenets,
and a future generic-view constructor example. The later normalization comment
refines the earlier suggestion to reject noncanonical views: expanded views are
accepted, then normalized. Overlapping paths remain ill formed.

The parent authored the typing revisions and integrated navigation and policy
links. Agent /root/normalization_audit reviewed the design and both semantic
chapters in full. Agent /root/writing_tenets authored the style guide, then
reviewed the typing chapter through line 450 and the complete future-extension
chapter against it. Agent /root/generic_views_future authored the future
extension. These agents shared the conversation and some contributed to the
design they reviewed; this is not a blind independent audit.

## Conclusion and reasoning

No remaining semantic inconsistency was found in the revised draft.
Formalization and proofs remain pending.

- The formal type always contains a view. Bare C abbreviates the positive
  empty-path view, so whole values need no separate type constructor.
- Collapsing all positive siblings preserves the known paths. Unknown or
  negative children prevent collapse. The finite input paths bound the
  procedure even with recursive class declarations.
- Empty classes require care: retaining a positive entry preserves the fact
  that an object exists. A missing entry cannot be manufactured by vacuous
  sibling collapse. Only the already-known root permits the empty-view case.
- Focus preserves the residual view. Emptying expands along the target path,
  replaces that subtree with a negative entry, and then normalizes. It retains
  sibling information. Type comparisons use normal forms and observation
  inclusion, rather than inclusion of written entries.
- The constructor rule still requires whole arguments. The generic-view
  signature is a separate future proposal; prefixing an empty view cannot yet
  express an initialized field with a wholly hidden interior.

The narrative review found the new examples in dependency order and no new
undefined symbols. Its one copyedit removed a repeated sentence in the
emptying algorithm; the semantic reviewer rechecked that final unit.

This review did not reassess the entire operational semantics, prove
normalization properties, or compare the draft typing rules with Lean.
No new typing declarations exist in Lean.

## Mechanical checks

The parent ran `just book-v2` successfully and the 39 renderer book tests passed.
`git diff --check` passed. Browser inspection found no MathJax errors in the
typing or future-extension chapter and verified the new navigation links.
[preview.png](preview.png) retains the normalization example.

The [evidence status](status.txt) command exited with status 1: 27 draft units
and 41 stale existing decisions. The new style guide is an explicit review
context input and future extensions is a strict chapter. Drafts intentionally
remain ineligible for affirmative correspondence. Existing records were not
approved, replaced, or refreshed.
