# Shared-copy design context

This note retains the conversation context used in the adversarial review of
`shared.give`. It records an unresolved choice; it does not select a design.

The user's requirement for the second language layer was:

> Then we define a new lean project that has the same grammar, but extended with shared ownership. Now we introduce `share` on values (so `x->share` but not `x.share`). Then we work through what happens to `a.b.c->` when you traverse a shared link (it becomes a shared copy, effectively).

The user later preferred distinct modules in one Lean project and a proved
correspondence between the layers. They also required that correspondence
reviews check whether theorem statements capture intent, leaving proofs to Lean.

During implementation, the assistant identified three possible accounts of
copying a unique field through a shared container:

1. Promote the final stored reference to shared when it is copied.
2. Promote the container's entire owned subtree when sharing the container.
3. Keep stored fields unique and state exclusivity in terms of access paths.

The assistant asked which account the user intended. No answer selecting an
account was received before this review. Implementation proceeded with the first
account, expressly described as provisional. The earlier review of `shared.give`
also acknowledges this in its limitations:

> The comparison is with the explicitly described lazy final-slot promotion design. It is not evidence that the user has approved that provisional semantic choice.

The requirement establishes the shared-copy behavior, but does not by itself
choose how stored ownership modes change. The active text and Lean both use
final-slot promotion. Their agreement is evidence of internal consistency; it
does not resolve the recorded alternatives. No claim is made here that human
approval is generally required for every implementation choice.

Recoverable source for the implemented choice: `md/shared.md`, especially
`shared.give` and `shared.example.share_value`, and `lean/Shared/Step.lean`.
The existing evidence record is retained under
`evidence/records/shared.give/d3089f17e4*.json`; the full digest is available in
the revised review's `supersedes` field. This note is a primary-agent transcript
extract and context summary, not an independently authenticated transcript.
