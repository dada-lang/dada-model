# Work in progress

- [Soundness assessment](wip/2026-09-soundness-assessment.md): predicate vocabulary
  migration implemented; constructor, scope, drop, destructor, and branch fixes pending.
- [Test organization](wip/test-anchors.md): discussion proposal; migration not started.
- [Var-pop normalization](wip/var-pop-normalization.md): preceding implementation plan.
- [Vec](wip/vec.md): implementation history and remaining follow-ups.
- [Unsafe code](wip/unsafe.md): historical design notes; see its status caveat.

Vocabulary as of September 25, 2026: `shared` replaces the former `copy` predicate;
use `shared` together with `owned` for the former narrower `shared` predicate.
Any shared permission can be duplicated. The full workspace suite passes
(627 model tests and 7 mdBook preprocessor tests).
