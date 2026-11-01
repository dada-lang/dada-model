import Unique.ViewNormalization
import Unique.ViewIdempotence

namespace Dada.Unique.Typing

-- Normalization changes the spelling, not the initialized/empty observations.
-- The result is well formed, stable under another pass, and independent of the
-- order used to list the input view's entries.
theorem normalization_correct {classes : ClassTable} (classesWf : classes.WellFormed)
    {ty : ViewType} (wf : ty.WellFormed classes) :
    (normalize classes ty).WellFormed classes ∧
    (normalize classes ty).className = ty.className ∧
    (∀ path, Pos classes (normalize classes ty) path ↔ Pos classes ty path) ∧
    (∀ path, Neg (normalize classes ty) path ↔ Neg ty path) ∧
    normalize classes (normalize classes ty) = normalize classes ty ∧
    (∀ entries, ty.entries.Perm entries →
      normalize classes ⟨ty.className, entries⟩ = normalize classes ty) := by
  refine ⟨normalize_wellFormed classesWf wf, rfl,
    normalize_pos_iff classesWf wf, normalize_neg_iff classesWf wf,
    normalize_idempotent classesWf wf, ?_⟩
  intro entries permutation
  exact (normalize_permutation classesWf wf.1 permutation).symm

end Dada.Unique.Typing
