import Shared.TypingRealization
import Shared.TypingViewLemmas

namespace Dada.Shared.Typing

theorem Satisfies.focus (satisfied : Satisfies classes state reference source)
    (classesWf : classes.WellFormed) (wf : WellFormedWith classes.erase state pending)
    (normal : Normalized classes source)
    (focused : focus classes source path = some result)
    (read : readPath state reference path = some (some target)) :
    Satisfies classes state target result := by
  have observations := focus_observations classesWf normal focused
  obtain ⟨permission, declared, samePermission⟩ := focus_permission focused
  constructor
  · rw [samePermission]
    exact satisfied.modes path target permission declared read
  · obtain ⟨target', data, read', member, correct⟩ := satisfied.positive path observations.positive
    have same : target' = target := by simpa [read] using read'.symm
    subst target'
    exact ⟨data, member, by simpa [observations.className] using correct.symm⟩
  · intro suffix known
    obtain ⟨resultReference, data, completeRead, member, correct⟩ :=
      satisfied.positive _ (observations.positives suffix known)
    refine ⟨resultReference, data, (readPath_append wf read suffix).symm.trans completeRead, member, ?_⟩
    simpa [Unique.Typing.classAt_append, observations.className] using correct
  · intro suffix known
    exact (readPath_append wf read suffix).symm.trans
      (satisfied.negative _ (observations.negatives suffix known))
  · intro suffix reached tailPermission tailDeclared tailRead
    have completeDeclared : declaredPermission classes source.nominal.className (path ++ suffix) =
        some (permission.comp tailPermission) := by
      rw [declaredPermission_append observations.className]
      change declaredPermission classes source.nominal.className path = some permission at declared
      simp [declared, tailDeclared]
    have completeRead := (readPath_append wf read suffix).trans tailRead
    have mode := satisfied.modes _ _ _ completeDeclared completeRead
    simpa [samePermission, Perm.comp_assoc] using mode

end Dada.Shared.Typing
