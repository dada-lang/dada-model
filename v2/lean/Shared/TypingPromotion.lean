import Shared.TypingGiveEffects

namespace Dada.Shared.Typing

-- Promotion changes one stored reference, but every route to that slot already
-- has shared access. Existing references therefore retain their observations.
theorem Satisfies.promote_frame (wf : WellFormedWith classes.erase before pending)
    (afterWf : WellFormedWith classes.erase after afterPending)
    (promoted : Promote before source object after)
    (cut : Route before pending cutSite cutPath (.shared object))
    (route : Route before pending site initial reference)
    (satisfied : Satisfies classes before reference ty) :
    Satisfies classes after reference ty := by
  constructor
  · exact satisfied.mode
  · obtain ⟨data, stored, correct⟩ := satisfied.root
    obtain ⟨newData, newStored, same⟩ := promoted.old_object_data reference.object data stored
    exact ⟨newData, newStored, same.trans correct⟩
  · intro path positive
    obtain ⟨target, data, read, stored, correct⟩ := satisfied.positive path positive
    obtain ⟨newData, newStored, same⟩ := promoted.old_object_data target.object data stored
    exact ⟨target, newData, (promote_readPath_eq wf afterWf promoted cut route path).trans read,
      newStored, same ▸ correct⟩
  · intro path negative
    exact (promote_readPath_eq wf afterWf promoted cut route path).trans
      (satisfied.negative path negative)
  · intro path target permission declared read
    rw [promote_readPath_eq wf afterWf promoted cut route path] at read
    exact satisfied.modes path target permission declared read

-- The promoted object's own fields lie below its incoming reference in the
-- allocation order. Their contents and permissions do not change.
theorem Satisfies.promote_target (wf : WellFormedWith classes.erase before pending)
    (afterWf : WellFormedWith classes.erase after afterPending)
    (promoted : Promote before source reference.object after)
    (satisfied : Satisfies classes before reference ty) :
    Satisfies classes after reference ty := by
  constructor
  · exact satisfied.mode
  · obtain ⟨data, stored, correct⟩ := satisfied.root
    obtain ⟨newData, newStored, same⟩ := promoted.old_object_data reference.object data stored
    exact ⟨newData, newStored, same.trans correct⟩
  · intro path positive
    obtain ⟨target, data, read, stored, correct⟩ := satisfied.positive path positive
    obtain ⟨newData, newStored, same⟩ := promoted.old_object_data target.object data stored
    exact ⟨target, newData,
      (promote_readPath_below_eq wf afterWf promoted (Nat.le_refl _) path).trans read,
      newStored, same ▸ correct⟩
  · intro path negative
    exact (promote_readPath_below_eq wf afterWf promoted (Nat.le_refl _) path).trans
      (satisfied.negative path negative)
  · intro path target permission declared read
    rw [promote_readPath_below_eq wf afterWf promoted (Nat.le_refl _) path] at read
    exact satisfied.modes path target permission declared read

private theorem promotion_source_field_general (wf : WellFormedWith classes before pending)
    (resolved : Resolve before place source object permission)
    (shared : permission = .shared)
    (promoted : Promote before source object after) :
    ∃ parent field, source = .field parent field := by
  cases resolved with
  | @«variable» name reference stored =>
    have same := stored_value_unique wf promoted.stored stored
    have modes := congrArg (fun slot => slot.map Reference.mode) same
    simp [Reference.owned, shared] at modes
  | field _ _ _ => exact ⟨_, _, rfl⟩

theorem promotion_source_field (wf : WellFormedWith classes before pending)
    (resolved : Resolve before place source object .shared)
    (promoted : Promote before source object after) :
    ∃ parent field, source = .field parent field :=
  promotion_source_field_general wf resolved rfl promoted

theorem promotion_preserves_variables (wf : WellFormedWith classes before pending)
    (resolved : Resolve before place source object .shared)
    (promoted : Promote before source object after) : after.variables = before.variables := by
  obtain ⟨parent, field, sourceField⟩ := promotion_source_field wf resolved promoted
  cases promoted with
  | «variable» => cases sourceField
  | field => rfl

theorem Realizes.promote (realized : Realizes classes environment before pending)
    (resolved : Resolve before place source object .shared)
    (promoted : Promote before source object after)
    (admissible : Admissible classes ty)
    (target : Satisfies classes after (.shared object) ty) :
    Realizes classes environment after ((Reference.shared object, ty) :: pending) := by
  have afterOwnership := (Give.promote resolved promoted).preserves_pending realized.ownership
  have variables := promotion_preserves_variables realized.ownership resolved promoted
  have cut := route_of_resolve (pending := pending.map Prod.fst) resolved
  constructor
  · exact realized.classesWellFormed
  · exact realized.environmentWellFormed
  · intro root view member
    rcases List.mem_cons.mp member with same | member
    · cases same; exact admissible
    · exact realized.pendingTypes root view member
  · exact afterOwnership
  · exact realized.fields.promote promoted
  · intro name
    rw [variables]
    exact realized.variableDomain name
  · intro name member
    rw [variables]
    exact realized.emptyVariables name member
  · intro name view member
    obtain ⟨root, atRoot, satisfied⟩ := realized.initializedVariables name view member
    exact ⟨root, variables ▸ atRoot,
      satisfied.promote_frame realized.ownership afterOwnership promoted cut
        (.root (.variable atRoot))⟩
  · intro root view member
    rcases List.mem_cons.mp member with same | member
    · cases same; exact target
    · exact (realized.pendingValues root view member).promote_frame realized.ownership
        afterOwnership promoted cut
        (.root (.pending (List.mem_map.mpr ⟨(root, view), member, rfl⟩)))

theorem Realizes.copy (realized : Realizes classes environment state pending)
    (resolved : Resolve state place source object .shared)
    (stored : Stored state source (some (.shared object)))
    (admissible : Admissible classes ty)
    (target : Satisfies classes state (.shared object) ty) :
    Realizes classes environment state ((Reference.shared object, ty) :: pending) := by
  refine { realized with
    pendingTypes := ?_,
    ownership := (Give.copy resolved stored).preserves_pending realized.ownership,
    pendingValues := ?_ }
  · intro root view member
    rcases List.mem_cons.mp member with same | member
    · cases same; exact admissible
    · exact realized.pendingTypes root view member
  · intro root view member
    rcases List.mem_cons.mp member with same | member
    · cases same; exact target
    · exact realized.pendingValues root view member

end Dada.Shared.Typing
