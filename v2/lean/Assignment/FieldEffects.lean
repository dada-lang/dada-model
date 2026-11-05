import Assignment.WriteOwnership
import Assignment.StoreViews

namespace Dada.Assignment
open Shared Shared.Typing

private theorem route_read (wf : WellFormedWith classes state pending)
    (route : Route state pending (.variable root) path reference)
    (atRoot : (root, some rootReference) ∈ state.variables) :
    readPath state rootReference path = some (some reference) := by
  induction route with
  | root owner =>
    cases owner with
    | «variable» member =>
      have same := member_value_unique wf.variableKeys atRoot member
      injection same with same
      subst rootReference
      exact readPath_nil_of_allocated wf ((Route.root (.variable member)).allocated wf)
  | @field oldPath parent data field child previousRoute stored atField ih =>
    exact (readPath_append wf ih [field]).trans (readPath_singleton_of_stored wf ⟨data,stored,atField⟩)

private theorem outside_separate (outside : ¬ (cutPath ++ [field]) <+: path) :
    ∀ pre post, path = pre ++ field :: post → ¬ ([] ++ pre = cutPath) := by
  intro pre post same both
  simp only [List.nil_append] at both
  subst pre
  apply outside
  exact ⟨post, by simpa [List.append_assoc] using same.symm⟩

-- Reads outside the replaced subtree agree in both directions; the backward
-- direction also covers paths hidden by the source's visible view.
theorem write_readPath_outside
    (wf : WellFormedWith classes before pending)
    (afterWf : WellFormedWith classes after afterPending)
    (written : Write before (.field parent field) incoming after)
    (cut : Route before pending (.variable root) cutPath (.owned parent))
    (atRoot : (root, some reference) ∈ before.variables)
    (outside : ¬ (cutPath ++ [field]) <+: path) :
    readPath after reference path = readPath before reference path := by
  have cutAfter := written.parent_route (otherPending := afterPending) wf cut cut (Nat.le_refl _)
  have rootAfter := written.stored_unchanged (place := .variable root) (by simp) atRoot
  apply readPath_eq_of_success
  · intro slot read
    exact write_readPath_frame wf afterWf written cut (.root (.variable atRoot)) read
      (fun pre post same both => outside_separate outside pre post same both.2)
  · intro slot read
    exact write_readPath_back_frame wf afterWf written cutAfter (.root (.variable rootAfter)) read
      (fun pre post same both => outside_separate outside pre post same both.2)

theorem write_readPath_installed
    (wf : WellFormedWith classes before pending)
    (afterWf : WellFormedWith classes after afterPending)
    (written : Write before (.field parent field) incoming after)
    (cut : Route before pending (.variable root) cutPath (.owned parent))
    (atRoot : (root, some reference) ∈ before.variables) :
    readPath after reference (cutPath ++ [field]) = some (some incoming) := by
  have cutAfter := written.parent_route (otherPending := afterPending) wf cut cut (Nat.le_refl _)
  have rootAfter := written.stored_unchanged (place := .variable root) (by simp) atRoot
  have parentRead := route_read afterWf cutAfter rootAfter
  exact (readPath_append afterWf parentRead [field]).trans
    (by simpa [Reference.owned] using readPath_singleton_of_stored (reference := Reference.owned parent) afterWf written.installed)

-- Unaffected roots keep every readable path, even in a cyclic shared subgraph.
theorem write_satisfies_other_variable
    (wf : WellFormedWith classes.erase before pending)
    (afterWf : WellFormedWith classes.erase after afterPending)
    (written : Write before (.field parent field) incoming after)
    (cut : Route before pending (.variable root) cutPath (.owned parent))
    (atRoot : (name, some reference) ∈ before.variables)
    (different : name ≠ root) (satisfied : Satisfies classes before reference ty) :
    Satisfies classes after reference ty := by
  have cutAfter := written.parent_route (otherPending := afterPending) wf cut cut (Nat.le_refl _)
  have rootAfter := written.stored_unchanged (place := .variable name) (by simp) atRoot
  apply satisfies_preserved satisfied written.old_object_data
  · intro path slot read
    exact write_readPath_other wf afterWf written cut (.root (.variable atRoot))
      (by simpa using different) read
  · intro path reached read
    exact write_readPath_back_frame wf afterWf written cutAfter (.root (.variable rootAfter)) read
      (by intro pre post _ both; exact different (RootSite.variable.inj both.1))

theorem write_satisfies_pending
    (wf : WellFormedWith classes.erase before pending)
    (afterWf : WellFormedWith classes.erase after afterPending)
    (written : Write before (.field parent field) incoming after)
    (cut : Route before pending (.variable root) cutPath (.owned parent))
    (oldMember : reference ∈ pending) (newMember : reference ∈ afterPending)
    (satisfied : Satisfies classes before reference ty) :
    Satisfies classes after reference ty := by
  have cutAfter := written.parent_route (otherPending := afterPending) wf cut cut (Nat.le_refl _)
  apply satisfies_preserved satisfied written.old_object_data
  · intro path slot read
    exact write_readPath_other wf afterWf written cut (.root (.pending oldMember)) (by simp) read
  · intro path reached read
    exact write_readPath_back_frame wf afterWf written cutAfter (.root (.pending newMember)) read
      (by intro pre post _ both; cases both.1)

-- The incoming pending root is now below the changed field, and cannot return
-- to its uniquely owned parent. Its view remains exactly the same.
theorem write_satisfies_incoming
    (wf : WellFormedWith classes.erase before pending)
    (afterWf : WellFormedWith classes.erase after afterPending)
    (written : Write before (.field parent field) incoming after)
    (cut : Route before pending (.variable root) cutPath (.owned parent))
    (member : incoming ∈ pending)
    (satisfied : Satisfies classes before incoming ty) :
    Satisfies classes after incoming ty := by
  have cutAfter := written.parent_route (otherPending := afterPending) wf cut cut (Nat.le_refl _)
  obtain ⟨data, stored, atField⟩ := written.installed
  have incomingRoute : Route after afterPending (.variable root) (cutPath ++ [field]) incoming := by
    simpa [Reference.owned] using Route.field cutAfter stored atField
  apply satisfies_preserved satisfied written.old_object_data
  · intro path slot read
    exact write_readPath_other wf afterWf written cut (.root (.pending member)) (by simp) read
  · intro path reached read
    apply write_readPath_back_frame wf afterWf written cutAfter incomingRoute read
    intro pre post _ both
    have lengths := congrArg List.length both.2
    simp only [List.length_append, List.length_singleton] at lengths
    omega

-- A displaced value is retained as a temporary root until the following GC.
theorem write_satisfies_displaced
    (wf : WellFormedWith classes.erase before pending)
    (afterWf : WellFormedWith classes.erase after afterPending)
    (written : Write before (.field parent field) incoming after)
    (cut : Route before pending (.variable root) cutPath (.owned parent))
    (stored : Stored before (.field parent field) (some reference))
    (member : reference ∈ afterPending)
    (satisfied : Satisfies classes before reference ty) :
    Satisfies classes after reference ty := by
  have cutAfter := written.parent_route (otherPending := afterPending) wf cut cut (Nat.le_refl _)
  obtain ⟨data, dataStored, atField⟩ := stored
  have outgoingRoute : Route before pending (.variable root) (cutPath ++ [field]) reference := by
    simpa [Reference.owned] using Route.field cut dataStored atField
  apply satisfies_preserved satisfied written.old_object_data
  · intro path slot read
    exact write_readPath_descendant wf afterWf written cut outgoingRoute (by simp) read
  · intro path reached read
    exact write_readPath_back_frame wf afterWf written cutAfter (.root (.pending member)) read
      (by intro pre post _ both; cases both.1)

end Dada.Assignment
