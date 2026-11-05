import Assignment.WriteOwnership
import Assignment.ContextLemmas

namespace Dada.Assignment
open Shared Shared.Typing

theorem Write.variable_objects (written : Write before (.variable name) incoming after) :
    before.objects = after.objects := by
  cases written
  rfl

-- Replacing a local changes no heap paths. Its old struct reference remains a
-- temporary root until the statement's collection step discards that root.
theorem store_local_preserves {environment : Environment} {previous : Slot}
    (realized : Realizes classes environment state ((incoming, ty) :: pending))
    (found : environment.lookup name = some description)
    (permitted : replaceable classes description = true)
    (afterWf : (environment.replace name (some ty)).WellFormed classes)
    (writable : Writable state (.variable name) (.variable name) previous)
    (written : Write state (.variable name) incoming result) :
    ∃ garbage, (∀ reference view, (reference, view) ∈ garbage → StructType classes view) ∧
      Realizes classes (environment.replace name (some ty)) result (pending ++ garbage) := by
  have atDescription := Environment.lookup_member found
  obtain ⟨garbage, roots, structs, types, values⟩ :
      ∃ garbage : PendingValues,
        garbage.map Prod.fst = previous.toList ∧
        (∀ reference view, (reference, view) ∈ garbage → StructType classes view) ∧
        (∀ reference view, (reference, view) ∈ garbage → Admissible classes view) ∧
        (∀ reference view, (reference, view) ∈ garbage → Satisfies classes state reference view) := by
    cases description with
    | none =>
      have empty := realized.emptyVariables name atDescription
      have same := stored_value_unique realized.ownership writable.stored
        (show Stored state (.variable name) none from empty)
      subst previous
      exact ⟨[], rfl, by simp, by simp, by simp⟩
    | some oldType =>
      obtain ⟨oldReference, stored, satisfied⟩ := realized.initializedVariables name oldType atDescription
      have same := stored_value_unique realized.ownership writable.stored
        (show Stored state (.variable name) (some oldReference) from stored)
      subst previous
      refine ⟨[(oldReference, oldType)], rfl, ?_, ?_, ?_⟩
      · intro reference view member
        have equal : (reference, view) = (oldReference, oldType) := by simpa using member
        cases equal
        simpa [replaceable] using permitted
      · intro reference view member
        have equal : (reference, view) = (oldReference, oldType) := by simpa using member
        cases equal
        exact Environment.admissible realized.environmentWellFormed atDescription
      · intro reference view member
        have equal : (reference, view) = (oldReference, oldType) := by simpa using member
        cases equal
        exact satisfied
  refine ⟨garbage, structs, ?_⟩
  have sameObjects := written.variable_objects
  have ownership := written.preserves_pending realized.ownership writable
  constructor
  · exact realized.classesWellFormed
  · exact afterWf
  · intro reference view member
    rcases List.mem_append.mp member with member | member
    · exact realized.pendingTypes reference view (List.mem_cons_of_mem _ member)
    · exact types reference view member
  · simpa only [List.map_append, roots] using ownership.perm List.perm_append_comm
  · intro parent data field target stored atField
    obtain ⟨declaration, fieldType, targetData, declared, declaredField, targetStored, correct⟩ :=
      realized.fields parent data field target (sameObjects ▸ stored) atField
    exact ⟨declaration, fieldType, targetData, declared, declaredField, sameObjects ▸ targetStored, correct⟩
  · intro localName
    rw [Environment.replace_keys, written.variableKeys]
    exact realized.variableDomain localName
  · intro localName member
    rcases Environment.replace_member member with ⟨_, impossible⟩ | ⟨different, old⟩
    · cases impossible
    · exact written.stored_unchanged (place := .variable localName)
        (by intro same; exact different (StoragePlace.variable.inj same))
        (realized.emptyVariables localName old)
  · intro localName view member
    rcases Environment.replace_member member with ⟨rfl, same⟩ | ⟨different, old⟩
    · cases same
      exact ⟨incoming, written.installed,
        (realized.pendingValues incoming ty (List.mem_cons_self ..)).same_objects sameObjects⟩
    · obtain ⟨reference, stored, satisfied⟩ := realized.initializedVariables localName view old
      exact ⟨reference, written.stored_unchanged (place := .variable localName)
        (by intro same; exact different (StoragePlace.variable.inj same)) stored,
        satisfied.same_objects sameObjects⟩
  · intro reference view member
    rcases List.mem_append.mp member with member | member
    · exact (realized.pendingValues reference view (List.mem_cons_of_mem _ member)).same_objects sameObjects
    · exact (values reference view member).same_objects sameObjects

end Dada.Assignment
