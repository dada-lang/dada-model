import Assignment.StoreFields
import Assignment.WriteOwnership
import Assignment.FieldEffects
import Assignment.StoreGarbage
import Shared.TypingBindingSoundness
import Shared.TypingGiveCore

namespace Dada.Assignment
open Shared Shared.Typing

-- Assemble the local environment and all pending roots after a field update.
-- The displaced struct is retained as garbage until the statement collects it.
theorem store_field_preserves_core
    {classes : ClassTable} {environment : Environment} {state result : State}
    {incoming sourceReference : Reference} {ty replacement : ValueType}
    {pending : PendingValues} {root : VariableId} {parent : ObjectId} {field : FieldName}
    {place : Place} {previous : Slot}
    (realized : Realizes classes environment state ((incoming, ty) :: pending))
    (sourceStored : (root, some sourceReference) ∈ state.variables)
    (afterWf : (environment.replace root (some replacement)).WellFormed classes)
    (writable : Writable state place (.field parent field) previous)
    (written : Write state (.field parent field) incoming result)
    (fields : FieldsMatchClasses classes result)
    (sourceAfter : Satisfies classes result sourceReference replacement)
    (otherAfter : ∀ name reference view, name ≠ root →
      (name, some reference) ∈ state.variables →
      Satisfies classes state reference view → Satisfies classes result reference view)
    (pendingAfter : ∀ reference view, (reference, view) ∈ pending →
      Satisfies classes result reference view)
    (displacedTypes : ∀ reference, previous = some reference →
      ∃ view, Admissible classes view ∧ StructType classes view ∧
        Satisfies classes state reference view)
    (displacedAfter : ∀ reference view, previous = some reference →
      Satisfies classes state reference view → Satisfies classes result reference view) :
    ∃ garbage, (∀ reference view, (reference, view) ∈ garbage → StructType classes view) ∧
      Realizes classes (environment.replace root (some replacement)) result (pending ++ garbage) := by
  obtain ⟨garbage, roots, structs, types, values⟩ :
      ∃ garbage : PendingValues,
        garbage.map Prod.fst = previous.toList ∧
        (∀ reference view, (reference, view) ∈ garbage → StructType classes view) ∧
        (∀ reference view, (reference, view) ∈ garbage → Admissible classes view) ∧
        (∀ reference view, (reference, view) ∈ garbage → Satisfies classes result reference view) := by
    cases previous with
    | none => exact ⟨[], rfl, by simp, by simp, by simp⟩
    | some previous =>
      obtain ⟨view, admissible, structTy, satisfied⟩ := displacedTypes previous rfl
      refine ⟨[(previous, view)], rfl, ?_, ?_, ?_⟩
      · intro reference ty member
        have equal : (reference, ty) = (previous, view) := by simpa using member
        cases equal
        exact structTy
      · intro reference ty member
        have equal : (reference, ty) = (previous, view) := by simpa using member
        cases equal
        exact admissible
      · intro reference ty member
        have equal : (reference, ty) = (previous, view) := by simpa using member
        cases equal
        exact displacedAfter previous view rfl satisfied
  refine ⟨garbage, structs, ?_⟩
  have ownership := written.preserves_pending realized.ownership writable
  constructor
  · exact realized.classesWellFormed
  · exact afterWf
  · intro reference view member
    rcases List.mem_append.mp member with member | member
    · exact realized.pendingTypes reference view (List.mem_cons_of_mem _ member)
    · exact types reference view member
  · simpa only [List.map_append, roots] using ownership.perm List.perm_append_comm
  · exact fields
  · intro name
    rw [Environment.replace_keys, written.variableKeys]
    exact realized.variableDomain name
  · intro name member
    rcases Environment.replace_member member with ⟨_, impossible⟩ | ⟨_, old⟩
    · cases impossible
    · exact written.stored_unchanged (place := .variable name) (by simp)
        (realized.emptyVariables name old)
  · intro name view member
    rcases Environment.replace_member member with ⟨rfl, same⟩ | ⟨different, old⟩
    · cases same
      exact ⟨sourceReference, written.stored_unchanged (place := .variable name) (by simp) sourceStored,
        sourceAfter⟩
    · obtain ⟨reference, stored, satisfied⟩ := realized.initializedVariables name view old
      exact ⟨reference, written.stored_unchanged (place := .variable name) (by simp) stored,
        otherAfter name reference view different stored satisfied⟩
  · intro reference view member
    rcases List.mem_append.mp member with member | member
    · exact pendingAfter reference view member
    · exact values reference view member

theorem store_field_preserves
    {classes : ClassTable} {environment : Environment} {state result : State}
    {incoming sourceReference : Reference} {ty sourceType parentType : ValueType}
    {pending : PendingValues} {root : VariableId} {parent : ObjectId} {field : FieldName}
    {place : Place} {previous : Slot} {cutPath : Path}
    {declaration : TypedClass} {fieldType : FieldType}
    (realized : Realizes classes environment state ((incoming, ty) :: pending))
    (sourceMember : (root, some sourceType) ∈ environment)
    (sourceStored : (root, some sourceReference) ∈ state.variables)
    (focused : focus classes sourceType cutPath = some parentType)
    (parentGiven : parentType.permission = .given)
    (parentSatisfied : Satisfies classes state (.owned parent) parentType)
    (declared : classes.lookup parentType.base = some declaration)
    (fieldDeclared : declaration.fields.lookup field = some fieldType)
    (sameType : storageType ty = fieldType)
    (afterWf : (environment.replace root
      (some (replaceView classes sourceType ty (cutPath ++ [field])))).WellFormed classes)
    (writable : Writable state place (.field parent field) previous)
    (written : Write state (.field parent field) incoming result)
    (cut : Route state (incoming :: pending.map Prod.fst) (.variable root) cutPath (.owned parent))
    (replaceable : Replaceable classes.erase state previous) :
    ∃ garbage, (∀ reference view, (reference, view) ∈ garbage → StructType classes view) ∧
      Realizes classes (environment.replace root
        (some (replaceView classes sourceType ty (cutPath ++ [field])))) result (pending ++ garbage) := by
  have beforeWF := realized.ownership
  have afterWF := written.preserves_pending beforeWF writable
  have incomingSatisfied := realized.pendingValues incoming ty (by simp)
  obtain ⟨sourceRef, atSource, sourceSatisfied⟩ := realized.initializedVariables root sourceType sourceMember
  have sameSource := Option.some.inj (member_value_unique beforeWF.variableKeys atSource sourceStored)
  subst sourceRef
  have normal := (Environment.admissible realized.environmentWellFormed sourceMember).2
  have facts := storePathFacts realized.classesWellFormed normal focused parentGiven declared fieldDeclared sameType
  have incomingAfter := write_satisfies_incoming beforeWF afterWF written cut (by simp) incomingSatisfied
  have sourceAfter : Satisfies classes result sourceReference
      (replaceView classes sourceType ty (cutPath ++ [field])) := by
    apply satisfies_replaceView realized.classesWellFormed facts (by simp) sourceSatisfied incomingAfter
      afterWF written.old_object_data
    · intro path slot outside read
      exact (write_readPath_outside beforeWF afterWF written cut sourceStored outside).trans read
    · intro path reference outside read
      exact (write_readPath_outside beforeWF afterWF written cut sourceStored outside).symm.trans read
    · exact write_readPath_installed beforeWF afterWF written cut sourceStored
  apply store_field_preserves_core realized sourceStored afterWf writable written
    (fieldsMatchClasses_write_field beforeWF realized.fields written parentSatisfied incomingSatisfied
      declared fieldDeclared sameType) sourceAfter
  · intro name reference view different member satisfied
    exact write_satisfies_other_variable beforeWF afterWF written cut member different satisfied
  · intro reference view member
    have inPending : reference ∈ pending.map Prod.fst := List.mem_map.mpr ⟨(reference, view), member, rfl⟩
    exact write_satisfies_pending beforeWF afterWF written cut (by simp [inPending])
      (List.mem_append_right _ inPending) (realized.pendingValues reference view (List.mem_cons_of_mem _ member))
  · intro reference same
    have stored : Stored state (.field parent field) (some reference) := same ▸ writable.stored
    obtain ⟨data, dataStored, fieldStored⟩ := stored
    exact field_garbage_type realized parentSatisfied dataStored fieldStored declared fieldDeclared
      (same ▸ replaceable)
  · intro reference view same satisfied
    have stored : Stored state (.field parent field) (some reference) := same ▸ writable.stored
    exact write_satisfies_displaced beforeWF afterWF written cut stored (by simp [same]) satisfied

end Dada.Assignment
