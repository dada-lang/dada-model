import Assignment.StoreLocal
import Assignment.StoreField
import Assignment.StoreProgress

namespace Dada.Assignment
open Shared Shared.Typing

-- A store exchanges the incoming pending owner with the displaced slot. The
-- latter, if present, is a struct root that the statement collector may discard.
theorem store_preserves
    (stored : store classes before place ty = some after)
    (realized : Realizes classes before.current state ((reference, ty) :: pending))
    (writable : Writable state place target previous)
    (replaceable : Replaceable classes.erase state previous)
    (written : Write state target reference result) :
    ∃ garbage, (∀ ref ty, (ref, ty) ∈ garbage → StructType classes ty) ∧
      Realizes classes after.current result (pending ++ garbage) := by
  have afterWf := (store_wellFormed stored).1
  cases (store_facts stored).2.2 with
  | @«variable» name fixed old _ found _ permitted afterEq =>
    subst after
    cases writable with
    | «variable» member =>
      exact store_local_preserves realized found permitted afterWf (.variable member) written
  | @field base name fixed source parentType declaration fieldType old
      _ found focused given declared fieldDeclared _ sameType _ afterEq =>
    subst after
    cases writable with
    | @field _ sourcePlace parent data _ previous resolved dataStored fieldStored =>
      have sourceMember := Environment.lookup_member found
      have admissible := Environment.admissible realized.environmentWellFormed sourceMember
      obtain ⟨rootRef, atRoot, sourceSatisfied⟩ := realized.initializedVariables _ _ sourceMember
      obtain ⟨actualRoot, actualStored, read⟩ := resolve_readPath realized.ownership resolved
      have sameRoot := Option.some.inj
        (member_value_unique realized.ownership.variableKeys actualStored atRoot)
      subst actualRoot
      have parentSatisfied : Satisfies classes state (.owned parent) parentType :=
        sourceSatisfied.focus realized.classesWellFormed realized.ownership admissible.2 focused read
      exact store_field_preserves realized sourceMember atRoot focused given parentSatisfied declared
        fieldDeclared sameType afterWf (.field resolved dataStored fieldStored) written
        (route_of_resolve resolved) replaceable

-- Both operational existence and preservation quantify over the ordinary
-- checker and runtime relations; no success condition is added to typing.
theorem store_sound
    {classes : ClassTable} {before after : Context} {place : Place}
    {ty : ValueType} {state : State} {reference : Reference} {pending : PendingValues}
    (stored : store classes before place ty = some after)
    (realized : Realizes classes before.current state ((reference, ty) :: pending)) :
    (∃ target previous result, Writable state place target previous ∧
      Replaceable classes.erase state previous ∧ Write state target reference result) ∧
    (∀ target previous result, Writable state place target previous →
      Replaceable classes.erase state previous → Write state target reference result →
      ∃ garbage, (∀ ref ty, (ref, ty) ∈ garbage → StructType classes ty) ∧
        Realizes classes after.current result (pending ++ garbage)) := by
  refine ⟨store_exists stored realized, ?_⟩
  intro target previous result writable replaceable written
  exact store_preserves stored realized writable replaceable written

end Dada.Assignment
