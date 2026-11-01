import Unique.Typing
import Unique.Soundness

namespace Dada.Unique.Typing

-- An outer none means failed lookup. A final empty slot is some none.
-- Only a nonempty remaining path requires the selected slot to hold an object.
def readPath (state : State) (object : ObjectId) : Path → Option Slot
  | [] => do
      let _ ← state.objects.lookup object
      return some object
  | field :: rest => do
      let data ← state.objects.lookup object
      let slot ← data.fields.lookup field
      match rest with
      | [] => return slot
      | _ :: _ => do
          let target ← slot
          readPath state target rest

-- Views constrain known paths, while unlisted paths impose no local condition.
-- Positive paths require allocated objects of the declared nominal class.
structure Satisfies (classes : ClassTable) (state : State) (object : ObjectId) (ty : ViewType) : Prop where
  root : ∃ data, (object, data) ∈ state.objects ∧ data.className = ty.className
  positive : ∀ path, Pos classes ty path →
    ∃ target data, readPath state object path = some (some target) ∧
      (target, data) ∈ state.objects ∧
      classAt classes ty.className path = some data.className
  negative : ∀ path, Neg ty path → readPath state object path = some none

-- This nominal condition includes occupied fields hidden by a view.
def FieldsMatchClasses (classes : ClassTable) (state : State) : Prop :=
  ∀ parent data field target, (parent, data) ∈ state.objects →
    (field, some target) ∈ data.fields →
    ∃ declaration targetClass targetData,
      (data.className, declaration) ∈ classes ∧
      (field, targetClass) ∈ declaration.fields ∧
      (target, targetData) ∈ state.objects ∧ targetData.className = targetClass

abbrev PendingValues := List (ObjectId × ViewType)

-- Exact domain equality is extensional: list order does not affect realization.
-- Hidden owners and pending expression results remain in ownership accounting.
structure Realizes (classes : ClassTable) (environment : Environment) (state : State) (pending : PendingValues) : Prop where
  classesWellFormed : classes.WellFormed
  environmentWellFormed : environment.WellFormed classes
  pendingTypes : ∀ object ty, (object, ty) ∈ pending → Admissible classes ty
  ownership : WellFormedWith classes.erase state (pending.map Prod.fst)
  fields : FieldsMatchClasses classes state
  variableDomain : ∀ name,
    name ∈ environment.map Prod.fst ↔ name ∈ state.variables.map Prod.fst
  emptyVariables : ∀ name, (name, none) ∈ environment → (name, none) ∈ state.variables
  initializedVariables : ∀ name ty, (name, some ty) ∈ environment →
    ∃ object, (name, some object) ∈ state.variables ∧ Satisfies classes state object ty
  pendingValues : ∀ object ty, (object, ty) ∈ pending → Satisfies classes state object ty

theorem readPath_nil (state : State) (object : ObjectId) :
    readPath state object [] = (state.objects.lookup object).map (fun _ => some object) := by
  cases found : state.objects.lookup object <;> simp [readPath, found]

theorem readPath_singleton (state : State) (object : ObjectId) (field : FieldName) :
    readPath state object [field] =
      (state.objects.lookup object).bind (fun data => data.fields.lookup field) := by
  simp [readPath]

theorem readPath_empty (object : ObjectId) (path : Path) :
    readPath State.empty object path = none := by
  cases path <;> simp [readPath, State.empty]

theorem Satisfies.weaken (satisfied : Satisfies classes state object source)
    (sourceNormal : Normalized classes source) (targetNormal : Normalized classes target)
    (subtype : Subtype classes source target) : Satisfies classes state object target := by
  obtain ⟨sameClass, positives, negatives⟩ := subtype
  unfold Normalized at sourceNormal targetNormal
  rw [sourceNormal, targetNormal] at positives negatives
  constructor
  · obtain ⟨data, stored, correctClass⟩ := satisfied.root
    exact ⟨data, stored, correctClass.trans sameClass⟩
  · intro path positive
    obtain ⟨result, data, read, stored, correctClass⟩ :=
      satisfied.positive path (positives path positive)
    exact ⟨result, data, read, stored, sameClass ▸ correctClass⟩
  · intro path negative
    exact satisfied.negative path (negatives path negative)

theorem Realizes.empty {classes : ClassTable} (classesWellFormed : classes.WellFormed) :
    Realizes classes [] State.empty [] := by
  constructor
  · exact classesWellFormed
  · simp [Environment.WellFormed]
  · simp
  · exact (WellFormed.empty classes.erase).with_empty
  · simp [FieldsMatchClasses, State.empty]
  · simp [State.empty]
  · simp
  · simp
  · simp

end Dada.Unique.Typing
