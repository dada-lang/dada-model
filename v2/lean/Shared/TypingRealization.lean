import Shared.Typing
import Shared.TypingPaths

namespace Dada.Shared.Typing

-- A view describes access from this reference. Different aliases can expose
-- different views of the same object, but all routes obey declared permissions.
structure Satisfies (classes : ClassTable) (state : State) (reference : Reference) (ty : ValueType) : Prop where
  mode : reference.mode = ty.permission.toMode
  root : ∃ data, (reference.object, data) ∈ state.objects ∧ data.className = ty.nominal.className
  positive : ∀ path, Pos classes ty path →
    ∃ target data, readPath state reference path = some (some target) ∧
      (target.object, data) ∈ state.objects ∧
      Unique.Typing.classAt classes.nominal ty.nominal.className path = some data.className
  negative : ∀ path, Neg ty path → readPath state reference path = some none
  modes : ∀ path target permission,
    declaredPermission classes ty.nominal.className path = some permission →
    readPath state reference path = some (some target) →
    target.mode = (ty.permission.comp permission).toMode

-- Nominal field correctness also covers fields hidden by a view.
def FieldsMatchClasses (classes : ClassTable) (state : State) : Prop :=
  ∀ parent data field target, (parent, data) ∈ state.objects →
    (field, some target) ∈ data.fields →
    ∃ declaration fieldType targetData,
      (data.className, declaration) ∈ classes ∧
      (field, fieldType) ∈ declaration.fields ∧
      (target.object, targetData) ∈ state.objects ∧ targetData.className = fieldType.className

abbrev PendingValues := List (Reference × ValueType)

structure Realizes (classes : ClassTable) (environment : Environment) (state : State) (pending : PendingValues) : Prop where
  classesWellFormed : classes.WellFormed
  environmentWellFormed : environment.WellFormed classes
  pendingTypes : ∀ reference ty, (reference, ty) ∈ pending → Admissible classes ty
  ownership : WellFormedWith classes.erase state (pending.map Prod.fst)
  fields : FieldsMatchClasses classes state
  variableDomain : ∀ name,
    name ∈ environment.map Prod.fst ↔ name ∈ state.variables.map Prod.fst
  emptyVariables : ∀ name, (name, none) ∈ environment → (name, none) ∈ state.variables
  initializedVariables : ∀ name ty, (name, some ty) ∈ environment →
    ∃ reference, (name, some reference) ∈ state.variables ∧ Satisfies classes state reference ty
  pendingValues : ∀ reference ty, (reference, ty) ∈ pending →
    Satisfies classes state reference ty

theorem Satisfies.weaken (satisfied : Satisfies classes state reference source)
    (sourceNormal : Normalized classes source) (targetNormal : Normalized classes target)
    (subtype : Subtype classes source target) : Satisfies classes state reference target := by
  obtain ⟨samePermission, sameClass, positives, negatives⟩ := subtype
  unfold Normalized Unique.Typing.Normalized at sourceNormal targetNormal
  rw [sourceNormal, targetNormal] at positives negatives
  constructor
  · exact satisfied.mode.trans (congrArg Perm.toMode samePermission)
  · obtain ⟨data, stored, correct⟩ := satisfied.root
    exact ⟨data, stored, correct.trans sameClass⟩
  · intro path positive
    obtain ⟨result, data, read, stored, correct⟩ := satisfied.positive path (positives path positive)
    exact ⟨result, data, read, stored, sameClass ▸ correct⟩
  · intro path negative
    exact satisfied.negative path (negatives path negative)
  · intro path result permission declared read
    rw [← samePermission]
    exact satisfied.modes path result permission (sameClass ▸ declared) read

theorem Realizes.empty {classes : ClassTable} (classesWellFormed : classes.WellFormed) :
    Realizes classes [] State.empty [] := by
  constructor
  · exact classesWellFormed
  · simp [Environment.WellFormed]
  · simp
  · exact (WellFormed.empty classes.erase).with_pending
  · simp [FieldsMatchClasses, State.empty]
  · simp [State.empty]
  · simp
  · simp
  · simp

theorem Realizes.perm (realized : Realizes classes environment state pending)
    (permutation : pending.Perm other) : Realizes classes environment state other := by
  refine { realized with
    pendingTypes := ?_, ownership := realized.ownership.perm (permutation.map Prod.fst),
    pendingValues := ?_ }
  · intro reference ty member
    exact realized.pendingTypes reference ty (permutation.mem_iff.mpr member)
  · intro reference ty member
    exact realized.pendingValues reference ty (permutation.mem_iff.mpr member)

theorem Realizes.weaken_pending
    (realized : Realizes classes environment state ((reference, ty) :: pending))
    (admissible : Admissible classes other) (subtype : Subtype classes ty other) :
    Realizes classes environment state ((reference, other) :: pending) := by
  have original := realized.pendingTypes reference ty (by simp)
  refine { realized with pendingTypes := ?_, pendingValues := ?_ }
  · intro root view member
    rcases List.mem_cons.mp member with equal | member
    · cases equal; exact admissible
    · exact realized.pendingTypes root view (List.mem_cons_of_mem _ member)
  · intro root view member
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      exact (realized.pendingValues reference ty (by simp)).weaken original.2 admissible.2 subtype
    · exact realized.pendingValues root view (List.mem_cons_of_mem _ member)

theorem Realizes.next_fresh (realized : Realizes classes environment state pending) :
    ObjectId.mk state.nextId ∉ state.objects.map Prod.fst := by
  intro member
  obtain ⟨⟨object, data⟩, stored, same⟩ := List.mem_map.mp member
  dsimp at same
  subst object
  exact Nat.lt_irrefl _ (realized.ownership.bounds _ _ stored)

theorem Satisfies.share (satisfied : Satisfies classes state reference ty) :
    Satisfies classes state (.shared reference.object) ty.shared := by
  constructor
  · rfl
  · exact satisfied.root
  · intro path known
    obtain ⟨target, data, read, stored, correct⟩ := satisfied.positive path known
    refine ⟨.shared target.object, data, ?_, stored, correct⟩
    have sharedRead := readPath_enter state .shared reference path
    simpa [read] using sharedRead
  · intro path known
    have sharedRead := readPath_enter state .shared reference path
    simpa [satisfied.negative path known] using sharedRead
  · intro path target permission _ read
    rw [← enter_shared reference, readPath_enter] at read
    obtain ⟨slot, _, mapped⟩ := Option.map_eq_some_iff.mp read
    obtain ⟨old, _, equal⟩ := Option.map_eq_some_iff.mp mapped
    subst target
    cases old.mode <;> cases permission <;> rfl

theorem Realizes.share_pending
    (realized : Realizes classes environment state ((reference, ty) :: pending))
    (structTy : StructType classes ty) :
    Realizes classes environment state ((Reference.shared reference.object, ty.shared) :: pending) := by
  refine { realized with
    pendingTypes := ?_, ownership := realized.ownership.share_result,
    pendingValues := ?_ }
  · intro root view member
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      exact (realized.pendingTypes reference ty (by simp)).share structTy
    · exact realized.pendingTypes root view (List.mem_cons_of_mem _ member)
  · intro root view member
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      exact (realized.pendingValues reference ty (by simp)).share
    · exact realized.pendingValues root view (List.mem_cons_of_mem _ member)

end Dada.Shared.Typing
