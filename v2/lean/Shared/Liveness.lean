import Shared.Soundness
import Common.Rooted

namespace Dada.Shared

private def VariableRoot (state : State) (object : ObjectId) : Prop :=
  ∃ name reference, (name, some reference) ∈ state.variables ∧ reference.object = object

private def FieldEdge (state : State) (parent object : ObjectId) : Prop :=
  ∃ data name reference, (parent, data) ∈ state.objects ∧
    (name, some reference) ∈ data.fields ∧ reference.object = object

private theorem reference_origin {state : State} {object : ObjectId}
    (member : object ∈ References state) :
    VariableRoot state object ∨ ∃ parent, Allocated state parent ∧ FieldEdge state parent object := by
  simp only [References, List.mem_append, List.mem_filterMap, List.mem_flatMap] at member
  rcases member with root | field
  · obtain ⟨⟨name, slot⟩, stored, value⟩ := root
    obtain ⟨reference, sameSlot, sameTarget⟩ := Option.map_eq_some_iff.mp value
    dsimp at sameSlot
    subst slot
    exact Or.inl ⟨name, reference, stored, sameTarget⟩
  · obtain ⟨⟨parent, data⟩, allocated, ⟨⟨name, slot⟩, stored, value⟩⟩ := field
    obtain ⟨reference, sameSlot, sameTarget⟩ := Option.map_eq_some_iff.mp value
    dsimp at sameSlot
    subst slot
    exact Or.inr ⟨parent, List.mem_map.mpr ⟨(parent, data), allocated, rfl⟩,
      data, name, reference, allocated, stored, sameTarget⟩

-- Sharing can introduce several incoming owning edges, but every finite
-- backwards path through fields must still reach a variable root.
theorem WellFormed.allocated_live (wf : WellFormed classes state)
    (allocated : Allocated state object) : Live state object := by
  have rooted : Dada.Common.Rooted (VariableRoot state) (FieldEdge state) object :=
    Dada.Common.rooted_of_covered ObjectId.index state.nextId
      (fun node member => by
        obtain ⟨⟨_, data⟩, stored, rfl⟩ := List.mem_map.mp member
        exact wf.bounds _ data stored)
      (fun node member => reference_origin ((wf.referencesComplete node).mpr member))
      (fun parent node _ edge => by
        obtain ⟨data, name, reference, stored, field, sameTarget⟩ := edge
        simpa [sameTarget] using wf.older parent data name reference stored field)
      object allocated
  clear allocated
  induction rooted with
  | root atRoot =>
    obtain ⟨name, reference, stored, sameTarget⟩ := atRoot
    simpa [sameTarget] using Live.variable stored
  | field _ edge ih =>
    obtain ⟨data, name, reference, stored, field, sameTarget⟩ := edge
    simpa [sameTarget] using Live.field ih stored field

theorem WellFormed.live_allocated (wf : WellFormed classes state)
    (live : Live state object) : Allocated state object := by
  apply (wf.referencesComplete object).mp
  cases live with
  | «variable» stored =>
    exact List.mem_append_left _ (List.mem_filterMap.mpr ⟨(_, _), stored, rfl⟩)
  | field _ stored field =>
    exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨(_, _), stored, List.mem_filterMap.mpr ⟨(_, _), field, rfl⟩⟩)

theorem WellFormed.live_iff_allocated (wf : WellFormed classes state) :
    Live state object ↔ Allocated state object :=
  ⟨wf.live_allocated, wf.allocated_live⟩

theorem WellFormed.owner_count_positive (wf : WellFormed classes state)
    (allocated : Allocated state object) : 0 < (References state).count object :=
  List.count_pos_iff.mpr ((wf.referencesComplete object).mpr allocated)

-- A unique owner excludes every other owning occurrence, including shared ones.
-- Shared owners are counted separately even when their reference values coincide.
theorem WellFormed.unique_owner_count (wf : WellFormed classes state)
    (unique : Reference.owned object ∈ Owners state) :
    (References state).count object = 1 := by
  obtain ⟨leading, trailing, decomposition⟩ := List.mem_iff_append.mp unique
  have reordered : (Owners state).Perm (Reference.owned object :: (leading ++ trailing)) := by
    rw [decomposition]
    exact List.perm_middle
  have compatible := reordered.pairwise wf.ownersCompatible (by
    intro first second relation
    rcases relation with different | shared
    · exact Or.inl (Ne.symm different)
    · exact Or.inr ⟨shared.2, shared.1⟩)
  have absent : object ∉ (leading ++ trailing).map Reference.object := by
    intro member
    obtain ⟨reference, found, same⟩ := List.mem_map.mp member
    have relation := (List.pairwise_cons.mp compatible).1 reference found
    rcases relation with different | shared
    · exact different same.symm
    · cases shared.1
  have targets : (Owners state).map Reference.object = References state := by
    simp [Owners, References, List.map_filterMap, List.map_flatMap]
  have counted := (reordered.map Reference.object).count_eq object
  rw [targets] at counted
  rw [counted]
  change (object :: (leading ++ trailing).map Reference.object).count object = 1
  rw [List.count_cons, List.count_eq_zero.mpr absent]
  simp


private def LocatedOwners (state : State) : List (StoragePlace × Reference) :=
  state.variables.filterMap (fun binding => binding.2.map (fun r => (.variable binding.1, r))) ++
    state.objects.flatMap (fun entry => entry.2.fields.filterMap
      (fun field => field.2.map (fun r => (.field entry.1 field.1, r))))

private theorem located_owners (state : State) :
    (LocatedOwners state).map Prod.snd = Owners state := by
  simp [LocatedOwners, Owners, List.map_filterMap, List.map_flatMap, Function.comp_def]

private theorem stored_located (stored : Stored state place (some reference)) :
    (place, reference) ∈ LocatedOwners state := by
  cases place with
  | «variable» name =>
    exact List.mem_append_left _ (List.mem_filterMap.mpr ⟨(name, some reference), stored, rfl⟩)
  | field object name =>
    obtain ⟨data, member, field⟩ := stored
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨(object, data), member,
      List.mem_filterMap.mpr ⟨(name, some reference), field, rfl⟩⟩)

private theorem located_eq_or_compatible {owners : List (StoragePlace × Reference)}
    (pairwise : owners.Pairwise (fun a b => Compatible a.2 b.2))
    (first : a ∈ owners) (second : b ∈ owners) : a = b ∨ Compatible a.2 b.2 := by
  induction owners with
  | nil => simp at first
  | cons head tail ih =>
    rcases List.mem_cons.mp first with firstEq | firstTail
    · subst a
      rcases List.mem_cons.mp second with secondEq | secondTail
      · exact Or.inl secondEq.symm
      · exact Or.inr ((List.pairwise_cons.mp pairwise).1 _ secondTail)
    · rcases List.mem_cons.mp second with secondEq | secondTail
      · subst b
        apply Or.inr
        rcases (List.pairwise_cons.mp pairwise).1 _ firstTail with different | shared
        · exact Or.inl different.symm
        · exact Or.inr ⟨shared.2, shared.1⟩
      · exact ih pairwise.of_cons firstTail secondTail

private theorem WellFormed.unique_storage (wf : WellFormed classes state)
    (owned : Stored state place (some (.owned object)))
    (stored : Stored state otherPlace (some reference))
    (target : reference.object = object) :
    otherPlace = place ∧ reference = .owned object := by
  have pairwise : (LocatedOwners state).Pairwise (fun a b => Compatible a.2 b.2) := by
    apply List.pairwise_map.mp
    simpa [located_owners] using wf.ownersCompatible
  rcases located_eq_or_compatible pairwise (stored_located owned) (stored_located stored) with
    same | compatible
  · exact ⟨(congrArg Prod.fst same).symm, (congrArg Prod.snd same).symm⟩
  · rcases compatible with different | shared
    · exact False.elim (different target.symm)
    · cases shared.1

private theorem reference_eq_owned {reference : Reference} (unique : reference.mode = .unique) :
    reference = .owned reference.object := by
  cases reference with
  | reference mode object => cases unique; rfl

private theorem Mode.join_unique {first second : Mode} (unique : first.join second = .unique) :
    first = .unique ∧ second = .unique := by
  cases first <;> cases second <;> simp_all [Mode.join]

private theorem Resolve.unique_mode (wf : WellFormed classes state)
    (resolved : Resolve state path place object permission)
    (unique : permission = .unique)
    (other : Resolve state otherPath otherPlace otherObject mode)
    (sameTarget : otherObject = object) : mode = .unique := by
  induction resolved generalizing otherPath otherPlace otherObject mode with
  | @«variable» name reference stored =>
    have owned : Stored state (.variable name) (some (.owned reference.object)) := by
      change (name, some (.owned reference.object)) ∈ state.variables
      rw [← reference_eq_owned unique]
      exact stored
    cases other with
    | @«variable» otherName otherReference otherStored =>
      have same := wf.unique_storage owned (otherPlace := .variable otherName) otherStored sameTarget
      exact congrArg Reference.mode same.2
    | @field otherBase otherSource otherParent otherPermission otherData otherName otherReference base parentStored fieldStored =>
      have same := wf.unique_storage owned
        (otherPlace := .field otherParent otherName) ⟨otherData, parentStored, fieldStored⟩ sameTarget
      cases same.1
  | @field base source parent permission data name reference baseResolved parentStored fieldStored ih =>
    have modes := Mode.join_unique unique
    have owned : Stored state (.field parent name) (some (.owned reference.object)) := by
      refine ⟨data, parentStored, ?_⟩
      rw [← reference_eq_owned modes.2]
      exact fieldStored
    cases other with
    | @«variable» otherName otherReference otherStored =>
      have same := wf.unique_storage owned
        (otherPlace := .variable otherName) otherStored sameTarget
      cases same.1
    | @field otherBase otherSource otherParent otherPermission otherData otherName otherReference
        otherResolved otherParentStored otherFieldStored =>
      have same := wf.unique_storage owned
        (otherPlace := .field otherParent otherName)
        ⟨otherData, otherParentStored, otherFieldStored⟩ sameTarget
      have parentEqual : otherParent = parent := (StoragePlace.field.inj same.1).1
      have prefixMode := ih modes.1 otherResolved parentEqual
      have fieldMode := congrArg Reference.mode same.2
      rw [prefixMode, fieldMode]
      rfl

-- References along two variable-rooted paths to one object cannot disagree
-- between all-unique access and access that crosses a shared reference.
theorem WellFormed.path_mode_exclusive (wf : WellFormed classes state)
    (unique : Resolve state uniquePath uniquePlace object .unique)
    (shared : Resolve state sharedPath sharedPlace object .shared) : False := by
  have impossible := unique.unique_mode wf rfl shared rfl
  cases impossible

end Dada.Shared
