import Unique.Soundness
import Common.Rooted

namespace Dada.Unique

private def VariableRoot (state : State) (object : ObjectId) : Prop :=
  ∃ name, (name, some object) ∈ state.variables

private def FieldEdge (state : State) (parent object : ObjectId) : Prop :=
  ∃ data name, (parent, data) ∈ state.objects ∧ (name, some object) ∈ data.fields

private theorem reference_origin {state : State} {object : ObjectId}
    (member : object ∈ References state) :
    VariableRoot state object ∨ ∃ parent, Allocated state parent ∧ FieldEdge state parent object := by
  simp only [References, List.mem_append, List.mem_filterMap, List.mem_flatMap] at member
  rcases member with root | field
  · obtain ⟨⟨name, slot⟩, stored, value⟩ := root
    dsimp at value
    subst slot
    exact Or.inl ⟨name, stored⟩
  · obtain ⟨⟨parent, data⟩, allocated, ⟨⟨name, slot⟩, stored, value⟩⟩ := field
    dsimp at value
    subst slot
    exact Or.inr ⟨parent, List.mem_map.mpr ⟨(parent, data), allocated, rfl⟩,
      data, name, allocated, stored⟩

-- The finite allocation order prevents an owner-only cycle from satisfying
-- coverage without any variable root.
theorem WellFormed.allocated_live (wf : WellFormed classes state)
    (allocated : Allocated state object) : Live state object := by
  have rooted : Dada.Common.Rooted (VariableRoot state) (FieldEdge state) object :=
    Dada.Common.rooted_of_covered ObjectId.index state.nextId
      (fun node member => by
        obtain ⟨⟨_, data⟩, stored, rfl⟩ := List.mem_map.mp member
        exact wf.bounds _ data stored)
      (fun node member => reference_origin ((wf.referencesComplete node).mpr member))
      (fun parent node _ edge => by
        obtain ⟨data, name, stored, field⟩ := edge
        exact wf.older parent data name node stored field)
      object allocated
  clear allocated
  induction rooted with
  | root atRoot =>
    obtain ⟨name, stored⟩ := atRoot
    exact .variable stored
  | field _ edge ih =>
    obtain ⟨data, name, stored, field⟩ := edge
    exact .field ih stored field

theorem WellFormed.live_allocated (wf : WellFormed classes state)
    (live : Live state object) : Allocated state object := by
  apply (wf.referencesComplete object).mp
  cases live with
  | «variable» stored =>
    exact List.mem_append_left _ (List.mem_filterMap.mpr ⟨(_, some object), stored, rfl⟩)
  | field _ stored field =>
    exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨(_, _), stored, List.mem_filterMap.mpr ⟨(_, some object), field, rfl⟩⟩)

-- Liveness is a graph property, independent of the transition relation.
theorem WellFormed.live_iff_allocated (wf : WellFormed classes state) :
    Live state object ↔ Allocated state object :=
  ⟨wf.live_allocated, wf.allocated_live⟩

-- There is exactly one owning occurrence of each allocated object, counted
-- across both variables and object fields.
theorem WellFormed.owner_count (wf : WellFormed classes state)
    (allocated : Allocated state object) : (References state).count object = 1 := by
  exact wf.referencesUnique.count_of_mem ((wf.referencesComplete object).mpr allocated)

end Dada.Unique
