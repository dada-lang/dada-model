import PlaceEffects

namespace Dada.Heap

variable {Primitive : Type}

-- An existing object with no reference-bearing contents needs no recursive release.
def EmptyObjectAt : State Primitive → ObjectId → Prop
  | .state objects _, id => ∃ object, (id, object) ∈ objects.entries ∧ ObjectEmpty object

def WithinObject : Place → ObjectId → Prop
  | .variable _, _ => False
  | .field owner _, id => owner = id
  | .element owner _, id => owner = id

def eraseObject : State Primitive → ObjectId → State Primitive
  | .state objects variables, id => .state (objects.erase id) variables

theorem EmptyObjectAt.no_reference {state : State Primitive} {id : ObjectId}
    (empty : EmptyObjectAt state id) {place : Place} {reference : Reference}
    (inside : WithinObject place id) : ¬ ReferenceAt state place reference := by
  cases state with
  | state objects variables =>
    obtain ⟨object, present, contents⟩ := empty
    cases place with
    | «variable» variableId => exact False.elim inside
    | field owner name =>
      cases inside
      rintro ⟨fields, found, field⟩
      have same := objects.value_unique present found
      cases same
      exact contents name reference field
    | element owner index =>
      cases inside
      rintro ⟨elements, found, element⟩
      have same := objects.value_unique present found
      cases same
      exact contents index reference element

theorem EmptyObjectAt.owner_outside {state : State Primitive} {id : ObjectId} {source : Place}
    (empty : EmptyObjectAt state id) (owner : OwnerAt state source id) :
    ¬ WithinObject source id := by
  intro inside
  rcases owner with owner | owner <;> exact empty.no_reference inside owner

theorem eraseObject_slots (state : State Primitive) (id : ObjectId)
    (place : Place) (slot : Slot) :
    Stored (eraseObject state id) place slot ↔
      Stored state place slot ∧ ¬ WithinObject place id := by
  cases state with
  | state objects variables =>
    cases place with
    | «variable» variableId => simp [Stored, eraseObject, WithinObject]
    | field owner name =>
      simp only [Stored, eraseObject, WithinObject, FiniteMap.erase,
        List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨fields, ⟨member, different⟩, field⟩
        exact ⟨⟨fields, member, field⟩, different⟩
      · rintro ⟨⟨fields, member, field⟩, different⟩
        exact ⟨fields, ⟨member, different⟩, field⟩
    | element owner index =>
      simp only [Stored, eraseObject, WithinObject, FiniteMap.erase,
        List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨elements, ⟨member, different⟩, element⟩
        exact ⟨⟨elements, member, element⟩, different⟩
      · rintro ⟨⟨elements, member, element⟩, different⟩
        exact ⟨elements, ⟨member, different⟩, element⟩

theorem eraseObject_references (state : State Primitive) (id : ObjectId)
    (place : Place) (reference : Reference) :
    ReferenceAt (eraseObject state id) place reference ↔
      ReferenceAt state place reference ∧ ¬ WithinObject place id :=
  eraseObject_slots state id place (.initialized reference)

theorem eraseObject_liveObjects (state : State Primitive) (id other : ObjectId) :
    AllocatedObject (eraseObject state id) other ↔ AllocatedObject state other ∧ other ≠ id := by
  cases state with
  | state objects variables =>
    simp only [AllocatedObject, eraseObject, FiniteMap.erase, List.mem_map, List.mem_filter,
      decide_eq_true_eq]
    constructor
    · rintro ⟨⟨key, object⟩, ⟨member, different⟩, equal⟩
      cases equal
      exact ⟨⟨(key, object), member, rfl⟩, different⟩
    · rintro ⟨⟨⟨key, object⟩, member, equal⟩, different⟩
      cases equal
      exact ⟨(key, object), ⟨member, different⟩, rfl⟩

-- This relation describes the ownership effect of releasing a final owner of
-- empty contents. It is not yet a machine drop rule: path permission, lease
-- invalidation and identity-reuse policies must be supplied by that rule.
inductive DropLeaf : State Primitive → Place → ObjectId → State Primitive → Prop where
  | release (before middle : State Primitive) (source : Place) (id : ObjectId)
      (owner : OwnerAt before source id)
      (lastOwner : ∀ place, OwnerAt before place id → place = source)
      (empty : EmptyObjectAt before id)
      (cleared : writeSlot before source .uninitialized = some middle) :
      DropLeaf before source id (eraseObject middle id)

theorem DropLeaf.references {before after : State Primitive} {source : Place} {id : ObjectId}
    (drop : DropLeaf before source id after) (place : Place) (reference : Reference) :
    ReferenceAt after place reference ↔ place ≠ source ∧ ReferenceAt before place reference := by
  cases drop with
  | release middle source id owner lastOwner empty cleared =>
    rw [eraseObject_references, clearSlot_references cleared]
    constructor
    · exact And.left
    · intro retained
      exact ⟨retained, fun inside => empty.no_reference inside retained.2⟩

theorem DropLeaf.liveObjects {before after : State Primitive} {source : Place} {id : ObjectId}
    (drop : DropLeaf before source id after) (other : ObjectId) :
    AllocatedObject after other ↔ AllocatedObject before other ∧ other ≠ id := by
  cases drop with
  | release middle source id owner lastOwner empty cleared =>
    rw [eraseObject_liveObjects, writeSlot_liveObjects cleared]

theorem DropLeaf.source_uninitialized {before after : State Primitive}
    {source : Place} {id : ObjectId} (drop : DropLeaf before source id after) :
    Stored after source .uninitialized := by
  cases drop with
  | release middle source id owner lastOwner empty cleared =>
    apply (eraseObject_slots middle id source .uninitialized).mpr
    exact ⟨readSlot_stored.mp (writeSlot_reads_back cleared), empty.owner_outside owner⟩

theorem DropLeaf.preserves_variable_order
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot} {source : Place} {id : ObjectId}
    (drop : DropLeaf (.state objects variables) source id (.state objects' variables')) :
    variables'.entries.map Prod.fst = variables.entries.map Prod.fst := by
  cases drop with
  | release middle source id owner lastOwner empty cleared =>
    cases middle with
    | state middleObjects middleVariables =>
      exact writeSlot_preserves_variable_order cleared

theorem DropLeaf.preserves_ownership {before after : State Primitive}
    {source : Place} {id : ObjectId} (invariant : OwnershipInvariant before)
    (drop : DropLeaf before source id after) : OwnershipInvariant after := by
  have references := drop.references
  have objects := drop.liveObjects
  cases drop with
  | release middle source id owner lastOwner empty cleared =>
    exact invariant.dropLeaf source id owner lastOwner references objects

-- ANCHOR: drop_leaf_primitive
example :
    let x : VariableId := ⟨0⟩
    let α : ObjectId := ⟨0⟩
    let before : State Int :=
      .state ⟨[(α, .primitive 22)], by simp⟩
        ⟨[(x, .initialized (.owned α))], by simp⟩
    let after : State Int :=
      .state .empty ⟨[(x, .uninitialized)], by simp⟩
    DropLeaf before (.variable x) α after := by
  dsimp only
  let before : State Int :=
    .state ⟨[(⟨0⟩, .primitive 22)], by simp⟩
      ⟨[(⟨0⟩, .initialized (.owned ⟨0⟩))], by simp⟩
  let middle : State Int :=
    .state ⟨[(⟨0⟩, .primitive 22)], by simp⟩
      ⟨[(⟨0⟩, .uninitialized)], by simp⟩
  have lastOwner : ∀ place, OwnerAt before place ⟨0⟩ → place = .variable ⟨0⟩ := by
    intro place owner
    cases place <;> simp [before, OwnerAt, ReferenceAt, Stored] at owner ⊢
    exact owner
  have drop := DropLeaf.release before middle (.variable ⟨0⟩) ⟨0⟩
    (Or.inl (by simp [before, ReferenceAt, Stored])) lastOwner
    (by exact ⟨.primitive 22, by simp, True.intro⟩)
    (by rfl)
  simpa [eraseObject, middle, FiniteMap.erase, FiniteMap.empty] using drop
-- ANCHOR_END: drop_leaf_primitive

end Dada.Heap
