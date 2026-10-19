import Invariants
import Places

namespace Dada.Heap

variable {Primitive : Type}

-- Storage effects connect executable slot updates to occurrence-based ownership.
-- These helpers do not grant permission to access a place or validate a lease.
theorem readSlot_stored {state : State Primitive} {place : Place} {slot : Slot} :
    readSlot state place = some slot ↔ Stored state place slot := by
  cases state with
  | state objects variables =>
    cases place with
    | «variable» id => exact readSlot_variable_iff objects variables id slot
    | field id name => exact readSlot_field_iff objects variables id name slot
    | element id index => exact readSlot_element_iff objects variables id index slot

theorem writeSlot_references {before after : State Primitive} {place : Place} {slot : Slot}
    (written : writeSlot before place slot = some after)
    (other : Place) (reference : Reference) :
    ReferenceAt after other reference ↔
      (other = place ∧ slot = .initialized reference) ∨
        (other ≠ place ∧ ReferenceAt before other reference) := by
  unfold ReferenceAt
  rw [← readSlot_stored, writeSlot_effects written other]
  by_cases same : other = place
  · simp [same]
  · simp [same, readSlot_stored]

theorem writeSlot_liveObjects {before after : State Primitive} {place : Place} {slot : Slot}
    (written : writeSlot before place slot = some after) (id : ObjectId) :
    AllocatedObject after id ↔ AllocatedObject before id := by
  cases before with
  | state objects variables =>
    cases after with
    | state objects' variables' =>
      have keys := (writeSlot_preserves_keys written).1
      simp only [AllocatedObject, keys]

theorem initializeSlot_references {before after : State Primitive}
    {destination : Place} {reference : Reference}
    (empty : Stored before destination .uninitialized)
    (written : writeSlot before destination (.initialized reference) = some after)
    (place : Place) (result : Reference) :
    ReferenceAt after place result ↔
      (place = destination ∧ result = reference) ∨ ReferenceAt before place result := by
  rw [writeSlot_references written]
  constructor
  · rintro (⟨same, equal⟩ | ⟨_, old⟩)
    · exact Or.inl ⟨same, (Slot.initialized.inj equal).symm⟩
    · exact Or.inr old
  · rintro (⟨same, equal⟩ | old)
    · exact Or.inl ⟨same, congrArg Slot.initialized equal.symm⟩
    · refine Or.inr ⟨?_, old⟩
      intro same
      subst place
      have impossible := Stored.value_unique old empty
      cases impossible

theorem clearSlot_references {before after : State Primitive} {source : Place}
    (written : writeSlot before source .uninitialized = some after)
    (place : Place) (reference : Reference) :
    ReferenceAt after place reference ↔
      place ≠ source ∧ ReferenceAt before place reference := by
  rw [writeSlot_references written]
  simp

theorem moveSlot_references {before middle after : State Primitive}
    {source destination : Place} {reference : Reference}
    (empty : Stored before destination .uninitialized) (different : source ≠ destination)
    (cleared : writeSlot before source .uninitialized = some middle)
    (written : writeSlot middle destination (.initialized reference) = some after)
    (place : Place) (result : Reference) :
    ReferenceAt after place result ↔
      (place = destination ∧ result = reference) ∨
        (place ≠ source ∧ ReferenceAt before place result) := by
  have emptyMiddle : Stored middle destination .uninitialized := by
    rw [← readSlot_stored, writeSlot_preserves_other cleared (Ne.symm different)]
    exact readSlot_stored.mpr empty
  rw [initializeSlot_references emptyMiddle written, clearSlot_references cleared]

theorem initializeBorrow_preserves_ownership {before after : State Primitive}
    {destination : Place} {reference : Reference}
    (invariant : OwnershipInvariant before)
    (empty : Stored before destination .uninitialized)
    (nonowning : ∀ id, reference ≠ .owned id ∧ reference ≠ .showned id)
    (written : writeSlot before destination (.initialized reference) = some after) :
    OwnershipInvariant after := by
  exact invariant.addBorrow destination reference nonowning
    (initializeSlot_references empty written) (writeSlot_liveObjects written)

theorem moveSlot_preserves_ownership {before middle after : State Primitive}
    {source destination : Place} {reference : Reference}
    (invariant : OwnershipInvariant before)
    (stored : ReferenceAt before source reference)
    (empty : Stored before destination .uninitialized) (different : source ≠ destination)
    (cleared : writeSlot before source .uninitialized = some middle)
    (written : writeSlot middle destination (.initialized reference) = some after) :
    OwnershipInvariant after := by
  apply invariant.move source destination reference stored
    (moveSlot_references empty different cleared written)
  intro id
  exact (writeSlot_liveObjects written id).trans (writeSlot_liveObjects cleared id)

theorem duplicateShared_preserves_ownership {before after : State Primitive}
    {source destination : Place} {id : ObjectId}
    (invariant : OwnershipInvariant before)
    (stored : ReferenceAt before source (.showned id))
    (empty : Stored before destination .uninitialized)
    (written : writeSlot before destination (.initialized (.showned id)) = some after) :
    OwnershipInvariant after := by
  exact invariant.duplicateShared source destination id stored
    (initializeSlot_references empty written) (writeSlot_liveObjects written)

theorem clearBorrow_preserves_ownership {before after : State Primitive}
    {source : Place} {reference : Reference}
    (invariant : OwnershipInvariant before)
    (stored : ReferenceAt before source reference)
    (nonowning : ∀ id, reference ≠ .owned id ∧ reference ≠ .showned id)
    (written : writeSlot before source .uninitialized = some after) :
    OwnershipInvariant after := by
  exact invariant.removeBorrow source reference stored nonowning
    (clearSlot_references written) (writeSlot_liveObjects written)

theorem releaseShared_preserves_ownership {before after : State Primitive}
    {source other : Place} {id : ObjectId}
    (invariant : OwnershipInvariant before)
    (stored : ReferenceAt before source (.showned id))
    (remaining : ReferenceAt before other (.showned id)) (different : other ≠ source)
    (written : writeSlot before source .uninitialized = some after) :
    OwnershipInvariant after := by
  exact invariant.releaseShared source other id stored remaining different
    (clearSlot_references written) (writeSlot_liveObjects written)

end Dada.Heap
