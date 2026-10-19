import ReferenceUpdates

namespace Dada.Heap

variable {Primitive : Type}

-- Consuming a stored reference relocates its occurrence and every direct lease
-- depending on it. This storage helper also handles a transferred unique lease;
-- path-level give of a leased reference may instead reborrow, as in v1.
-- Access permission and invalidation are obligations of the calling operation.
inductive MoveReference : State Primitive → Place → Place → State Primitive → Prop where
  | move
      {before middle writtenState : State Primitive} {source destination : Place}
      {reference : Reference}
      (stored : ReferenceAt before source reference)
      (empty : Stored before destination .uninitialized)
      (different : source ≠ destination)
      (cleared : writeSlot before source .uninitialized = some middle)
      (written : writeSlot middle destination (.initialized reference) = some writtenState) :
      MoveReference before source destination (retargetLeases source destination writtenState)

theorem MoveReference.preserves_ownership {before after : State Primitive}
    {source destination : Place} (move : MoveReference before source destination after)
    (invariant : OwnershipInvariant before) : OwnershipInvariant after := by
  cases move with
  | move stored empty different cleared written =>
    exact retargetLeases_preserves_ownership source destination
      (moveSlot_preserves_ownership invariant stored empty different cleared written)

-- This includes variable allocation order, not just equality of key sets.
def storageKeys : State Primitive → List ObjectId × List VariableId
  | .state objects variables =>
      (objects.entries.map Prod.fst, variables.entries.map Prod.fst)

private theorem writeSlot_storageKeys {before after : State Primitive} {place : Place} {slot : Slot}
    (written : writeSlot before place slot = some after) :
    storageKeys after = storageKeys before := by
  cases before
  cases after
  exact Prod.ext (writeSlot_preserves_keys written).1 (writeSlot_preserves_keys written).2

private theorem retargetLeases_storageKeys (source destination : Place) (state : State Primitive) :
    storageKeys (retargetLeases source destination state) = storageKeys state := by
  cases state
  simp [storageKeys, retargetLeases, mapReferences]

theorem MoveReference.preserves_keys {before after : State Primitive}
    {source destination : Place} (move : MoveReference before source destination after) :
    storageKeys after = storageKeys before := by
  cases move with
  | move _ _ _ cleared written =>
    exact (retargetLeases_storageKeys source destination _).trans
      ((writeSlot_storageKeys written).trans (writeSlot_storageKeys cleared))

theorem MoveReference.preserves_variable_order
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot} {source destination : Place}
    (move : MoveReference (.state objects variables) source destination (.state objects' variables')) :
    variables'.entries.map Prod.fst = variables.entries.map Prod.fst :=
  congrArg Prod.snd move.preserves_keys

-- The exact lookup equation also covers malformed self-dependent leases: if the
-- moved reference itself is leased(source), its support becomes destination.
theorem MoveReference.readSlot {before after : State Primitive} {source destination : Place}
    (move : MoveReference before source destination after) {reference : Reference}
    (stored : ReferenceAt before source reference) (place : Place) :
    readSlot after place =
      if place = destination then
        some (.initialized (retargetReference source destination reference))
      else if place = source then some .uninitialized
      else (readSlot before place).map (Slot.mapReferences (retargetReference source destination)) := by
  cases move with
  | move original _ different cleared written =>
    have same := Slot.initialized.inj (Stored.value_unique original stored)
    subst_vars
    rw [readSlot_retargetLeases, writeSlot_effects written, writeSlot_effects cleared]
    by_cases atDestination : place = destination
    · simp [atDestination, Slot.mapReferences]
    · by_cases atSource : place = source
      · simp [atSource, different, Slot.mapReferences]
      · simp [atDestination, atSource]

theorem MoveReference.reads_back {before after : State Primitive} {source destination : Place}
    (move : MoveReference before source destination after) {reference : Reference}
    (stored : ReferenceAt before source reference) :
    ReferenceAt after destination (retargetReference source destination reference) := by
  rw [ReferenceAt, ← readSlot_stored, move.readSlot stored]
  simp

theorem MoveReference.source_uninitialized {before after : State Primitive}
    {source destination : Place} (move : MoveReference before source destination after) :
    Stored after source .uninitialized := by
  cases move with
  | move stored empty different cleared written =>
    rw [← readSlot_stored, readSlot_retargetLeases,
      writeSlot_preserves_other written different, writeSlot_reads_back cleared]
    rfl

theorem MoveReference.other_references {before after : State Primitive}
    {source destination : Place} (move : MoveReference before source destination after)
    (place : Place) (reference : Reference)
    (notSource : place ≠ source) (notDestination : place ≠ destination) :
    ReferenceAt after place reference ↔
      ∃ previous, ReferenceAt before place previous ∧
        retargetReference source destination previous = reference := by
  cases move with
  | move _ empty different cleared written =>
    rw [retargetLeases, mapReferences_references]
    simp [moveSlot_references empty different cleared written, notSource, notDestination]

theorem MoveReference.dependent_follows {before after : State Primitive}
    {source destination : Place} (move : MoveReference before source destination after)
    (place : Place) (notSource : place ≠ source)
    (dependent : ReferenceAt before place (.leased source)) :
    ReferenceAt after place (.leased destination) := by
  have notDestination : place ≠ destination := by
    cases move with
    | move _ empty _ _ _ =>
      intro same
      subst place
      exact empty.uninitialized_has_no_reference _ dependent
  apply (move.other_references place (.leased destination) notSource notDestination).mpr
  exact ⟨.leased source, dependent, by simp [retargetReference]⟩

-- Moving the owner rewrites y's direct support; t still depends on y.
-- ANCHOR: move_owner_with_dependents
example :
    MoveReference
      (State.state (Primitive := Int) ⟨[(⟨0⟩, .primitive 22)], by simp⟩
        ⟨[(⟨2⟩, .uninitialized),
          (⟨3⟩, .initialized (.leased (.variable ⟨1⟩))),
          (⟨1⟩, .initialized (.leased (.variable ⟨0⟩))),
          (⟨0⟩, .initialized (.owned ⟨0⟩))], by decide⟩)
      (.variable ⟨0⟩) (.variable ⟨2⟩)
      (.state ⟨[(⟨0⟩, .primitive 22)], by simp⟩
        ⟨[(⟨2⟩, .initialized (.owned ⟨0⟩)),
          (⟨3⟩, .initialized (.leased (.variable ⟨1⟩))),
          (⟨1⟩, .initialized (.leased (.variable ⟨2⟩))),
          (⟨0⟩, .uninitialized)], by decide⟩) := by
  let middle : State Int := .state ⟨[(⟨0⟩, .primitive 22)], by simp⟩
    ⟨[(⟨2⟩, .uninitialized),
      (⟨3⟩, .initialized (.leased (.variable ⟨1⟩))),
      (⟨1⟩, .initialized (.leased (.variable ⟨0⟩))),
      (⟨0⟩, .uninitialized)], by decide⟩
  let writtenState : State Int := .state ⟨[(⟨0⟩, .primitive 22)], by simp⟩
    ⟨[(⟨2⟩, .initialized (.owned ⟨0⟩)),
      (⟨3⟩, .initialized (.leased (.variable ⟨1⟩))),
      (⟨1⟩, .initialized (.leased (.variable ⟨0⟩))),
      (⟨0⟩, .uninitialized)], by decide⟩
  have moved := MoveReference.move (middle := middle) (writtenState := writtenState)
    (source := .variable ⟨0⟩) (destination := .variable ⟨2⟩)
    (before := .state ⟨[(⟨0⟩, .primitive 22)], by simp⟩
      ⟨[(⟨2⟩, .uninitialized),
        (⟨3⟩, .initialized (.leased (.variable ⟨1⟩))),
        (⟨1⟩, .initialized (.leased (.variable ⟨0⟩))),
        (⟨0⟩, .initialized (.owned ⟨0⟩))], by decide⟩)
    (reference := .owned ⟨0⟩)
    (by simp [ReferenceAt, Stored]) (by simp [Stored]) (by decide)
    (by rfl)
    (by rfl)
  simpa [writtenState, retargetLeases, mapReferences, Object.mapReferences,
    Slot.mapReferences, FiniteMap.mapValues, retargetReference] using moved
-- ANCHOR_END: move_owner_with_dependents

-- Transferring y's unique lease preserves its parent x; its child t follows it
-- to z. This is a consuming transfer, not the v1 path-level give reborrow case.
-- ANCHOR: move_lease_with_sublease
example :
    MoveReference
      (State.state (Primitive := Int) ⟨[(⟨0⟩, .primitive 22)], by simp⟩
        ⟨[(⟨2⟩, .uninitialized),
          (⟨3⟩, .initialized (.leased (.variable ⟨1⟩))),
          (⟨1⟩, .initialized (.leased (.variable ⟨0⟩))),
          (⟨0⟩, .initialized (.owned ⟨0⟩))], by decide⟩)
      (.variable ⟨1⟩) (.variable ⟨2⟩)
      (.state ⟨[(⟨0⟩, .primitive 22)], by simp⟩
        ⟨[(⟨2⟩, .initialized (.leased (.variable ⟨0⟩))),
          (⟨3⟩, .initialized (.leased (.variable ⟨2⟩))),
          (⟨1⟩, .uninitialized),
          (⟨0⟩, .initialized (.owned ⟨0⟩))], by decide⟩) := by
  let middle : State Int := .state ⟨[(⟨0⟩, .primitive 22)], by simp⟩
    ⟨[(⟨2⟩, .uninitialized),
      (⟨3⟩, .initialized (.leased (.variable ⟨1⟩))),
      (⟨1⟩, .uninitialized),
      (⟨0⟩, .initialized (.owned ⟨0⟩))], by decide⟩
  let writtenState : State Int := .state ⟨[(⟨0⟩, .primitive 22)], by simp⟩
    ⟨[(⟨2⟩, .initialized (.leased (.variable ⟨0⟩))),
      (⟨3⟩, .initialized (.leased (.variable ⟨1⟩))),
      (⟨1⟩, .uninitialized),
      (⟨0⟩, .initialized (.owned ⟨0⟩))], by decide⟩
  have moved := MoveReference.move (middle := middle) (writtenState := writtenState)
    (source := .variable ⟨1⟩) (destination := .variable ⟨2⟩)
    (before := .state ⟨[(⟨0⟩, .primitive 22)], by simp⟩
      ⟨[(⟨2⟩, .uninitialized),
        (⟨3⟩, .initialized (.leased (.variable ⟨1⟩))),
        (⟨1⟩, .initialized (.leased (.variable ⟨0⟩))),
        (⟨0⟩, .initialized (.owned ⟨0⟩))], by decide⟩)
    (reference := .leased (.variable ⟨0⟩))
    (by simp [ReferenceAt, Stored]) (by simp [Stored]) (by decide)
    (by rfl)
    (by rfl)
  simpa [writtenState, retargetLeases, mapReferences, Object.mapReferences,
    Slot.mapReferences, FiniteMap.mapValues, retargetReference] using moved
-- ANCHOR_END: move_lease_with_sublease

end Dada.Heap
