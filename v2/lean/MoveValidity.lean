import Access
import Moves

namespace Dada.Heap

variable {Primitive : Type}
variable {before after : State Primitive} {source destination place : Place}
variable {reference : Reference} {context permission : AccessPermission} {object : ObjectId}

-- A move preserves every allocated object. This does not establish that the object
-- was reachable from an owner, or that any borrow was active.
theorem MoveReference.liveObjects (move : MoveReference before source destination after)
    (object : ObjectId) : AllocatedObject after object ↔ AllocatedObject before object := by
  cases before
  cases after
  have keys := congrArg Prod.fst move.preserves_keys
  simp only [storageKeys] at keys
  simp only [AllocatedObject, keys]

-- Every initialized slot follows its occurrence, with the moved slot now at the
-- destination. An old initialized slot cannot be the formerly empty destination.
theorem MoveReference.transports_slot (move : MoveReference before source destination after)
    (stored : Heap.readSlot before place = some (.initialized reference)) :
    Heap.readSlot after (if place = source then destination else place) =
      some (.initialized (retargetReference source destination reference)) := by
  have referenceAt := readSlot_stored.mp stored
  by_cases atSource : place = source
  · subst place
    simpa only [ite_true] using readSlot_stored.mpr (move.reads_back referenceAt)
  · have notDestination : place ≠ destination := by
      cases move with
      | move _ empty _ _ _ =>
        intro same
        subst place
        exact empty.uninitialized_has_no_reference _ referenceAt
    rw [ite_eq_right atSource]
    apply readSlot_stored.mpr
    exact (move.other_references place _ atSource notDestination).mpr
      ⟨reference, referenceAt, rfl⟩

theorem retargetReference_project (source destination : Place)
    (context : AccessPermission) (reference : Reference) :
    context.project (retargetReference source destination reference) =
      context.project reference := by
  cases reference <;> rfl

-- Transport a finite successful resolution derivation, not merely the textual
-- support name. Each lease keeps the same target object and effective access.
-- No access-conflict check, liveness analysis, or runtime invalidation is implied.
theorem MoveReference.resolveReference
    (move : MoveReference before source destination after)
    (resolved : ResolveReference before context reference object permission) :
    ResolveReference after context (retargetReference source destination reference)
      object permission := by
  induction resolved with
  | owned live => exact .owned ((move.liveObjects _).mpr live)
  | showned live => exact .showned ((move.liveObjects _).mpr live)
  | shlease live => exact .shlease ((move.liveObjects _).mpr live)
  | leased allowed stored target ih =>
    apply ResolveReference.leased
    · simpa only [AccessPermission.project] using allowed
    · exact move.transports_slot stored
    · exact ih

theorem MoveReference.resolvePlace
    (move : MoveReference before source destination after)
    (resolved : ResolvePlace before context place object permission) :
    ResolvePlace after context (if place = source then destination else place)
      object permission := by
  cases resolved with
  | intro stored target =>
    exact .intro (move.transports_slot stored) (move.resolveReference target)

theorem MoveReference.source_resolves_at_destination
    (move : MoveReference before source destination after)
    (resolved : ResolvePlace before context source object permission) :
    ResolvePlace after context destination object permission := by
  simpa only [ite_true] using move.resolvePlace resolved

theorem MoveReference.other_place_keeps_target
    (move : MoveReference before source destination after)
    (different : place ≠ source)
    (resolved : ResolvePlace before context place object permission) :
    ResolvePlace after context place object permission := by
  simpa only [ite_eq_right different] using move.resolvePlace resolved

theorem MoveReference.dependent_keeps_target
    (move : MoveReference before source destination after)
    (dependent : ResolveReference before context (.leased source) object permission) :
    ResolveReference after context (.leased destination) object permission := by
  simpa [retargetReference] using move.resolveReference dependent

-- ANCHOR: move_preserves_lease_resolution
example (move : MoveReference before source destination after)
    (dependent : ResolveReference before context (.leased source) object permission) :
    ResolveReference after context (.leased destination) object permission := by
  exact move.dependent_keeps_target dependent
-- ANCHOR_END: move_preserves_lease_resolution

end Dada.Heap
