import Destruction

namespace Dada.Heap

variable {Primitive : Type}

-- The resource-effect layer acts on already selected places. It deliberately
-- does not extend Step: path permissions and lease invalidation must be supplied
-- by the access layer before these effects become complete machine operations.
inductive PlaceOperation where
  | give (source : Place) (destination : VariableId)
  | lease (source : Place) (destination : VariableId)
  | share (source : Place) (destination : VariableId)
  | drop (source : Place)

inductive PlaceEffect : State Primitive → PlaceOperation → State Primitive → Prop where
  | giveOwned
      {before middle after : State Primitive} {source : Place}
      {destination : VariableId} {id : ObjectId}
      (stored : ReferenceAt before source (.owned id))
      (empty : Stored before (.variable destination) .uninitialized)
      (different : source ≠ .variable destination)
      (cleared : writeSlot before source .uninitialized = some middle)
      (written : writeSlot middle (.variable destination) (.initialized (.owned id)) = some after) :
      PlaceEffect before (.give source destination) after
  | leaseOwned
      {before after : State Primitive} {source : Place}
      {destination : VariableId} {id : ObjectId}
      (stored : ReferenceAt before source (.owned id))
      (empty : Stored before (.variable destination) .uninitialized)
      (written : writeSlot before (.variable destination) (.initialized (.leased source)) = some after) :
      PlaceEffect before (.lease source destination) after
  | leaseLeased
      {before after : State Primitive} {source support : Place}
      {destination : VariableId}
      (stored : ReferenceAt before source (.leased support))
      (empty : Stored before (.variable destination) .uninitialized)
      (written : writeSlot before (.variable destination) (.initialized (.leased source)) = some after) :
      PlaceEffect before (.lease source destination) after
  | shareOwned
      {before after : State Primitive} {source : Place}
      {destination : VariableId} {id : ObjectId}
      (stored : ReferenceAt before source (.owned id))
      (empty : Stored before (.variable destination) .uninitialized)
      (written : writeSlot before (.variable destination) (.initialized (.shlease id)) = some after) :
      PlaceEffect before (.share source destination) after
  | shareShowned
      {before after : State Primitive} {source : Place}
      {destination : VariableId} {id : ObjectId}
      (stored : ReferenceAt before source (.showned id))
      (empty : Stored before (.variable destination) .uninitialized)
      (written : writeSlot before (.variable destination) (.initialized (.showned id)) = some after) :
      PlaceEffect before (.share source destination) after
  | dropLeased
      {before after : State Primitive} {source support : Place}
      (stored : ReferenceAt before source (.leased support))
      (written : writeSlot before source .uninitialized = some after) :
      PlaceEffect before (.drop source) after
  | dropShlease
      {before after : State Primitive} {source : Place} {id : ObjectId}
      (stored : ReferenceAt before source (.shlease id))
      (written : writeSlot before source .uninitialized = some after) :
      PlaceEffect before (.drop source) after
  | dropShowned
      {before after : State Primitive} {source other : Place} {id : ObjectId}
      (stored : ReferenceAt before source (.showned id))
      (remaining : ReferenceAt before other (.showned id))
      (different : other ≠ source)
      (written : writeSlot before source .uninitialized = some after) :
      PlaceEffect before (.drop source) after

  | dropLeaf
      {before after : State Primitive} {source : Place} {id : ObjectId}
      (released : DropLeaf before source id after) :
      PlaceEffect before (.drop source) after
  | dropChild
      {before middle after : State Primitive} {source child : Place} {id : ObjectId}
      (owner : OwnerAt before source id)
      (lastOwner : ∀ place, OwnerAt before place id → place = source)
      (inside : WithinObject child id)
      (childEffect : PlaceEffect before (.drop child) middle)
      (rest : PlaceEffect middle (.drop source) after) :
      PlaceEffect before (.drop source) after

theorem placeEffect_preserves_ownership {before after : State Primitive}
    {operation : PlaceOperation} (invariant : OwnershipInvariant before)
    (effect : PlaceEffect before operation after) : OwnershipInvariant after := by
  induction effect with
  | giveOwned stored empty different cleared written =>
    exact moveSlot_preserves_ownership invariant stored empty different cleared written
  | leaseOwned _ empty written =>
    exact initializeBorrow_preserves_ownership invariant empty (by intro id; simp) written
  | leaseLeased _ empty written =>
    exact initializeBorrow_preserves_ownership invariant empty (by intro id; simp) written
  | shareOwned _ empty written =>
    exact initializeBorrow_preserves_ownership invariant empty (by intro id; simp) written
  | shareShowned stored empty written =>
    exact duplicateShared_preserves_ownership invariant stored empty written
  | dropLeased stored written =>
    exact clearBorrow_preserves_ownership invariant stored (by intro id; simp) written
  | dropShlease stored written =>
    exact clearBorrow_preserves_ownership invariant stored (by intro id; simp) written
  | dropShowned stored remaining different written =>
    exact releaseShared_preserves_ownership invariant stored remaining different written
  | dropLeaf released => exact released.preserves_ownership invariant
  | dropChild _ _ _ _ _ childIH restIH => exact restIH (childIH invariant)

-- Reference operations do not allocate, pop, or reorder variable lifetimes.
def variableOrder : State Primitive → List VariableId
  | .state _ variables => variables.entries.map Prod.fst

theorem writeSlot_variableOrder {before after : State Primitive} {place : Place} {slot : Slot}
    (written : writeSlot before place slot = some after) :
    variableOrder after = variableOrder before := by
  cases before
  cases after
  exact writeSlot_preserves_variable_order written

theorem placeEffect_preserves_variable_order {before after : State Primitive}
    {operation : PlaceOperation} (effect : PlaceEffect before operation after) :
    variableOrder after = variableOrder before := by
  induction effect with
  | giveOwned _ _ _ cleared written =>
    exact (writeSlot_variableOrder written).trans (writeSlot_variableOrder cleared)
  | leaseOwned _ _ written | leaseLeased _ _ written | shareOwned _ _ written
  | shareShowned _ _ written | dropLeased _ written | dropShlease _ written
  | dropShowned _ _ _ written => exact writeSlot_variableOrder written
  | dropLeaf released =>
    cases before
    cases after
    exact released.preserves_variable_order
  | dropChild _ _ _ _ _ childIH restIH => exact restIH.trans childIH

-- This is an object-map equality, including all object contents; it is stronger than
-- merely preserving the set of object identities for this variable-to-variable case.
theorem give_variable_preserves_objects
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot} {source destination : VariableId}
    (effect : PlaceEffect (.state objects variables)
      (.give (.variable source) destination) (.state objects' variables')) :
    objects' = objects := by
  cases effect with
  | giveOwned stored _ _ cleared written =>
    have found := readSlot_stored.mpr stored
    simp only [readSlot] at found
    simp [writeSlot, found] at cleared
    subst_vars
    cases destFound : (variables.replace source .uninitialized).lookup destination with
    | none => simp [writeSlot, destFound] at written
    | some old =>
      simp [writeSlot, destFound] at written
      exact written.1.symm

end Dada.Heap
