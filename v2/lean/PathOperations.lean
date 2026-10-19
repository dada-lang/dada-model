import Access
import Moves
import PlaceOperations

namespace Dada.Heap

variable {Primitive : Type}

inductive PathOperation where
  | give (source : AccessPath) (destination : VariableId)
  | lease (source : AccessPath) (destination : VariableId)
  | share (source : AccessPath) (destination : VariableId)
  | drop (source : AccessPath)

-- Runtime access follows the effective permissions of the selected path.
-- Liveness-dependent borrow restrictions are a separate judgment.
-- Effective showned access inherited from an owned inner edge requires a future
-- ownership-conversion rule; it cannot duplicate or destroy that edge here.
inductive PathStep : State Primitive → PathOperation → State Primitive → Prop where
  | giveGiven
      (resolved : ResolvePath before path source object .given)
      (moved : MoveReference before source (.variable destination) after) :
      PathStep before (.give path destination) after
  | giveLeased
      (resolved : ResolvePath before path source object .leased)
      (empty : Stored before (.variable destination) .uninitialized)
      (written : writeSlot before (.variable destination) (.initialized (.leased source)) = some after) :
      PathStep before (.give path destination) after
  | giveShowned
      (resolved : ResolvePath before path source object .showned)
      (stored : ReferenceAt before source (.showned object))
      (empty : Stored before (.variable destination) .uninitialized)
      (written : writeSlot before (.variable destination) (.initialized (.showned object)) = some after) :
      PathStep before (.give path destination) after
  | giveShlease
      (resolved : ResolvePath before path source object .shlease)
      (empty : Stored before (.variable destination) .uninitialized)
      (written : writeSlot before (.variable destination) (.initialized (.shlease object)) = some after) :
      PathStep before (.give path destination) after
  | lease
      (resolved : ResolvePath before path source object permission)
      (uniqueAccess : permission = .given ∨ permission = .leased)
      (empty : Stored before (.variable destination) .uninitialized)
      (written : writeSlot before (.variable destination) (.initialized (.leased source)) = some after) :
      PathStep before (.lease path destination) after
  | shareBorrow
      (resolved : ResolvePath before path source object permission)
      (borrowedResult : permission ≠ .showned)
      (empty : Stored before (.variable destination) .uninitialized)
      (written : writeSlot before (.variable destination) (.initialized (.shlease object)) = some after) :
      PathStep before (.share path destination) after
  | shareShowned
      (resolved : ResolvePath before path source object .showned)
      (stored : ReferenceAt before source (.showned object))
      (empty : Stored before (.variable destination) .uninitialized)
      (written : writeSlot before (.variable destination) (.initialized (.showned object)) = some after) :
      PathStep before (.share path destination) after
  | dropGiven
      (resolved : ResolvePath before path source object .given)
      (dropped : PlaceEffect before (.drop source) after) :
      PathStep before (.drop path) after
  | dropShowned
      (resolved : ResolvePath before path source object .showned)
      (stored : ReferenceAt before source (.showned object))
      (writable : WritablePath before path)
      (dropped : PlaceEffect before (.drop source) after) :
      PathStep before (.drop path) after
  | dropBorrow
      (resolved : ResolvePath before path source object permission)
      (borrowedAccess : permission = .leased ∨ permission = .shlease) :
      PathStep before (.drop path) before

theorem PathStep.preserves_ownership
    (step : PathStep before operation after) (invariant : OwnershipInvariant before) :
    OwnershipInvariant after := by
  cases step with
  | giveGiven _ moved => exact moved.preserves_ownership invariant
  | giveLeased _ empty written | giveShlease _ empty written
  | lease _ _ empty written | shareBorrow _ _ empty written =>
    exact initializeBorrow_preserves_ownership invariant empty (by intro id; simp) written
  | giveShowned _ stored empty written | shareShowned _ stored empty written =>
    exact duplicateShared_preserves_ownership invariant stored empty written
  | dropGiven _ dropped | dropShowned _ _ _ dropped =>
    exact placeEffect_preserves_ownership invariant dropped
  | dropBorrow _ _ => exact invariant

theorem PathStep.preserves_variable_order
    (step : PathStep before operation after) : variableOrder after = variableOrder before := by
  cases step with
  | giveGiven _ moved =>
    cases before
    cases after
    exact moved.preserves_variable_order
  | giveLeased _ _ written | giveShowned _ _ _ written | giveShlease _ _ written
  | lease _ _ _ written | shareBorrow _ _ _ written | shareShowned _ _ _ written =>
    exact writeSlot_variableOrder written
  | dropGiven _ dropped | dropShowned _ _ _ dropped =>
    exact placeEffect_preserves_variable_order dropped
  | dropBorrow _ _ => rfl

-- A wrapper combines the previously checked allocation/creation slice and the
-- path runtime slice. It is not a type-safety theorem or a complete fault model.
inductive MachineOperation (Primitive : Type) where
  | heap (operation : Operation Primitive)
  | place (operation : PathOperation)

inductive MachineStep : State Primitive → MachineOperation Primitive → State Primitive → Prop where
  | heap (step : Step Primitive before operation after) :
      MachineStep before (.heap operation) after
  | place (step : PathStep before operation after) :
      MachineStep before (.place operation) after

theorem MachineStep.preserves_ownership
    (step : MachineStep before operation after) (invariant : OwnershipInvariant before) :
    OwnershipInvariant after := by
  cases step with
  | heap step => exact step_preserves_ownership invariant step
  | place step => exact step.preserves_ownership invariant

inductive MachineReachable : State Primitive → Prop where
  | initial : MachineReachable (State.initial Primitive)
  | step (before : MachineReachable state) (next : MachineStep state operation after) :
      MachineReachable after

theorem machineReachable_preserves_ownership (reachable : MachineReachable state) :
    OwnershipInvariant state := by
  induction reachable with
  | initial => exact initial_ownershipInvariant _
  | step _ next ih => exact next.preserves_ownership ih

-- Reachability establishes these ownership conclusions; callers do not assume
-- the invariant. OwnerAt counts occurrences in variables, fields, and elements.
theorem machineReachable_has_owner (reachable : MachineReachable state)
    (live : AllocatedObject state object) :
    ∃ place, OwnerAt state place object :=
  (machineReachable_preserves_ownership reachable).hasOwner object live

-- An owned occurrence excludes every other owning occurrence, including showned
-- ones. This says nothing about uniqueness or activity of borrowed references.
theorem machineReachable_unique_owner (reachable : MachineReachable state)
    (owned : ReferenceAt state place (.owned object)) :
    ∀ other, OwnerAt state other object ↔ other = place := by
  have invariant := machineReachable_preserves_ownership reachable
  intro other
  constructor
  · intro owner
    rcases owner with unique | shared
    · exact invariant.unique other place object unique owned
    · exact False.elim (invariant.exclusive place other object owned shared)
  · intro same
    subst other
    exact Or.inl owned

end Dada.Heap
