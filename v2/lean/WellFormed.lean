import MoveValidity
import PathOperations

namespace Dada.Heap

variable {Primitive : Type}

-- Rooted liveness follows owning occurrences, starting at every variable slot.
-- OwnerAt includes both unique and shared ownership, but never a lease.
inductive OwningReachable (state : State Primitive) : ObjectId → Prop where
  | variable (owner : OwnerAt state (.variable rootVariable) object) :
      OwningReachable state object
  | field (parent : OwningReachable state object)
      (owner : OwnerAt state (.field object name) target) :
      OwningReachable state target
  | element (parent : OwningReachable state object)
      (owner : OwnerAt state (.element object index) target) :
      OwningReachable state target

-- This is structural reference reachability, not an executable access path.
-- Each edge resolves independently; no permission restriction from an earlier
-- edge prevents counting a reference stored inside a reachable object.
inductive ReferenceReachable (state : State Primitive) : ObjectId → Prop where
  | variable (stored : ReferenceAt state (.variable rootVariable) reference)
      (resolved : ResolveReference state .given reference object permission) :
      ReferenceReachable state object
  | field (parent : ReferenceReachable state object)
      (stored : ReferenceAt state (.field object name) reference)
      (resolved : ResolveReference state .given reference target permission) :
      ReferenceReachable state target
  | element (parent : ReferenceReachable state object)
      (stored : ReferenceAt state (.element object index) reference)
      (resolved : ResolveReference state .given reference target permission) :
      ReferenceReachable state target

-- AllocatedObject means object-map membership.
-- RootedOwnership equates those allocated objects with rooted owning paths.
def RootedOwnership (state : State Primitive) : Prop :=
  ∀ object, AllocatedObject state object ↔ OwningReachable state object

theorem OwnerAt.resolves (ownership : OwnershipInvariant state)
    (owner : OwnerAt state place object) :
    ∃ reference permission, ReferenceAt state place reference ∧
      ResolveReference state .given reference object permission := by
  have live := ownership.targetsLive place object owner
  rcases owner with unique | shared
  · exact ⟨.owned object, .given, unique, .owned live⟩
  · exact ⟨.showned object, .showned, shared, .showned live⟩

theorem OwningReachable.referenceReachable (ownership : OwnershipInvariant state)
    (reachable : OwningReachable state object) : ReferenceReachable state object := by
  induction reachable with
  | «variable» owner =>
    obtain ⟨_, _, stored, resolved⟩ := owner.resolves ownership
    exact .variable stored resolved
  | field _ owner ih =>
    obtain ⟨_, _, stored, resolved⟩ := owner.resolves ownership
    exact .field ih stored resolved
  | element _ owner ih =>
    obtain ⟨_, _, stored, resolved⟩ := owner.resolves ownership
    exact .element ih stored resolved

theorem ReferenceReachable.allocated (reachable : ReferenceReachable state object) :
    AllocatedObject state object := by
  cases reachable with
  | «variable» _ resolved => exact resolved.live
  | field _ _ resolved => exact resolved.live
  | element _ _ resolved => exact resolved.live

theorem OwningReachable.allocated (ownership : OwnershipInvariant state)
    (reachable : OwningReachable state object) : AllocatedObject state object :=
  (reachable.referenceReachable ownership).allocated

-- Every stored reference, including those in fields and array elements, has a
-- finite resolution through existing support slots to an allocated object. This is
-- reference validity in a state, not exclusivity or activity of a unique lease.
-- It imposes no history of previously allocated variable or object identities.
structure NoDangling (state : State Primitive) : Prop where
  resolves : ∀ place reference, ReferenceAt state place reference →
    ∃ object permission, ResolveReference state .given reference object permission

structure WellFormed (state : State Primitive) : Prop where
  allocatedLive : ∀ object, AllocatedObject state object → OwningReachable state object
  slotsValid : ∀ place slot, Stored state place slot →
    match slot with
    | .uninitialized => True
    | .initialized reference =>
      ∃ object permission, ResolveReference state .given reference object permission ∧
        OwningReachable state object
  uniqueOwners : ∀ place object, ReferenceAt state place (.owned object) →
    ∀ other, OwnerAt state other object → other = place

theorem WellFormed.reference_live (valid : WellFormed state)
    (stored : ReferenceAt state place reference) :
    ∃ object permission, ResolveReference state .given reference object permission ∧
      OwningReachable state object :=
  valid.slotsValid place (.initialized reference) stored

theorem WellFormed.noDangling (valid : WellFormed state) : NoDangling state := by
  constructor
  intro place reference stored
  obtain ⟨object, permission, resolved, _⟩ := valid.reference_live stored
  exact ⟨object, permission, resolved⟩

theorem WellFormed.ownership (valid : WellFormed state) : OwnershipInvariant state := by
  constructor
  · intro place object owner
    rcases owner with unique | shared
    · obtain ⟨_, _, resolved, _⟩ := valid.reference_live unique
      cases resolved with
      | owned allocated => exact allocated
    · obtain ⟨_, _, resolved, _⟩ := valid.reference_live shared
      cases resolved with
      | showned allocated => exact allocated
  · intro object allocated
    cases valid.allocatedLive object allocated with
    | «variable» owner => exact ⟨_, owner⟩
    | field _ owner => exact ⟨_, owner⟩
    | element _ owner => exact ⟨_, owner⟩
  · intro place other object first second
    exact (valid.uniqueOwners place object first other (Or.inl second)).symm
  · intro place other object unique shared
    have same := valid.uniqueOwners place object unique other (Or.inr shared)
    subst other
    have impossible := Stored.value_unique unique shared
    cases impossible

theorem WellFormed.rootedOwnership (valid : WellFormed state) : RootedOwnership state := by
  intro object
  exact ⟨valid.allocatedLive object, fun reachable => reachable.allocated valid.ownership⟩

-- The three direct clauses retain exactly the earlier combination of ownership,
-- rooted liveness, and reference integrity; no execution premise is involved.
theorem WellFormed.equivalent_conditions :
    WellFormed state ↔ OwnershipInvariant state ∧ RootedOwnership state ∧ NoDangling state := by
  constructor
  · intro valid
    exact ⟨valid.ownership, valid.rootedOwnership, valid.noDangling⟩
  · rintro ⟨ownership, rooted, references⟩
    constructor
    · intro object allocated
      exact (rooted object).mp allocated
    · intro place slot stored
      cases slot with
      | uninitialized => trivial
      | initialized reference =>
        obtain ⟨object, permission, resolved⟩ := references.resolves place reference stored
        exact ⟨object, permission, resolved, (rooted object).mp resolved.live⟩
    · intro place object unique other owner
      rcases owner with otherUnique | shared
      · exact ownership.unique other place object otherUnique unique
      · exact False.elim (ownership.exclusive place other object unique shared)

theorem WellFormed.reachability_agrees (valid : WellFormed state) :
    (AllocatedObject state object ↔ OwningReachable state object) ∧
    (ReferenceReachable state object ↔ OwningReachable state object) := by
  refine ⟨valid.rootedOwnership object, ?_⟩
  constructor
  · intro reachable
    exact (valid.rootedOwnership object).mp reachable.allocated
  · intro reachable
    exact reachable.referenceReachable valid.ownership

-- These are consequences of the state-level definition of well-formedness.
-- Their hypotheses make no claim that the state is reachable by current steps.
theorem WellFormed.has_owner (valid : WellFormed state)
    (live : AllocatedObject state object) :
    ∃ place, OwnerAt state place object :=
  valid.ownership.hasOwner object live

-- OwnerAt includes both owned and showned occurrences in variables, fields,
-- and array elements. This exclusivity is about owners, not unique leases.
theorem WellFormed.unique_owner (valid : WellFormed state)
    (owned : ReferenceAt state place (.owned object)) :
    ∀ other, OwnerAt state other object ↔ other = place := by
  intro other
  constructor
  · intro owner
    rcases owner with unique | shared
    · exact valid.ownership.unique other place object unique owned
    · exact False.elim (valid.ownership.exclusive place other object owned shared)
  · intro same
    subst other
    exact Or.inl owned

theorem initial_noDangling : NoDangling (State.initial Primitive) := by
  constructor
  intro place reference stored
  cases place <;> simp [ReferenceAt, Stored, State.initial, FiniteMap.empty] at stored

theorem initial_rootedOwnership : RootedOwnership (State.initial Primitive) := by
  intro object
  constructor
  · intro allocated
    simp [AllocatedObject, State.initial, FiniteMap.empty] at allocated
  · intro reachable
    exact reachable.allocated (initial_ownershipInvariant Primitive)

theorem initial_wellFormed : WellFormed (State.initial Primitive) :=
  WellFormed.equivalent_conditions.mpr
    ⟨initial_ownershipInvariant Primitive, initial_rootedOwnership, initial_noDangling⟩

theorem NoDangling.target_live (valid : NoDangling state)
    (stored : ReferenceAt state place reference) :
    ∃ object permission,
      ResolveReference state .given reference object permission ∧ AllocatedObject state object := by
  obtain ⟨object, permission, resolved⟩ := valid.resolves _ _ stored
  exact ⟨object, permission, resolved, resolved.live⟩

theorem NoDangling.shlease_live (valid : NoDangling state)
    (stored : ReferenceAt state place (.shlease object)) : AllocatedObject state object := by
  obtain ⟨_, _, resolved⟩ := valid.resolves _ _ stored
  cases resolved with
  | shlease live => exact live

theorem NoDangling.lease_support_resolves (valid : NoDangling state)
    (stored : ReferenceAt state place (.leased support)) :
    ∃ object, ResolvePlace state .leased support object .leased := by
  obtain ⟨object, _, resolved⟩ := valid.resolves _ _ stored
  cases resolved with
  | leased _ supportStored target => exact ⟨object, .intro supportStored target⟩

theorem NoDangling.lease_support_exists (valid : NoDangling state)
    (stored : ReferenceAt state place (.leased support)) :
    ∃ reference, ReferenceAt state support reference := by
  obtain ⟨_, resolved⟩ := valid.lease_support_resolves stored
  cases resolved with
  | intro supportStored _ => exact ⟨_, readSlot_stored.mp supportStored⟩

theorem WellFormed.lease_support_exists (valid : WellFormed state)
    (stored : ReferenceAt state place (.leased support)) :
    ∃ reference, ReferenceAt state support reference :=
  valid.noDangling.lease_support_exists stored

private theorem MoveReference.reference_origin
    (move : MoveReference before source destination after)
    (stored : ReferenceAt after place reference) :
    ∃ oldPlace oldReference, ReferenceAt before oldPlace oldReference ∧
      retargetReference source destination oldReference = reference := by
  by_cases atDestination : place = destination
  · subst place
    have original : ∃ oldReference, ReferenceAt before source oldReference := by
      cases move with
      | move original _ _ _ _ => exact ⟨_, original⟩
    obtain ⟨oldReference, original⟩ := original
    exact ⟨source, oldReference, original,
      Slot.initialized.inj (Stored.value_unique (move.reads_back original) stored)⟩
  · have notSource : place ≠ source := by
      intro same
      subst place
      exact move.source_uninitialized.uninitialized_has_no_reference _ stored
    obtain ⟨oldReference, oldStored, same⟩ :=
      (move.other_references place reference notSource atDestination).mp stored
    exact ⟨place, oldReference, oldStored, same⟩

theorem MoveReference.preserves_noDangling
    (move : MoveReference before source destination after) (valid : NoDangling before) :
    NoDangling after := by
  constructor
  intro place reference stored
  obtain ⟨oldPlace, oldReference, original, same⟩ := move.reference_origin stored
  obtain ⟨object, permission, resolved⟩ := valid.resolves oldPlace oldReference original
  rw [← same]
  exact ⟨object, permission, move.resolveReference resolved⟩

private theorem MoveReference.transports_owner
    (move : MoveReference before source destination after)
    (owner : OwnerAt before place object) :
    OwnerAt after (if place = source then destination else place) object := by
  rcases owner with unique | shared
  · exact Or.inl (readSlot_stored.mp (by
      simpa [retargetReference] using move.transports_slot (readSlot_stored.mpr unique)))
  · exact Or.inr (readSlot_stored.mp (by
      simpa [retargetReference] using move.transports_slot (readSlot_stored.mpr shared)))

-- A move into a variable can turn an interior ownership edge into a root, but
-- cannot disconnect the moved object or anything below it from all roots.
theorem MoveReference.preserves_owningReachable
    (move : MoveReference before source (.variable destination) after)
    (reachable : OwningReachable before object) : OwningReachable after object := by
  induction reachable with
  | @«variable» rootVariable object owner =>
    have transported := move.transports_owner owner
    by_cases atSource : Place.variable rootVariable = source
    · exact .variable (by simpa only [ite_eq_left atSource] using transported)
    · exact .variable (by simpa only [ite_eq_right atSource] using transported)
  | @field object name target parent owner ih =>
    have transported := move.transports_owner owner
    by_cases atSource : Place.field object name = source
    · exact .variable (by simpa only [ite_eq_left atSource] using transported)
    · exact .field ih (by simpa only [ite_eq_right atSource] using transported)
  | @element object index target parent owner ih =>
    have transported := move.transports_owner owner
    by_cases atSource : Place.element object index = source
    · exact .variable (by simpa only [ite_eq_left atSource] using transported)
    · exact .element ih (by simpa only [ite_eq_right atSource] using transported)

theorem MoveReference.preserves_rootedOwnership
    (move : MoveReference before source (.variable destination) after)
    (ownership : OwnershipInvariant before) (rooted : RootedOwnership before) :
    RootedOwnership after := by
  intro object
  constructor
  · intro allocated
    exact move.preserves_owningReachable
      ((rooted object).mp ((move.liveObjects object).mp allocated))
  · intro reachable
    exact reachable.allocated (move.preserves_ownership ownership)

theorem MoveReference.preserves_wellFormed
    (move : MoveReference before source (.variable destination) after) (valid : WellFormed before) :
    WellFormed after :=
  WellFormed.equivalent_conditions.mpr
    ⟨move.preserves_ownership valid.ownership,
      move.preserves_rootedOwnership valid.ownership valid.rootedOwnership,
      move.preserves_noDangling valid.noDangling⟩

private def disconnectedCycle : State Nat :=
  .state ⟨[(⟨0⟩, .aggregate ⟨[("self", .initialized (.owned ⟨0⟩))], by simp⟩)], by simp⟩
    .empty

private theorem disconnectedCycle_ownership : OwnershipInvariant disconnectedCycle := by
  have onlyOwner : ∀ place object, OwnerAt disconnectedCycle place object →
      place = .field ⟨0⟩ "self" ∧ object = ⟨0⟩ := by
    intro place object owner
    cases place with
    | «variable» id =>
      simp [OwnerAt, ReferenceAt, Stored, disconnectedCycle, FiniteMap.empty] at owner
    | field id name =>
      rcases owner with owner | owner
      all_goals
        simp [ReferenceAt, Stored, disconnectedCycle] at owner
        obtain ⟨fields, ⟨rfl, rfl⟩, field⟩ := owner
        simp_all
    | element id index =>
      simp [OwnerAt, ReferenceAt, Stored, disconnectedCycle] at owner
  constructor
  · intro place object owner
    obtain ⟨_, rfl⟩ := onlyOwner _ _ owner
    simp [AllocatedObject, disconnectedCycle]
  · intro object allocated
    simp [AllocatedObject, disconnectedCycle] at allocated
    subst object
    exact ⟨.field ⟨0⟩ "self", Or.inl (by simp [ReferenceAt, Stored, disconnectedCycle])⟩
  · intro place other object first second
    exact (onlyOwner _ _ (Or.inl first)).1.trans (onlyOwner _ _ (Or.inl second)).1.symm
  · intro place other object _ shared
    cases other with
    | «variable» id =>
      simp [ReferenceAt, Stored, disconnectedCycle, FiniteMap.empty] at shared
    | field id name =>
      simp [ReferenceAt, Stored, disconnectedCycle] at shared
      obtain ⟨fields, ⟨rfl, rfl⟩, field⟩ := shared
      simp at field
    | element id index => simp [ReferenceAt, Stored, disconnectedCycle] at shared

private theorem disconnectedCycle_noDangling : NoDangling disconnectedCycle := by
  constructor
  intro place reference stored
  cases place with
  | «variable» id => simp [ReferenceAt, Stored, disconnectedCycle, FiniteMap.empty] at stored
  | field id name =>
    simp [ReferenceAt, Stored, disconnectedCycle] at stored
    obtain ⟨fields, ⟨rfl, rfl⟩, field⟩ := stored
    simp only [List.mem_singleton, Prod.mk.injEq, Slot.initialized.injEq] at field
    obtain ⟨_, rfl⟩ := field
    exact ⟨⟨0⟩, .given, .owned (by simp [AllocatedObject, disconnectedCycle])⟩
  | element id index => simp [ReferenceAt, Stored, disconnectedCycle] at stored

private theorem disconnectedCycle_not_rooted : ¬ RootedOwnership disconnectedCycle := by
  have noRoot : ∀ object, ¬ OwningReachable disconnectedCycle object := by
    intro object reachable
    induction reachable with
    | «variable» owner =>
      simp [OwnerAt, ReferenceAt, Stored, disconnectedCycle, FiniteMap.empty] at owner
    | field _ _ ih => exact ih
    | element _ _ ih => exact ih
  intro rooted
  exact noRoot ⟨0⟩ ((rooted ⟨0⟩).mp (by simp [AllocatedObject, disconnectedCycle]))

-- A field owning its own containing object supplies a local owner and a valid
-- reference, but there is no path from a variable that keeps the object live.
-- ANCHOR: disconnected_owning_cycle_not_wellFormed
example :
    OwnershipInvariant disconnectedCycle ∧ NoDangling disconnectedCycle ∧
    ¬ RootedOwnership disconnectedCycle ∧ ¬ WellFormed disconnectedCycle := by
  refine ⟨disconnectedCycle_ownership, disconnectedCycle_noDangling,
    disconnectedCycle_not_rooted, ?_⟩
  intro valid
  exact disconnectedCycle_not_rooted valid.rootedOwnership
-- ANCHOR_END: disconnected_owning_cycle_not_wellFormed

private def danglingBefore : State Nat :=
  .state ⟨[(⟨0⟩, .primitive 22)], by simp⟩
    ⟨[(⟨1⟩, .initialized (.shlease ⟨0⟩)),
      (⟨0⟩, .initialized (.owned ⟨0⟩))], by decide⟩

private def danglingAfter : State Nat :=
  .state .empty
    ⟨[(⟨1⟩, .initialized (.shlease ⟨0⟩)), (⟨0⟩, .uninitialized)], by decide⟩

-- Allocate x, allocate y, create a primitive in x, and share x into y.
private theorem danglingBefore_reachable : MachineReachable danglingBefore := by
  let x : VariableId := ⟨0⟩
  let y : VariableId := ⟨1⟩
  let variablesX : FiniteMap VariableId Slot := ⟨[(x, .uninitialized)], by simp⟩
  let variablesXY : FiniteMap VariableId Slot :=
    ⟨[(y, .uninitialized), (x, .uninitialized)], by decide⟩
  let created : State Nat :=
    .state ⟨[(⟨0⟩, .primitive 22)], by simp⟩
      ⟨[(y, .uninitialized), (x, .initialized (.owned ⟨0⟩))], by decide⟩
  have allocX := Step.allocVariable (Primitive := Nat) FiniteMap.empty FiniteMap.empty
    x (by simp [FiniteMap.empty])
  have allocY := Step.allocVariable (Primitive := Nat) FiniteMap.empty variablesX
    y (by simp [variablesX, x, y])
  have create := Step.createPrimitive (Primitive := Nat) FiniteMap.empty variablesXY
    22 x (by simp [variablesXY]) ⟨0⟩ (by simp [FiniteMap.empty])
  have reachableCreated : MachineReachable created :=
    .step (.step (.step .initial (.heap allocX)) (.heap allocY)) (.heap create)
  have share : PathStep created (.share (.path x []) y) danglingBefore := by
    apply PathStep.shareBorrow (source := .variable x) (object := ⟨0⟩) (permission := .given)
    · apply ResolvePath.variable
      apply ResolvePlace.intro (by rfl)
      apply ResolveReference.owned
      simp [created, AllocatedObject]
    · decide
    · simp [created, Stored]
    · rfl
  exact .step reachableCreated (.place share)

private theorem danglingBefore_wellFormed : WellFormed danglingBefore := by
  apply WellFormed.equivalent_conditions.mpr
  refine ⟨machineReachable_preserves_ownership danglingBefore_reachable, ?_, ?_⟩
  · intro object
    constructor
    · intro allocated
      simp [AllocatedObject, danglingBefore] at allocated
      subst object
      exact .variable (rootVariable := ⟨0⟩) (Or.inl (by
        simp [ReferenceAt, Stored, danglingBefore]))
    · intro reachable
      exact reachable.allocated
        (machineReachable_preserves_ownership danglingBefore_reachable)
  · constructor
    intro place reference stored
    cases place with
    | «variable» id =>
      simp [ReferenceAt, Stored, danglingBefore] at stored
      rcases stored with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨⟨0⟩, .shlease, .shlease (by simp [danglingBefore, AllocatedObject])⟩
      · exact ⟨⟨0⟩, .given, .owned (by simp [danglingBefore, AllocatedObject])⟩
    | field id name => simp [ReferenceAt, Stored, danglingBefore] at stored
    | element id index => simp [ReferenceAt, Stored, danglingBefore] at stored

private theorem danglingDrop :
    PathStep danglingBefore (.drop (.path ⟨0⟩ [])) danglingAfter := by
  let middle : State Nat := .state ⟨[(⟨0⟩, .primitive 22)], by simp⟩
    ⟨[(⟨1⟩, .initialized (.shlease ⟨0⟩)), (⟨0⟩, .uninitialized)], by decide⟩
  apply PathStep.dropGiven (source := .variable ⟨0⟩) (object := ⟨0⟩)
  · apply ResolvePath.variable
    apply ResolvePlace.intro (by rfl)
    apply ResolveReference.owned
    simp [danglingBefore, AllocatedObject]
  · have lastOwner : ∀ place, OwnerAt danglingBefore place ⟨0⟩ →
        place = .variable ⟨0⟩ := by
      intro place owner
      cases place <;> simp [danglingBefore, OwnerAt, ReferenceAt, Stored] at owner ⊢
      exact owner
    have release := DropLeaf.release danglingBefore middle (.variable ⟨0⟩) ⟨0⟩
      (Or.inl (readSlot_stored.mp (by rfl))) lastOwner
      ⟨.primitive 22, by simp, True.intro⟩ (by rfl)
    apply PlaceEffect.dropLeaf
    simpa [middle, danglingAfter, eraseObject, FiniteMap.erase, FiniteMap.empty] using release

private theorem danglingAfter_invalid : ¬ NoDangling danglingAfter := by
  intro valid
  have live := valid.shlease_live
    (place := .variable ⟨1⟩) (object := ⟨0⟩) (readSlot_stored.mp (by rfl))
  simp [danglingAfter, AllocatedObject, FiniteMap.empty] at live

-- This is a checked counterexample to preservation by the current unrestricted
-- path runtime slice. The source is well formed and reachable; dropping the
-- final owner leaves y pointing at the deleted object. Ownership still holds.
-- ANCHOR: reachable_drop_leaves_dangling
example :
    MachineReachable danglingBefore ∧ WellFormed danglingBefore ∧
    PathStep danglingBefore (.drop (.path ⟨0⟩ [])) danglingAfter ∧
    MachineReachable danglingAfter ∧ OwnershipInvariant danglingAfter ∧
    ¬ NoDangling danglingAfter := by
  have reachableAfter : MachineReachable danglingAfter :=
    .step danglingBefore_reachable (.place danglingDrop)
  exact ⟨danglingBefore_reachable, danglingBefore_wellFormed, danglingDrop,
    reachableAfter, machineReachable_preserves_ownership reachableAfter,
    danglingAfter_invalid⟩
-- ANCHOR_END: reachable_drop_leaves_dangling

theorem machineReachable_does_not_imply_noDangling :
    ¬ (∀ state : State Nat, MachineReachable state → NoDangling state) := by
  intro preserved
  exact danglingAfter_invalid (preserved danglingAfter
    (.step danglingBefore_reachable (.place danglingDrop)))

end Dada.Heap
