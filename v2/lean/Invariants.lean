import Heap

namespace Dada.Heap

variable {Primitive : Type}

-- A place identifies one storage occurrence. In particular, equal reference
-- values stored in distinct fields or array elements are counted separately.
def Stored : State Primitive → Place → Slot → Prop
  | .state _ variables, .variable id, slot => (id, slot) ∈ variables.entries
  | .state objects _, .field id name, slot =>
      ∃ fields, (id, Object.aggregate fields) ∈ objects.entries ∧
        (name, slot) ∈ fields.entries
  | .state objects _, .element id index, slot =>
      ∃ elements, (id, Object.array elements) ∈ objects.entries ∧
        elements[index]? = some slot

def ReferenceAt (state : State Primitive) (place : Place) (reference : Reference) : Prop :=
  Stored state place (.initialized reference)

-- Object-map membership is separate from liveness through a rooted owning path.
def AllocatedObject : State Primitive → ObjectId → Prop
  | .state objects _, id => id ∈ objects.entries.map Prod.fst

def OwnerAt (state : State Primitive) (place : Place) (id : ObjectId) : Prop :=
  ReferenceAt state place (.owned id) ∨ ReferenceAt state place (.showned id)

-- These are predicates on arbitrary states, not assumptions built into Step.
-- Lease validity, ownership acyclicity, and reachability from variables are
-- separate obligations: none follows from these ownership conditions alone.
structure OwnershipInvariant (state : State Primitive) : Prop where
  targetsLive : ∀ place id, OwnerAt state place id → AllocatedObject state id
  hasOwner : ∀ id, AllocatedObject state id → ∃ place, OwnerAt state place id
  unique : ∀ place other id,
    ReferenceAt state place (.owned id) → ReferenceAt state other (.owned id) →
      place = other
  exclusive : ∀ place other id,
    ReferenceAt state place (.owned id) → ¬ ReferenceAt state other (.showned id)

theorem Stored.value_unique {state : State Primitive} {place : Place} {slot other : Slot}
    (stored : Stored state place slot) (stored' : Stored state place other) :
    slot = other := by
  cases state with
  | state objects variables =>
    cases place with
    | «variable» id => exact variables.value_unique stored stored'
    | field id name =>
      obtain ⟨fields, member, field⟩ := stored
      obtain ⟨fields', member', field'⟩ := stored'
      have same := objects.value_unique member member'
      cases same
      exact fields.value_unique field field'
    | element id index =>
      obtain ⟨elements, member, element⟩ := stored
      obtain ⟨elements', member', element'⟩ := stored'
      have same := objects.value_unique member member'
      cases same
      exact Option.some.inj (element.symm.trans element')

theorem Stored.uninitialized_has_no_reference {state : State Primitive} {place : Place}
    (empty : Stored state place .uninitialized) : ∀ reference, ¬ ReferenceAt state place reference := by
  intro reference initialized
  have incompatible := Stored.value_unique empty initialized
  cases incompatible

theorem Stored.element_in_bounds
    {objects : FiniteMap ObjectId (Object Primitive)} {variables : FiniteMap VariableId Slot}
    {id : ObjectId} {index : Nat} {slot : Slot}
    (stored : Stored (.state objects variables) (.element id index) slot) :
    ∃ elements, (id, Object.array elements) ∈ objects.entries ∧ index < elements.size := by
  obtain ⟨elements, member, element⟩ := stored
  exact ⟨elements, member, (Array.getElem?_eq_some_iff.mp element).1⟩

theorem OwnershipInvariant.absent_has_no_owner {state : State Primitive}
    (invariant : OwnershipInvariant state) (id : ObjectId) (absent : ¬ AllocatedObject state id) :
    ∀ place, ¬ OwnerAt state place id := by
  intro place owner
  exact absent (invariant.targetsLive place id owner)

theorem initial_ownershipInvariant (Primitive : Type) :
    OwnershipInvariant (State.initial Primitive) := by
  have absent : ∀ place reference,
      ¬ ReferenceAt (State.initial Primitive) place reference := by
    intro place reference
    cases place <;> simp [ReferenceAt, Stored, State.initial, FiniteMap.empty]
  constructor
  · intro place id owner
    rcases owner with owner | owner <;> exact False.elim (absent _ _ owner)
  · intro id live
    simp [AllocatedObject, State.initial, FiniteMap.empty] at live
  · intro place other id owner _
    exact False.elim (absent _ _ owner)
  · intro place other id owner _
    exact absent _ _ owner

-- A reusable preservation lemma for changes to empty storage: ownership depends
-- on stored occurrences and live identities, not on the number of empty slots.
theorem OwnershipInvariant.transport {before after : State Primitive}
    (invariant : OwnershipInvariant before)
    (references : ∀ place reference,
      ReferenceAt after place reference ↔ ReferenceAt before place reference)
    (objects : ∀ id, AllocatedObject after id ↔ AllocatedObject before id) :
    OwnershipInvariant after := by
  constructor
  · intro place id owner
    apply (objects id).mpr
    apply invariant.targetsLive place id
    rcases owner with owner | owner
    · exact Or.inl ((references _ _).mp owner)
    · exact Or.inr ((references _ _).mp owner)
  · intro id live
    obtain ⟨place, owner⟩ := invariant.hasOwner id ((objects id).mp live)
    refine ⟨place, ?_⟩
    rcases owner with owner | owner
    · exact Or.inl ((references _ _).mpr owner)
    · exact Or.inr ((references _ _).mpr owner)
  · intro place other id owner owner'
    exact invariant.unique place other id
      ((references _ _).mp owner) ((references _ _).mp owner')
  · intro place other id owner owner'
    exact invariant.exclusive place other id
      ((references _ _).mp owner) ((references _ _).mp owner')

-- Inserting exactly one fresh object and its owner preserves ownership. The
-- no-dangling-owner condition is essential: map freshness alone is insufficient.
theorem OwnershipInvariant.create {before after : State Primitive}
    (invariant : OwnershipInvariant before) (id : ObjectId) (destination : Place)
    (fresh : ¬ AllocatedObject before id)
    (references : ∀ place reference, ReferenceAt after place reference ↔
      (place = destination ∧ reference = .owned id) ∨ ReferenceAt before place reference)
    (objects : ∀ other, AllocatedObject after other ↔ other = id ∨ AllocatedObject before other) :
    OwnershipInvariant after := by
  have no_owner : ∀ place, ¬ OwnerAt before place id := by
    intro place owner
    exact fresh (invariant.targetsLive place id owner)
  constructor
  · intro place other owner
    apply (objects other).mpr
    rcases owner with owner | owner
    · rcases (references _ _).mp owner with ⟨_, equal⟩ | old
      · exact Or.inl (Reference.owned.inj equal)
      · exact Or.inr (invariant.targetsLive _ _ (Or.inl old))
    · rcases (references _ _).mp owner with ⟨_, equal⟩ | old
      · cases equal
      · exact Or.inr (invariant.targetsLive _ _ (Or.inr old))
  · intro other live
    rcases (objects other).mp live with rfl | old
    · exact ⟨destination, Or.inl ((references _ _).mpr (Or.inl ⟨rfl, rfl⟩))⟩
    · obtain ⟨place, owner⟩ := invariant.hasOwner other old
      refine ⟨place, ?_⟩
      rcases owner with owner | owner
      · exact Or.inl ((references _ _).mpr (Or.inr owner))
      · exact Or.inr ((references _ _).mpr (Or.inr owner))
  · intro place other target owner owner'
    rcases (references _ _).mp owner with ⟨rfl, equal⟩ | old
    · cases equal
      rcases (references _ _).mp owner' with ⟨equal, _⟩ | old'
      · exact equal.symm
      · exact False.elim (no_owner other (Or.inl old'))
    · rcases (references _ _).mp owner' with ⟨rfl, equal⟩ | old'
      · cases equal
        exact False.elim (no_owner place (Or.inl old))
      · exact invariant.unique _ _ _ old old'
  · intro place other target owner shared
    rcases (references _ _).mp shared with ⟨_, equal⟩ | old_shared
    · cases equal
    · rcases (references _ _).mp owner with ⟨_, equal⟩ | old_owner
      · cases equal
        exact no_owner other (Or.inr old_shared)
      · exact invariant.exclusive _ _ _ old_owner old_shared

-- Empty aggregate and array slots have no stored reference occurrences.
def ObjectEmpty : Object Primitive → Prop
  | .primitive _ => True
  | .aggregate fields => ∀ name reference,
      (name, Slot.initialized reference) ∉ fields.entries
  | .array elements => ∀ (index : Nat) reference,
      elements[index]? ≠ some (Slot.initialized reference)

theorem initialFields_empty (names : List FieldName) (distinct : names.Nodup) :
    ObjectEmpty (Object.aggregate (Primitive := Primitive) (initialFields names distinct)) := by
  intro name reference member
  have empty := (initialFields_contents names distinct).mp member
  cases empty.2

theorem initialElements_empty (length : Nat) :
    ObjectEmpty (Object.array (Primitive := Primitive) (initialElements length)) := by
  intro index reference
  simp [initialElements, Array.getElem?_replicate]

theorem FiniteMap.initialize_references
    (variables : FiniteMap VariableId Slot) (destination : VariableId)
    (empty : (destination, Slot.uninitialized) ∈ variables.entries)
    (reference : Reference) (key : VariableId) (result : Reference) :
    (key, Slot.initialized result) ∈
        (variables.replace destination (.initialized reference)).entries ↔
      (key = destination ∧ result = reference) ∨
        (key, Slot.initialized result) ∈ variables.entries := by
  rw [FiniteMap.replace_contents]
  constructor
  · rintro ⟨previous, member, equal⟩
    by_cases same : key = destination
    · simp only [same, ite_true] at equal
      exact Or.inl ⟨same, Slot.initialized.inj equal⟩
    · simp only [same, ite_false] at equal
      exact Or.inr (equal ▸ member)
  · rintro (⟨rfl, rfl⟩ | member)
    · exact ⟨.uninitialized, empty, by simp⟩
    · have different : key ≠ destination := by
        intro equal
        subst key
        have incompatible := variables.value_unique member empty
        cases incompatible
      exact ⟨.initialized result, member, by simp [different]⟩

theorem insert_empty_references
    (objects : FiniteMap ObjectId (Object Primitive))
    (variables : FiniteMap VariableId Slot)
    (id : ObjectId) (object : Object Primitive)
    (fresh : id ∉ objects.entries.map Prod.fst) (objectEmpty : ObjectEmpty object)
    (destination : VariableId)
    (empty : (destination, Slot.uninitialized) ∈ variables.entries)
    (place : Place) (reference : Reference) :
    ReferenceAt
        (.state (objects.insertFresh id object fresh)
          (variables.replace destination (.initialized (.owned id)))) place reference ↔
      (place = .variable destination ∧ reference = .owned id) ∨
        ReferenceAt (.state objects variables) place reference := by
  cases place with
  | «variable» key =>
    simpa [ReferenceAt, Stored] using
      variables.initialize_references destination empty (.owned id) key reference
  | field target name =>
    simp only [ReferenceAt, Stored, FiniteMap.insertFresh, List.mem_cons,
      reduceCtorEq, false_and, false_or]
    constructor
    · rintro ⟨fields, (equal | member), field⟩
      · obtain ⟨_, equal⟩ := Prod.mk.inj equal
        subst object
        exact False.elim (objectEmpty name reference field)
      · exact ⟨fields, member, field⟩
    · rintro ⟨fields, member, field⟩
      exact ⟨fields, Or.inr member, field⟩
  | element target index =>
    simp only [ReferenceAt, Stored, FiniteMap.insertFresh, List.mem_cons,
      reduceCtorEq, false_and, false_or]
    constructor
    · rintro ⟨elements, (equal | member), element⟩
      · obtain ⟨_, equal⟩ := Prod.mk.inj equal
        subst object
        exact False.elim (objectEmpty index reference element)
      · exact ⟨elements, member, element⟩
    · rintro ⟨elements, member, element⟩
      exact ⟨elements, Or.inr member, element⟩

theorem insert_empty_preserves_ownership
    (objects : FiniteMap ObjectId (Object Primitive))
    (variables : FiniteMap VariableId Slot)
    (invariant : OwnershipInvariant (.state objects variables))
    (id : ObjectId) (object : Object Primitive)
    (fresh : id ∉ objects.entries.map Prod.fst) (objectEmpty : ObjectEmpty object)
    (destination : VariableId)
    (empty : (destination, Slot.uninitialized) ∈ variables.entries) :
    OwnershipInvariant
      (.state (objects.insertFresh id object fresh)
        (variables.replace destination (.initialized (.owned id)))) := by
  apply invariant.create id (.variable destination) fresh
  · exact insert_empty_references objects variables id object fresh objectEmpty destination empty
  · intro target
    simp [AllocatedObject, FiniteMap.insertFresh]

theorem step_preserves_ownership {before after : State Primitive}
    {operation : Operation Primitive}
    (invariant : OwnershipInvariant before) (step : Step Primitive before operation after) :
    OwnershipInvariant after := by
  cases step with
  | allocVariable objects variables id fresh =>
    apply invariant.transport
    · intro place reference
      cases place <;> simp [ReferenceAt, Stored, FiniteMap.insertFresh]
    · intro target
      rfl
  | deallocVariable objects variables id empty _ =>
    apply invariant.transport
    · intro place reference
      cases place with
      | «variable» key =>
        simp only [ReferenceAt, Stored, FiniteMap.erase, List.mem_filter,
          decide_eq_true_eq]
        constructor
        · exact And.left
        · intro member
          refine ⟨member, ?_⟩
          intro equal
          subst key
          have incompatible := variables.value_unique member empty
          cases incompatible
      | field target name => rfl
      | element target index => rfl
    · intro target
      rfl
  | createPrimitive objects variables value destination empty id fresh =>
    exact insert_empty_preserves_ownership objects variables invariant id
      (.primitive value) fresh True.intro destination empty
  | createAggregate objects variables fields distinct destination empty id fresh =>
    exact insert_empty_preserves_ownership objects variables invariant id
      (.aggregate (initialFields fields distinct)) fresh
      (initialFields_empty fields distinct) destination empty
  | createArray objects variables length destination empty id fresh =>
    exact insert_empty_preserves_ownership objects variables invariant id
      (.array (initialElements length)) fresh (initialElements_empty length) destination empty

-- Reachable deliberately names the current allocation/creation Step relation.
-- Adding place operations requires a corresponding preservation proof, rather
-- than silently treating their post-state invariant as a transition premise.
inductive Reachable (Primitive : Type) : State Primitive → Prop where
  | initial : Reachable Primitive (State.initial Primitive)
  | step {before after : State Primitive} {operation : Operation Primitive}
      (reachable : Reachable Primitive before)
      (transition : Step Primitive before operation after) : Reachable Primitive after

theorem reachable_ownershipInvariant {state : State Primitive}
    (reachable : Reachable Primitive state) : OwnershipInvariant state := by
  induction reachable with
  | initial => exact initial_ownershipInvariant Primitive
  | step _ transition invariant => exact step_preserves_ownership invariant transition

-- Moving a reference relocates one occurrence without changing ownership kind.
-- The effect equation is supplied by a concrete place-update proof; it is not a
-- post-state invariant premise and applies to every reference, including leases.
theorem OwnershipInvariant.move {before after : State Primitive}
    (invariant : OwnershipInvariant before) (source destination : Place)
    (reference : Reference) (stored : ReferenceAt before source reference)
    (references : ∀ place result, ReferenceAt after place result ↔
      (place = destination ∧ result = reference) ∨
        (place ≠ source ∧ ReferenceAt before place result))
    (objects : ∀ id, AllocatedObject after id ↔ AllocatedObject before id) :
    OwnershipInvariant after := by
  constructor
  · intro place id owner
    apply (objects id).mpr
    rcases owner with owner | owner
    · rcases (references _ _).mp owner with ⟨_, equal⟩ | ⟨_, old⟩
      · exact invariant.targetsLive source id (Or.inl (equal ▸ stored))
      · exact invariant.targetsLive place id (Or.inl old)
    · rcases (references _ _).mp owner with ⟨_, equal⟩ | ⟨_, old⟩
      · exact invariant.targetsLive source id (Or.inr (equal ▸ stored))
      · exact invariant.targetsLive place id (Or.inr old)
  · intro id live
    obtain ⟨place, owner⟩ := invariant.hasOwner id ((objects id).mp live)
    by_cases same : place = source
    · subst place
      refine ⟨destination, ?_⟩
      rcases owner with owner | owner
      · have equal : .owned id = reference :=
          Slot.initialized.inj (Stored.value_unique owner stored)
        exact Or.inl ((references _ _).mpr (Or.inl ⟨rfl, equal⟩))
      · have equal : .showned id = reference :=
          Slot.initialized.inj (Stored.value_unique owner stored)
        exact Or.inr ((references _ _).mpr (Or.inl ⟨rfl, equal⟩))
    · refine ⟨place, ?_⟩
      rcases owner with owner | owner
      · exact Or.inl ((references _ _).mpr (Or.inr ⟨same, owner⟩))
      · exact Or.inr ((references _ _).mpr (Or.inr ⟨same, owner⟩))
  · intro place other id owner owner'
    rcases (references _ _).mp owner with ⟨rfl, equal⟩ | ⟨different, old⟩
    · rcases (references _ _).mp owner' with ⟨rfl, _⟩ | ⟨different', old'⟩
      · rfl
      · exact False.elim (different'
          (invariant.unique source other id (equal ▸ stored) old').symm)
    · rcases (references _ _).mp owner' with ⟨rfl, equal⟩ | ⟨_, old'⟩
      · exact False.elim (different
          (invariant.unique place source id old (equal ▸ stored)))
      · exact invariant.unique place other id old old'
  · intro place other id owner shared
    rcases (references _ _).mp owner with ⟨_, equal⟩ | ⟨_, old⟩
    · rcases (references _ _).mp shared with ⟨_, equal'⟩ | ⟨_, old'⟩
      · cases equal.trans equal'.symm
      · exact invariant.exclusive source other id (equal ▸ stored) old'
    · rcases (references _ _).mp shared with ⟨_, equal⟩ | ⟨_, old'⟩
      · exact invariant.exclusive place source id old (equal ▸ stored)
      · exact invariant.exclusive place other id old old'

theorem OwnershipInvariant.transportOwners {before after : State Primitive}
    (invariant : OwnershipInvariant before)
    (owned : ∀ place id,
      ReferenceAt after place (.owned id) ↔ ReferenceAt before place (.owned id))
    (showned : ∀ place id,
      ReferenceAt after place (.showned id) ↔ ReferenceAt before place (.showned id))
    (objects : ∀ id, AllocatedObject after id ↔ AllocatedObject before id) :
    OwnershipInvariant after := by
  constructor
  · intro place id owner
    apply (objects id).mpr
    apply invariant.targetsLive place id
    rcases owner with owner | owner
    · exact Or.inl ((owned _ _).mp owner)
    · exact Or.inr ((showned _ _).mp owner)
  · intro id live
    obtain ⟨place, owner⟩ := invariant.hasOwner id ((objects id).mp live)
    refine ⟨place, ?_⟩
    rcases owner with owner | owner
    · exact Or.inl ((owned _ _).mpr owner)
    · exact Or.inr ((showned _ _).mpr owner)
  · intro place other id owner owner'
    exact invariant.unique place other id ((owned _ _).mp owner) ((owned _ _).mp owner')
  · intro place other id owner owner'
    exact invariant.exclusive place other id ((owned _ _).mp owner) ((showned _ _).mp owner')

theorem OwnershipInvariant.duplicateShared {before after : State Primitive}
    (invariant : OwnershipInvariant before) (source destination : Place)
    (id : ObjectId) (stored : ReferenceAt before source (.showned id))
    (references : ∀ place reference, ReferenceAt after place reference ↔
      (place = destination ∧ reference = .showned id) ∨ ReferenceAt before place reference)
    (objects : ∀ other, AllocatedObject after other ↔ AllocatedObject before other) :
    OwnershipInvariant after := by
  constructor
  · intro place other owner
    apply (objects other).mpr
    rcases owner with owner | owner
    · rcases (references _ _).mp owner with ⟨_, equal⟩ | old
      · cases equal
      · exact invariant.targetsLive place other (Or.inl old)
    · rcases (references _ _).mp owner with ⟨_, equal⟩ | old
      · cases equal
        exact invariant.targetsLive source id (Or.inr stored)
      · exact invariant.targetsLive place other (Or.inr old)
  · intro other live
    obtain ⟨place, owner⟩ := invariant.hasOwner other ((objects other).mp live)
    refine ⟨place, ?_⟩
    rcases owner with owner | owner
    · exact Or.inl ((references _ _).mpr (Or.inr owner))
    · exact Or.inr ((references _ _).mpr (Or.inr owner))
  · intro place other target owner owner'
    rcases (references _ _).mp owner with ⟨_, equal⟩ | old
    · cases equal
    · rcases (references _ _).mp owner' with ⟨_, equal⟩ | old'
      · cases equal
      · exact invariant.unique place other target old old'
  · intro place other target owner shared
    rcases (references _ _).mp owner with ⟨_, equal⟩ | old
    · cases equal
    · rcases (references _ _).mp shared with ⟨_, equal⟩ | old'
      · cases equal
        exact invariant.exclusive place source id old stored
      · exact invariant.exclusive place other target old old'

theorem OwnerAt.target_unique {state : State Primitive} {place : Place} {id other : ObjectId}
    (owner : OwnerAt state place id) (owner' : OwnerAt state place other) : id = other := by
  rcases owner with owner | owner <;> rcases owner' with owner' | owner'
  · exact Reference.owned.inj (Slot.initialized.inj (Stored.value_unique owner owner'))
  · have incompatible := Slot.initialized.inj (Stored.value_unique owner owner')
    cases incompatible
  · have incompatible := Slot.initialized.inj (Stored.value_unique owner owner')
    cases incompatible
  · exact Reference.showned.inj (Slot.initialized.inj (Stored.value_unique owner owner'))

-- Dropping a final owner of an object with no reference-bearing contents removes
-- exactly that occurrence and object. Recursive destruction needs its own effect
-- proof before it can use a more general invariant-preservation theorem.
theorem OwnershipInvariant.dropLeaf {before after : State Primitive}
    (invariant : OwnershipInvariant before) (source : Place) (id : ObjectId)
    (stored : OwnerAt before source id)
    (lastOwner : ∀ place, OwnerAt before place id → place = source)
    (references : ∀ place reference, ReferenceAt after place reference ↔
      place ≠ source ∧ ReferenceAt before place reference)
    (objects : ∀ other, AllocatedObject after other ↔ AllocatedObject before other ∧ other ≠ id) :
    OwnershipInvariant after := by
  have old_owner : ∀ place target, OwnerAt after place target →
      place ≠ source ∧ OwnerAt before place target := by
    intro place target owner
    rcases owner with owner | owner
    · obtain ⟨different, owner⟩ := (references _ _).mp owner
      exact ⟨different, Or.inl owner⟩
    · obtain ⟨different, owner⟩ := (references _ _).mp owner
      exact ⟨different, Or.inr owner⟩
  constructor
  · intro place target owner
    obtain ⟨different, owner⟩ := old_owner place target owner
    apply (objects target).mpr
    refine ⟨invariant.targetsLive place target owner, ?_⟩
    intro equal
    subst target
    exact different (lastOwner place owner)
  · intro target live
    obtain ⟨live, different⟩ := (objects target).mp live
    obtain ⟨place, owner⟩ := invariant.hasOwner target live
    have different_place : place ≠ source := by
      intro equal
      subst place
      exact different (owner.target_unique stored)
    refine ⟨place, ?_⟩
    rcases owner with owner | owner
    · exact Or.inl ((references _ _).mpr ⟨different_place, owner⟩)
    · exact Or.inr ((references _ _).mpr ⟨different_place, owner⟩)
  · intro place other target owner owner'
    exact invariant.unique place other target
      ((references _ _).mp owner).2 ((references _ _).mp owner').2
  · intro place other target owner owner'
    exact invariant.exclusive place other target
      ((references _ _).mp owner).2 ((references _ _).mp owner').2

theorem OwnershipInvariant.releaseShared {before after : State Primitive}
    (invariant : OwnershipInvariant before) (source other : Place) (id : ObjectId)
    (stored : ReferenceAt before source (.showned id))
    (remaining : ReferenceAt before other (.showned id)) (different : other ≠ source)
    (references : ∀ place reference, ReferenceAt after place reference ↔
      place ≠ source ∧ ReferenceAt before place reference)
    (objects : ∀ target, AllocatedObject after target ↔ AllocatedObject before target) :
    OwnershipInvariant after := by
  constructor
  · intro place target owner
    apply (objects target).mpr
    apply invariant.targetsLive place target
    rcases owner with owner | owner
    · exact Or.inl ((references _ _).mp owner).2
    · exact Or.inr ((references _ _).mp owner).2
  · intro target live
    obtain ⟨place, owner⟩ := invariant.hasOwner target ((objects target).mp live)
    by_cases same : place = source
    · subst place
      have equal : target = id := owner.target_unique (Or.inr stored)
      subst target
      exact ⟨other, Or.inr ((references _ _).mpr ⟨different, remaining⟩)⟩
    · refine ⟨place, ?_⟩
      rcases owner with owner | owner
      · exact Or.inl ((references _ _).mpr ⟨same, owner⟩)
      · exact Or.inr ((references _ _).mpr ⟨same, owner⟩)
  · intro place other target owner owner'
    exact invariant.unique place other target
      ((references _ _).mp owner).2 ((references _ _).mp owner').2
  · intro place other target owner owner'
    exact invariant.exclusive place other target
      ((references _ _).mp owner).2 ((references _ _).mp owner').2

-- The pointwise invariant entails the paper's disjunction: exactly one owned
-- occurrence and no showned occurrence, or at least one showned occurrence and
-- no owned occurrence. Places distinguish occurrences even when values match.
theorem OwnershipInvariant.ownership_cases {state : State Primitive}
    (invariant : OwnershipInvariant state) (id : ObjectId) (live : AllocatedObject state id) :
    (∃ place, ReferenceAt state place (.owned id) ∧
      (∀ other, ReferenceAt state other (.owned id) → other = place) ∧
      (∀ other, ¬ ReferenceAt state other (.showned id))) ∨
    (∃ place, ReferenceAt state place (.showned id) ∧
      (∀ other, ¬ ReferenceAt state other (.owned id))) := by
  obtain ⟨place, owner⟩ := invariant.hasOwner id live
  rcases owner with owner | owner
  · exact Or.inl ⟨place, owner,
      fun other owner' => invariant.unique other place id owner' owner,
      fun other => invariant.exclusive place other id owner⟩
  · exact Or.inr ⟨place, owner,
      fun other owner' => invariant.exclusive other place id owner' owner⟩

theorem OwnershipInvariant.addBorrow {before after : State Primitive}
    (invariant : OwnershipInvariant before) (destination : Place) (reference : Reference)
    (nonowning : ∀ id, reference ≠ .owned id ∧ reference ≠ .showned id)
    (references : ∀ place result, ReferenceAt after place result ↔
      (place = destination ∧ result = reference) ∨ ReferenceAt before place result)
    (objects : ∀ id, AllocatedObject after id ↔ AllocatedObject before id) :
    OwnershipInvariant after := by
  apply invariant.transportOwners (objects := objects)
  · intro place id
    rw [references]
    have unequal := (nonowning id).1
    simp only [Ne.symm unequal, and_false, false_or]
  · intro place id
    rw [references]
    have unequal := (nonowning id).2
    simp only [Ne.symm unequal, and_false, false_or]

theorem OwnershipInvariant.removeBorrow {before after : State Primitive}
    (invariant : OwnershipInvariant before) (source : Place) (reference : Reference)
    (stored : ReferenceAt before source reference)
    (nonowning : ∀ id, reference ≠ .owned id ∧ reference ≠ .showned id)
    (references : ∀ place result, ReferenceAt after place result ↔
      place ≠ source ∧ ReferenceAt before place result)
    (objects : ∀ id, AllocatedObject after id ↔ AllocatedObject before id) :
    OwnershipInvariant after := by
  apply invariant.transportOwners (objects := objects)
  · intro place id
    rw [references]
    constructor
    · exact And.right
    · intro owner
      refine ⟨?_, owner⟩
      intro equal
      subst place
      exact (nonowning id).1 (Slot.initialized.inj (Stored.value_unique stored owner))
  · intro place id
    rw [references]
    constructor
    · exact And.right
    · intro owner
      refine ⟨?_, owner⟩
      intro equal
      subst place
      exact (nonowning id).2 (Slot.initialized.inj (Stored.value_unique stored owner))

-- ANCHOR: duplicate_unique_owners
example (value : Primitive) :
    let x : VariableId := ⟨0⟩
    let y : VariableId := ⟨1⟩
    let α : ObjectId := ⟨0⟩
    let malformed : State Primitive :=
      .state ⟨[(α, .primitive value)], by simp⟩
        ⟨[(x, .initialized (.owned α)), (y, .initialized (.owned α))], by decide⟩
    ¬ OwnershipInvariant malformed := by
  dsimp only
  intro invariant
  have equal := invariant.unique (.variable ⟨0⟩) (.variable ⟨1⟩) ⟨0⟩
    (by simp [ReferenceAt, Stored]) (by simp [ReferenceAt, Stored])
  cases equal
-- ANCHOR_END: duplicate_unique_owners

-- ANCHOR: creation_preserves_ownership
example :
    let x : VariableId := ⟨0⟩
    let α : ObjectId := ⟨0⟩
    let allocated : State Int :=
      .state .empty ⟨[(x, .uninitialized)], by simp⟩
    let created : State Int :=
      .state ⟨[(α, .primitive 22)], by simp⟩
        ⟨[(x, .initialized (.owned α))], by simp⟩
    Reachable Int allocated ∧ Reachable Int created ∧ OwnershipInvariant created := by
  have allocation := Step.allocVariable (Primitive := Int) FiniteMap.empty FiniteMap.empty
    (VariableId.mk 0) (by simp [FiniteMap.empty])
  have creation := Step.createPrimitive (Primitive := Int) FiniteMap.empty
    (FiniteMap.mk [(VariableId.mk 0, Slot.uninitialized)] (by simp)) 22
    (VariableId.mk 0) (by simp) (ObjectId.mk 0) (by simp [FiniteMap.empty])
  have reachable := Reachable.step (Reachable.step Reachable.initial allocation) creation
  exact ⟨Reachable.step Reachable.initial allocation,
    reachable, reachable_ownershipInvariant reachable⟩
-- ANCHOR_END: creation_preserves_ownership

end Dada.Heap
