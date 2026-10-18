import PlaceEffects

namespace Dada.Heap

variable {Primitive : Type}

-- Mapping values leaves the keys and their allocation order unchanged.
def FiniteMap.mapValues (f : Value → Result) (map : FiniteMap Key Value) :
    FiniteMap Key Result where
  entries := map.entries.map fun entry => (entry.1, f entry.2)
  uniqueKeys := by
    simpa only [List.map_map, Function.comp_def] using map.uniqueKeys

@[simp] theorem FiniteMap.mapValues_keys (f : Value → Result) (map : FiniteMap Key Value) :
    (map.mapValues f).entries.map Prod.fst = map.entries.map Prod.fst := by
  simp [mapValues, List.map_map, Function.comp_def]

private theorem lookup_mappedEntries [DecidableEq Key] (f : Value → Result)
    (entries : List (Key × Value)) (key : Key) :
    (entries.map fun entry => (entry.1, f entry.2)).lookup key =
      (entries.lookup key).map f := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
    rcases entry with ⟨head, value⟩
    by_cases same : key = head
    · subst head
      simp
    · simp [List.lookup_cons, beq_eq_false_iff_ne.mpr same, ih]

@[simp] theorem FiniteMap.lookup_mapValues [DecidableEq Key] (f : Value → Result)
    (map : FiniteMap Key Value) (key : Key) :
    (map.mapValues f).lookup key = (map.lookup key).map f :=
  lookup_mappedEntries f map.entries key

def Slot.mapReferences (f : Reference → Reference) : Slot → Slot
  | .uninitialized => .uninitialized
  | .initialized reference => .initialized (f reference)

def Object.mapReferences (f : Reference → Reference) : Object Primitive → Object Primitive
  | .primitive value => .primitive value
  | .aggregate fields => .aggregate (fields.mapValues (Slot.mapReferences f))
  | .array elements => .array (elements.map (Slot.mapReferences f))

-- This is a simultaneous transformation of every stored reference, including
-- references in fields and array elements. It neither creates nor removes slots.
def mapReferences (f : Reference → Reference) : State Primitive → State Primitive
  | .state objects variables =>
      .state (objects.mapValues (Object.mapReferences f))
        (variables.mapValues (Slot.mapReferences f))

theorem mapReferences_keys (f : Reference → Reference)
    (objects : FiniteMap ObjectId (Object Primitive)) (variables : FiniteMap VariableId Slot) :
    let .state objects' variables' := mapReferences f (.state objects variables)
    objects'.entries.map Prod.fst = objects.entries.map Prod.fst ∧
      variables'.entries.map Prod.fst = variables.entries.map Prod.fst := by
  simp [mapReferences]

theorem readSlot_mapReferences (f : Reference → Reference) (state : State Primitive)
    (place : Place) :
    readSlot (mapReferences f state) place =
      (readSlot state place).map (Slot.mapReferences f) := by
  cases state with
  | state objects variables =>
    cases place with
    | «variable» id => simp [mapReferences, readSlot]
    | field id name =>
      simp only [mapReferences, readSlot, FiniteMap.lookup_mapValues]
      cases found : objects.lookup id with
      | none => rfl
      | some object =>
        cases object <;> simp [Object.mapReferences]
    | element id index =>
      simp only [mapReferences, readSlot, FiniteMap.lookup_mapValues]
      cases found : objects.lookup id with
      | none => rfl
      | some object =>
        cases object <;> simp [Object.mapReferences]

theorem mapReferences_liveObjects (f : Reference → Reference) (state : State Primitive)
    (id : ObjectId) : AllocatedObject (mapReferences f state) id ↔ AllocatedObject state id := by
  cases state
  simp [mapReferences, AllocatedObject]

theorem mapReferences_references (f : Reference → Reference) (state : State Primitive)
    (place : Place) (reference : Reference) :
    ReferenceAt (mapReferences f state) place reference ↔
      ∃ previous, ReferenceAt state place previous ∧ f previous = reference := by
  simp only [ReferenceAt, ← readSlot_stored, readSlot_mapReferences]
  cases found : readSlot state place with
  | none => simp
  | some slot =>
    cases slot <;> simp [Slot.mapReferences]

-- A reference transformation may change borrows freely but must preserve, and
-- never manufacture, each owning reference to use this ownership theorem.
def PreservesOwners (f : Reference → Reference) : Prop :=
  (∀ reference id, f reference = .owned id ↔ reference = .owned id) ∧
    (∀ reference id, f reference = .showned id ↔ reference = .showned id)

theorem mapReferences_preserves_ownership (f : Reference → Reference)
    (preserves : PreservesOwners f) {state : State Primitive}
    (invariant : OwnershipInvariant state) : OwnershipInvariant (mapReferences f state) := by
  apply invariant.transportOwners
  · intro place id
    rw [mapReferences_references]
    simp only [preserves.1]
    simp
  · intro place id
    rw [mapReferences_references]
    simp only [preserves.2]
    simp
  · exact mapReferences_liveObjects f state

-- A direct dependent lease follows a moved supporting reference. Applying this
-- once is sufficient: descendants continue to point to their unchanged parents.
def retargetReference (source destination : Place) : Reference → Reference
  | .leased place => .leased (if place = source then destination else place)
  | reference => reference

def retargetLeases (source destination : Place) (state : State Primitive) : State Primitive :=
  mapReferences (retargetReference source destination) state

theorem retargetReference_preservesOwners (source destination : Place) :
    PreservesOwners (retargetReference source destination) := by
  constructor <;> intro reference id <;> cases reference <;> simp [retargetReference]

theorem retargetLeases_preserves_ownership (source destination : Place)
    {state : State Primitive} (invariant : OwnershipInvariant state) :
    OwnershipInvariant (retargetLeases source destination state) :=
  mapReferences_preserves_ownership _ (retargetReference_preservesOwners source destination) invariant

theorem readSlot_retargetLeases (source destination place : Place) (state : State Primitive) :
    readSlot (retargetLeases source destination state) place =
      (readSlot state place).map (Slot.mapReferences (retargetReference source destination)) :=
  readSlot_mapReferences _ state place

theorem retargetLeases_keys (source destination : Place)
    (objects : FiniteMap ObjectId (Object Primitive)) (variables : FiniteMap VariableId Slot) :
    let .state objects' variables' := retargetLeases source destination (.state objects variables)
    objects'.entries.map Prod.fst = objects.entries.map Prod.fst ∧
      variables'.entries.map Prod.fst = variables.entries.map Prod.fst :=
  mapReferences_keys _ objects variables

theorem retargetLeases_dependent {state : State Primitive}
    (source destination place : Place)
    (dependent : ReferenceAt state place (.leased source)) :
    ReferenceAt (retargetLeases source destination state) place (.leased destination) := by
  apply (mapReferences_references _ state place _).mpr
  exact ⟨.leased source, dependent, by simp [retargetReference]⟩

theorem retargetLeases_other_support {state : State Primitive}
    (source destination place support : Place) (different : support ≠ source)
    (dependent : ReferenceAt state place (.leased support)) :
    ReferenceAt (retargetLeases source destination state) place (.leased support) := by
  apply (mapReferences_references _ state place _).mpr
  exact ⟨.leased support, dependent, by simp [retargetReference, different]⟩

-- All direct dependents are transformed, wherever their occurrences are stored.
-- The descendant supported by y continues to point to y, not to z.
-- ANCHOR: retarget_all_storage
example :
    let x : VariableId := ⟨0⟩
    let y : VariableId := ⟨1⟩
    let z : VariableId := ⟨2⟩
    let α : ObjectId := ⟨0⟩
    let β : ObjectId := ⟨1⟩
    let before : State Int := .state
      ⟨[(α, .aggregate ⟨[("array", .initialized (.owned β)),
          ("borrow", .initialized (.leased (.variable x)))], by decide⟩),
        (β, .array #[.initialized (.leased (.variable x)),
          .initialized (.leased (.variable y))])], by decide⟩
      ⟨[(z, .uninitialized), (y, .initialized (.leased (.variable x))),
        (x, .initialized (.owned α))], by decide⟩
    let after : State Int := .state
      ⟨[(α, .aggregate ⟨[("array", .initialized (.owned β)),
          ("borrow", .initialized (.leased (.variable z)))], by decide⟩),
        (β, .array #[.initialized (.leased (.variable z)),
          .initialized (.leased (.variable y))])], by decide⟩
      ⟨[(z, .uninitialized), (y, .initialized (.leased (.variable z))),
        (x, .initialized (.owned α))], by decide⟩
    retargetLeases (.variable x) (.variable z) before = after := by
  simp [retargetLeases, mapReferences, Object.mapReferences, Slot.mapReferences,
    FiniteMap.mapValues, retargetReference]
-- ANCHOR_END: retarget_all_storage

end Dada.Heap
