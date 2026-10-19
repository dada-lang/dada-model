import Heap

namespace Dada.Heap

variable {Primitive : Type}

deriving instance DecidableEq for Place

-- Lookup distinguishes a missing slot from a present, uninitialized slot.
def FiniteMap.lookup [DecidableEq Key] (map : FiniteMap Key Value) (key : Key) :
    Option Value := map.entries.lookup key

theorem FiniteMap.lookup_eq_some [DecidableEq Key] (map : FiniteMap Key Value)
    {key : Key} {value : Value} :
    map.lookup key = some value ↔ (key, value) ∈ map.entries := by
  constructor
  · intro found
    obtain ⟨before, after, entries, _⟩ := List.lookup_eq_some_iff.mp found
    simp [entries]
  · intro member
    have presentSome : (map.lookup key).isSome := by
      apply List.lookup_isSome_iff.mpr
      exact ⟨(key, value), member, by simp⟩
    obtain ⟨found, equal⟩ := Option.isSome_iff_exists.mp presentSome
    obtain ⟨before, after, entries, _⟩ := List.lookup_eq_some_iff.mp equal
    have present : (key, found) ∈ map.entries := by simp [entries]
    have same := map.value_unique present member
    simpa [same] using equal

private theorem lookup_replaced [DecidableEq Key] (entries : List (Key × Value))
    (key other : Key) (value : Value) :
    (entries.map fun entry =>
      (entry.1, if entry.1 = key then value else entry.2)).lookup other =
      if other = key then (entries.lookup key).map (fun _ => value)
      else entries.lookup other := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
    rcases entry with ⟨head, previous⟩
    by_cases same : other = key
    · subst other
      by_cases hit : key = head
      · subst head
        simp
      · simp [List.lookup_cons, beq_eq_false_iff_ne.mpr hit, Ne.symm hit, ih]
    · by_cases hit : other = head
      · subst head
        simp [same]
      · simp [List.lookup_cons, beq_eq_false_iff_ne.mpr hit, same, ih]

theorem FiniteMap.lookup_replace [DecidableEq Key] (map : FiniteMap Key Value)
    (key other : Key) (value : Value) :
    (map.replace key value).lookup other =
      if other = key then (map.lookup key).map (fun _ => value)
      else map.lookup other := lookup_replaced map.entries key other value

-- These are storage operations, not permission checks. Access-path resolution
-- must separately establish the authority to read or replace the chosen slot.
def readSlot : State Primitive → Place → Option Slot
  | .state _ variables, .variable id => variables.lookup id
  | .state objects _, .field id name => do
      let .aggregate fields ← objects.lookup id | none
      fields.lookup name
  | .state objects _, .element id index => do
      let .array elements ← objects.lookup id | none
      elements[index]?

-- A write never creates a variable, field, or array element. It changes only
-- an existing slot; missing objects, wrong shapes, and bad indices return none.
def writeSlot : State Primitive → Place → Slot → Option (State Primitive)
  | .state objects variables, .variable id, slot => do
      let _ ← variables.lookup id
      some (.state objects (variables.replace id slot))
  | .state objects variables, .field id name, slot => do
      let .aggregate fields ← objects.lookup id | none
      let _ ← fields.lookup name
      some (.state (objects.replace id (.aggregate (fields.replace name slot))) variables)
  | .state objects variables, .element id index, slot => do
      let .array elements ← objects.lookup id | none
      if bounds : index < elements.size then
        some (.state (objects.replace id (.array (elements.set index slot bounds))) variables)
      else none

theorem readSlot_variable_iff (objects : FiniteMap ObjectId (Object Primitive))
    (variables : FiniteMap VariableId Slot) (id : VariableId) (slot : Slot) :
    readSlot (.state objects variables) (.variable id) = some slot ↔
      (id, slot) ∈ variables.entries := FiniteMap.lookup_eq_some variables

theorem readSlot_field_iff (objects : FiniteMap ObjectId (Object Primitive))
    (variables : FiniteMap VariableId Slot) (id : ObjectId) (name : FieldName) (slot : Slot) :
    readSlot (.state objects variables) (.field id name) = some slot ↔
      ∃ fields, (id, Object.aggregate fields) ∈ objects.entries ∧
        (name, slot) ∈ fields.entries := by
  simp only [readSlot, bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨object, found, field⟩
    cases object with
    | primitive value => simp at field
    | array elements => simp at field
    | aggregate fields =>
      exact ⟨fields, objects.lookup_eq_some.mp found, fields.lookup_eq_some.mp field⟩
  · rintro ⟨fields, found, field⟩
    exact ⟨.aggregate fields, objects.lookup_eq_some.mpr found, fields.lookup_eq_some.mpr field⟩

theorem readSlot_element_iff (objects : FiniteMap ObjectId (Object Primitive))
    (variables : FiniteMap VariableId Slot) (id : ObjectId) (index : Nat) (slot : Slot) :
    readSlot (.state objects variables) (.element id index) = some slot ↔
      ∃ elements, (id, Object.array elements) ∈ objects.entries ∧
        elements[index]? = some slot := by
  simp only [readSlot, bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨object, found, element⟩
    cases object with
    | primitive value => simp at element
    | aggregate fields => simp at element
    | array elements => exact ⟨elements, objects.lookup_eq_some.mp found, element⟩
  · rintro ⟨elements, found, element⟩
    exact ⟨.array elements, objects.lookup_eq_some.mpr found, element⟩

theorem writeSlot_effects {before after : State Primitive} {place : Place} {slot : Slot}
    (written : writeSlot before place slot = some after) (other : Place) :
    readSlot after other = if other = place then some slot else readSlot before other := by
  cases before with
  | state objects variables =>
    cases place with
    | «variable» id =>
      cases found : variables.lookup id with
      | none => simp [writeSlot, found] at written
      | some previous =>
        simp [writeSlot, found] at written
        cases written
        cases other <;> simp [readSlot, FiniteMap.lookup_replace, found]
    | field id name =>
      cases found : objects.lookup id with
      | none => simp [writeSlot, found] at written
      | some object =>
        cases object with
        | primitive value => simp [writeSlot, found] at written
        | array elements => simp [writeSlot, found] at written
        | aggregate fields =>
          cases fieldFound : fields.lookup name with
          | none => simp [writeSlot, found, fieldFound] at written
          | some previous =>
            simp [writeSlot, found, fieldFound] at written
            cases written
            cases other with
            | «variable» other => simp [readSlot]
            | field other otherName =>
              by_cases same : other = id
              · subst other
                simp [readSlot, FiniteMap.lookup_replace, found, fieldFound]
              · simp [readSlot, FiniteMap.lookup_replace, same]
            | element other otherIndex =>
              by_cases same : other = id
              · subst other
                simp [readSlot, FiniteMap.lookup_replace, found]
              · simp [readSlot, FiniteMap.lookup_replace, same]
    | element id index =>
      cases found : objects.lookup id with
      | none => simp [writeSlot, found] at written
      | some object =>
        cases object with
        | primitive value => simp [writeSlot, found] at written
        | aggregate fields => simp [writeSlot, found] at written
        | array elements =>
          by_cases bounds : index < elements.size
          · simp [writeSlot, found, bounds] at written
            cases written
            cases other with
            | «variable» other => simp [readSlot]
            | field other otherName =>
              by_cases same : other = id
              · subst other
                simp [readSlot, FiniteMap.lookup_replace, found]
              · simp [readSlot, FiniteMap.lookup_replace, same]
            | element other otherIndex =>
              by_cases same : other = id
              · subst other
                simp [readSlot, FiniteMap.lookup_replace, found, Array.getElem?_set, eq_comm]
              · simp [readSlot, FiniteMap.lookup_replace, same]
          · simp [writeSlot, found, bounds] at written

theorem writeSlot_reads_back {before after : State Primitive} {place : Place} {slot : Slot}
    (written : writeSlot before place slot = some after) : readSlot after place = some slot := by
  simpa using writeSlot_effects written place

theorem writeSlot_preserves_other {before after : State Primitive}
    {place other : Place} {slot : Slot}
    (written : writeSlot before place slot = some after) (different : other ≠ place) :
    readSlot after other = readSlot before other := by
  simpa [different] using writeSlot_effects written other

theorem writeSlot_isSome_iff (state : State Primitive) (place : Place) (slot : Slot) :
    (writeSlot state place slot).isSome ↔ (readSlot state place).isSome := by
  cases state with
  | state objects variables =>
    cases place with
    | «variable» id =>
      cases found : variables.lookup id <;> simp [writeSlot, readSlot, found]
    | field id name =>
      cases found : objects.lookup id with
      | none => simp [writeSlot, readSlot, found]
      | some object =>
        cases object with
        | primitive value => simp [writeSlot, readSlot, found]
        | array elements => simp [writeSlot, readSlot, found]
        | aggregate fields =>
          cases fieldFound : fields.lookup name <;> simp [writeSlot, readSlot, found, fieldFound]
    | element id index =>
      cases found : objects.lookup id with
      | none => simp [writeSlot, readSlot, found]
      | some object =>
        cases object with
        | primitive value => simp [writeSlot, readSlot, found]
        | aggregate fields => simp [writeSlot, readSlot, found]
        | array elements =>
          by_cases bounds : index < elements.size
          · simp [writeSlot, readSlot, found, bounds]
          · simp [writeSlot, readSlot, found, bounds]

theorem writeSlot_none_iff (state : State Primitive) (place : Place) (slot : Slot) :
    writeSlot state place slot = none ↔ readSlot state place = none := by
  have same := writeSlot_isSome_iff state place slot
  cases written : writeSlot state place slot <;> cases read : readSlot state place <;>
    simp_all

-- Allocation order and the set of allocated objects are independent of slot
-- contents: no storage write changes either sequence of identities.
theorem writeSlot_preserves_keys
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot} {place : Place} {slot : Slot}
    (written : writeSlot (.state objects variables) place slot =
      some (.state objects' variables')) :
    objects'.entries.map Prod.fst = objects.entries.map Prod.fst ∧
      variables'.entries.map Prod.fst = variables.entries.map Prod.fst := by
  cases place with
  | «variable» id =>
    cases found : variables.lookup id with
    | none => simp [writeSlot, found] at written
    | some previous =>
      simp [writeSlot, found] at written
      rcases written with ⟨rfl, rfl⟩
      simp [FiniteMap.replace_keys]
  | field id name =>
    cases found : objects.lookup id with
    | none => simp [writeSlot, found] at written
    | some object =>
      cases object with
      | primitive value => simp [writeSlot, found] at written
      | array elements => simp [writeSlot, found] at written
      | aggregate fields =>
        cases fieldFound : fields.lookup name with
        | none => simp [writeSlot, found, fieldFound] at written
        | some previous =>
          simp [writeSlot, found, fieldFound] at written
          rcases written with ⟨rfl, rfl⟩
          simp [FiniteMap.replace_keys]
  | element id index =>
    cases found : objects.lookup id with
    | none => simp [writeSlot, found] at written
    | some object =>
      cases object with
      | primitive value => simp [writeSlot, found] at written
      | aggregate fields => simp [writeSlot, found] at written
      | array elements =>
        by_cases bounds : index < elements.size
        · simp [writeSlot, found, bounds] at written
          rcases written with ⟨rfl, rfl⟩
          simp [FiniteMap.replace_keys]
        · simp [writeSlot, found, bounds] at written

theorem writeSlot_preserves_variable_order
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot} {place : Place} {slot : Slot}
    (written : writeSlot (.state objects variables) place slot =
      some (.state objects' variables')) :
    variables'.entries.map Prod.fst = variables.entries.map Prod.fst :=
  (writeSlot_preserves_keys written).2

end Dada.Heap
