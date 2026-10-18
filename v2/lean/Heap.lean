import Std

namespace Dada.Heap

-- Primitive is a parameter of the whole model, implicit in uses of its types.
variable (Primitive : Type)

structure ObjectId where
  index : Nat
  deriving DecidableEq

-- A runtime variable identity, not a source-level spelling. The execution layer
-- alpha-renames variables to distinct identities for distinct allocation lifetimes.
structure VariableId where
  index : Nat
  deriving DecidableEq

abbrev FieldName := String

-- A finite map with no duplicate keys; absence differs from uninitialized.
structure FiniteMap (Key Value : Type) where
  entries : List (Key × Value)
  uniqueKeys : (entries.map Prod.fst).Nodup

inductive Place where
  | variable (id : VariableId)
  | field (object : ObjectId) (name : FieldName)
  | element (array : ObjectId) (index : Nat)

inductive Reference where
  | owned (object : ObjectId)
  | leased (place : Place)
  | showned (object : ObjectId)
  | shlease (object : ObjectId)

inductive Slot where
  | uninitialized
  | initialized (reference : Reference)

inductive Object where
  | primitive (value : Primitive)
  | aggregate (fields : FiniteMap FieldName Slot)
  | array (elements : Array Slot)

-- The variable store includes every live slot, including suspended callers.
-- Its entry order is the allocation stack, with the newest slot first.
-- Source scopes, call-stack visibility, and alpha-renaming belong to execution.
inductive State where
  | state
      (objects : FiniteMap ObjectId (Object Primitive))
      (variables : FiniteMap VariableId Slot)

inductive Projection where
  | field (name : FieldName)
  | index (index : Nat)

inductive AccessPath where
  | path (id : VariableId) (projections : List Projection)

-- Creation initializes an already allocated variable without reordering slots.
-- Deallocation pops only the newest slot and does not implicitly drop a value.
-- Other operations will extend this type.
inductive Operation where
  | allocVariable (id : VariableId)
  | deallocVariable (id : VariableId)
  | createPrimitive (value : Primitive) (destination : VariableId)
  | createAggregate (fields : List FieldName) (destination : VariableId)
  | createArray (length : Nat) (destination : VariableId)

def FiniteMap.empty : FiniteMap Key Value where
  entries := []
  uniqueKeys := List.nodup_nil

def State.initial : State Primitive :=
  .state FiniteMap.empty FiniteMap.empty

-- Allocation extends the finite map without replacing an existing entry.
def FiniteMap.insertFresh (map : FiniteMap Key Value) (key : Key) (value : Value)
    (fresh : key ∉ map.entries.map Prod.fst) : FiniteMap Key Value where
  entries := (key, value) :: map.entries
  uniqueKeys := List.nodup_cons.mpr ⟨fresh, map.uniqueKeys⟩

-- Removing a key preserves every entry with a different key.
def FiniteMap.erase [DecidableEq Key] (map : FiniteMap Key Value) (key : Key) :
    FiniteMap Key Value where
  entries := map.entries.filter fun entry => decide (entry.1 ≠ key)
  uniqueKeys := map.uniqueKeys.sublist (List.filter_sublist.map Prod.fst)

-- Replacement preserves exactly the existing keys; an absent key stays absent.
def FiniteMap.replace [DecidableEq Key] (map : FiniteMap Key Value)
    (key : Key) (value : Value) : FiniteMap Key Value where
  entries := map.entries.map fun entry =>
    (entry.1, if entry.1 = key then value else entry.2)
  uniqueKeys := by
    simpa only [List.map_map, Function.comp_def] using map.uniqueKeys

def initialFields (names : List FieldName) (distinct : names.Nodup) :
    FiniteMap FieldName Slot where
  entries := names.map fun name => (name, Slot.uninitialized)
  uniqueKeys := by
    simpa [List.map_map, Function.comp_def] using distinct

def initialElements (length : Nat) : Array Slot :=
  Array.replicate length .uninitialized

-- Successful steps are relations; missing rules do not define faults. The heap
-- checks only current absence at allocation. The execution layer must supply a
-- new identity for each variable lifetime: these rules alone permit reuse after
-- deallocation and do not establish lease invalidation or global freshness.
inductive Step : State Primitive → Operation Primitive → State Primitive → Prop where
  | allocVariable
      (objects : FiniteMap ObjectId (Object Primitive))
      (variables : FiniteMap VariableId Slot)
      (id : VariableId)
      (fresh : id ∉ variables.entries.map Prod.fst) :
      Step (.state objects variables) (.allocVariable id)
        (.state objects (variables.insertFresh id .uninitialized fresh))
  | deallocVariable
      (objects : FiniteMap ObjectId (Object Primitive))
      (variables : FiniteMap VariableId Slot)
      (id : VariableId)
      (empty : (id, Slot.uninitialized) ∈ variables.entries)
      (top : variables.entries.head?.map Prod.fst = some id) :
      Step (.state objects variables) (.deallocVariable id)
        (.state objects (variables.erase id))
  | createPrimitive
      (objects : FiniteMap ObjectId (Object Primitive))
      (variables : FiniteMap VariableId Slot)
      (value : Primitive)
      (destination : VariableId)
      (empty : (destination, Slot.uninitialized) ∈ variables.entries)
      (id : ObjectId)
      (fresh : id ∉ objects.entries.map Prod.fst) :
      Step (.state objects variables) (.createPrimitive value destination)
        (.state (objects.insertFresh id (.primitive value) fresh)
          (variables.replace destination (.initialized (.owned id))))
  | createAggregate
      (objects : FiniteMap ObjectId (Object Primitive))
      (variables : FiniteMap VariableId Slot)
      (fields : List FieldName)
      (distinct : fields.Nodup)
      (destination : VariableId)
      (empty : (destination, Slot.uninitialized) ∈ variables.entries)
      (id : ObjectId)
      (fresh : id ∉ objects.entries.map Prod.fst) :
      Step (.state objects variables) (.createAggregate fields destination)
        (.state (objects.insertFresh id (.aggregate (initialFields fields distinct)) fresh)
          (variables.replace destination (.initialized (.owned id))))
  | createArray
      (objects : FiniteMap ObjectId (Object Primitive))
      (variables : FiniteMap VariableId Slot)
      (length : Nat)
      (destination : VariableId)
      (empty : (destination, Slot.uninitialized) ∈ variables.entries)
      (id : ObjectId)
      (fresh : id ∉ objects.entries.map Prod.fst) :
      Step (.state objects variables) (.createArray length destination)
        (.state (objects.insertFresh id (.array (initialElements length)) fresh)
          (variables.replace destination (.initialized (.owned id))))

-- A unique-key map cannot associate two different contents with one identity.
theorem FiniteMap.value_unique (map : FiniteMap Key Value)
    {key : Key} {value value' : Value}
    (member : (key, value) ∈ map.entries)
    (member' : (key, value') ∈ map.entries) : value = value' := by
  obtain ⟨i, hi, entry⟩ := List.getElem_of_mem member
  obtain ⟨j, hj, entry'⟩ := List.getElem_of_mem member'
  have same_index : i = j := map.uniqueKeys.eq_of_getElem_eq
    (by simpa using hi) (by simpa using hj) (by simp [entry, entry'])
  subst j
  have same_entry : (key, value) = (key, value') := entry.symm.trans entry'
  exact (Prod.mk.inj same_entry).2

-- These statements are specific to the operation, so extending Step with other
-- operations does not silently broaden their scope.
theorem allocVariable_preserves_objects
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot} {id : VariableId}
    (step : Step Primitive (.state objects variables) (.allocVariable id)
      (.state objects' variables')) : objects' = objects := by
  cases step
  rfl

theorem allocVariable_contents
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot} {id : VariableId}
    (step : Step Primitive (.state objects variables) (.allocVariable id)
      (.state objects' variables')) {key : VariableId} {slot : Slot} :
    (key, slot) ∈ variables'.entries ↔
      (key = id ∧ slot = .uninitialized) ∨ (key, slot) ∈ variables.entries := by
  cases step
  simp [FiniteMap.insertFresh]

theorem allocVariable_pushes
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot} {id : VariableId}
    (step : Step Primitive (.state objects variables) (.allocVariable id)
      (.state objects' variables')) :
    variables'.entries = (id, .uninitialized) :: variables.entries := by
  cases step
  rfl

theorem allocVariable_requires_fresh
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot} {id : VariableId}
    (step : Step Primitive (.state objects variables) (.allocVariable id)
      (.state objects' variables')) : id ∉ variables.entries.map Prod.fst := by
  cases step with
  | allocVariable _ _ _ fresh => exact fresh

theorem deallocVariable_preserves_objects
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot} {id : VariableId}
    (step : Step Primitive (.state objects variables) (.deallocVariable id)
      (.state objects' variables')) : objects' = objects := by
  cases step
  rfl

theorem deallocVariable_contents
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot} {id : VariableId}
    (step : Step Primitive (.state objects variables) (.deallocVariable id)
      (.state objects' variables')) {key : VariableId} {slot : Slot} :
    (key, slot) ∈ variables'.entries ↔ (key, slot) ∈ variables.entries ∧ key ≠ id := by
  cases step
  simp [FiniteMap.erase]

theorem deallocVariable_requires_empty
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot} {id : VariableId}
    (step : Step Primitive (.state objects variables) (.deallocVariable id)
      (.state objects' variables')) : (id, Slot.uninitialized) ∈ variables.entries := by
  cases step with
  | deallocVariable _ _ _ empty _ => exact empty

theorem deallocVariable_requires_top
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot} {id : VariableId}
    (step : Step Primitive (.state objects variables) (.deallocVariable id)
      (.state objects' variables')) :
    variables.entries.head?.map Prod.fst = some id := by
  cases step with
  | deallocVariable _ _ _ _ top => exact top

theorem deallocVariable_pops
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot} {id : VariableId}
    (step : Step Primitive (.state objects variables) (.deallocVariable id)
      (.state objects' variables')) :
    variables.entries = (id, .uninitialized) :: variables'.entries := by
  cases step with
  | deallocVariable objects variables id empty top =>
    cases entries : variables.entries with
    | nil => simp [entries] at top
    | cons entry rest =>
      obtain ⟨key, value⟩ := entry
      have same_key : key = id := by simpa [entries] using top
      subst key
      have same_value : value = .uninitialized :=
        variables.value_unique (by simp [entries]) empty
      subst value
      have fresh : id ∉ rest.map Prod.fst :=
        (List.nodup_cons.mp (by simpa [entries] using variables.uniqueKeys)).1
      have unchanged : rest.filter (fun entry => decide (entry.1 ≠ id)) = rest := by
        apply List.filter_eq_self.mpr
        intro entry member
        simp only [decide_eq_true_eq]
        intro same
        exact fresh (same ▸ List.mem_map_of_mem member)
      change (id, .uninitialized) :: rest = (id, .uninitialized) ::
        variables.entries.filter (fun entry => decide (entry.1 ≠ id))
      rw [entries, List.filter_cons_of_neg (by simp), unchanged]

theorem deallocVariable_rejects_non_top
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot} {id : VariableId}
    (not_top : variables.entries.head?.map Prod.fst ≠ some id) :
    ¬ Step Primitive (.state objects variables) (.deallocVariable id)
      (.state objects' variables') := by
  intro step
  exact not_top (deallocVariable_requires_top Primitive step)

theorem deallocVariable_rejects_initialized
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot} {id : VariableId}
    {reference : Reference}
    (initialized : (id, Slot.initialized reference) ∈ variables.entries) :
    ¬ Step Primitive (.state objects variables) (.deallocVariable id)
      (.state objects' variables') := by
  intro step
  have incompatible := variables.value_unique initialized
    (deallocVariable_requires_empty Primitive step)
  cases incompatible

theorem deallocVariable_rejects_absent
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot} {id : VariableId}
    (absent : id ∉ variables.entries.map Prod.fst) :
    ¬ Step Primitive (.state objects variables) (.deallocVariable id)
      (.state objects' variables') := by
  intro step
  exact absent (List.mem_map_of_mem
    (deallocVariable_requires_empty Primitive step))

theorem FiniteMap.replace_keys [DecidableEq Key] (map : FiniteMap Key Value)
    (key : Key) (value : Value) :
    (map.replace key value).entries.map Prod.fst = map.entries.map Prod.fst := by
  simp [FiniteMap.replace, List.map_map, Function.comp_def]

theorem FiniteMap.replace_contents [DecidableEq Key] (map : FiniteMap Key Value)
    (key : Key) (value : Value) {other : Key} {result : Value} :
    (other, result) ∈ (map.replace key value).entries ↔
      ∃ previous, (other, previous) ∈ map.entries ∧
        result = if other = key then value else previous := by
  simp only [FiniteMap.replace, List.mem_map]
  constructor
  · rintro ⟨⟨other, previous⟩, member, equal⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
    exact ⟨previous, member, rfl⟩
  · rintro ⟨previous, member, rfl⟩
    exact ⟨(other, previous), member, rfl⟩

-- The constructors expose all changes, including the chosen fresh object ID.
theorem createPrimitive_effects
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot}
    {value : Primitive} {destination : VariableId}
    (step : Step Primitive (.state objects variables) (.createPrimitive value destination)
      (.state objects' variables')) :
    (destination, Slot.uninitialized) ∈ variables.entries ∧
      ∃ id, ∃ fresh : id ∉ objects.entries.map Prod.fst,
        objects' = objects.insertFresh id (.primitive value) fresh ∧
        variables' = variables.replace destination (.initialized (.owned id)) := by
  cases step with
  | createPrimitive _ _ _ _ empty id fresh =>
    exact ⟨empty, id, fresh, rfl, rfl⟩

theorem createAggregate_effects
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot}
    {fields : List FieldName} {destination : VariableId}
    (step : Step Primitive (.state objects variables) (.createAggregate fields destination)
      (.state objects' variables')) :
    (destination, Slot.uninitialized) ∈ variables.entries ∧
      ∃ distinct : fields.Nodup, ∃ id, ∃ fresh : id ∉ objects.entries.map Prod.fst,
        objects' = objects.insertFresh id (.aggregate (initialFields fields distinct)) fresh ∧
        variables' = variables.replace destination (.initialized (.owned id)) := by
  cases step with
  | createAggregate _ _ _ distinct _ empty id fresh =>
    exact ⟨empty, distinct, id, fresh, rfl, rfl⟩

theorem createArray_effects
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot}
    {length : Nat} {destination : VariableId}
    (step : Step Primitive (.state objects variables) (.createArray length destination)
      (.state objects' variables')) :
    (destination, Slot.uninitialized) ∈ variables.entries ∧
      ∃ id, ∃ fresh : id ∉ objects.entries.map Prod.fst,
        objects' = objects.insertFresh id (.array (initialElements length)) fresh ∧
        variables' = variables.replace destination (.initialized (.owned id)) := by
  cases step with
  | createArray _ _ _ _ empty id fresh =>
    exact ⟨empty, id, fresh, rfl, rfl⟩

theorem initialFields_contents
    (names : List FieldName) (distinct : names.Nodup)
    {name : FieldName} {slot : Slot} :
    (name, slot) ∈ (initialFields names distinct).entries ↔
      name ∈ names ∧ slot = .uninitialized := by
  simp only [initialFields, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨_, member, rfl, rfl⟩
    exact ⟨member, rfl⟩
  · rintro ⟨member, rfl⟩
    exact ⟨name, member, rfl, rfl⟩

theorem initialElements_size (length : Nat) :
    (initialElements length).size = length := by
  simp [initialElements]

theorem initialElements_contents (length : Nat) (index : Nat)
    (bound : index < (initialElements length).size) :
    (initialElements length)[index] = .uninitialized := by
  simp [initialElements]

-- This observation lets the common destination precondition be stated for all
-- three creation operations without adding another transition judgment.
def Operation.creationDestination {Primitive : Type} : Operation Primitive → Option VariableId
  | .createPrimitive _ destination => some destination
  | .createAggregate _ destination => some destination
  | .createArray _ destination => some destination
  | .allocVariable _ | .deallocVariable _ => none

theorem creation_requires_empty
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot}
    {operation : Operation Primitive} {destination : VariableId}
    (step : Step Primitive (.state objects variables) operation (.state objects' variables'))
    (creation : operation.creationDestination = some destination) :
    (destination, Slot.uninitialized) ∈ variables.entries := by
  cases step <;> simp_all [Operation.creationDestination]

theorem creation_preserves_variable_keys
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot}
    {operation : Operation Primitive} {destination : VariableId}
    (step : Step Primitive (.state objects variables) operation (.state objects' variables'))
    (creation : operation.creationDestination = some destination) :
    variables'.entries.map Prod.fst = variables.entries.map Prod.fst := by
  cases step <;> simp_all [Operation.creationDestination, FiniteMap.replace_keys]

-- Equality here preserves the full allocation order, not just the key set.
theorem creation_preserves_variable_order
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot}
    {operation : Operation Primitive} {destination : VariableId}
    (step : Step Primitive (.state objects variables) operation (.state objects' variables'))
    (creation : operation.creationDestination = some destination) :
    variables'.entries.map Prod.fst = variables.entries.map Prod.fst := by
  exact creation_preserves_variable_keys Primitive step creation

theorem creation_rejects_initialized
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot}
    {operation : Operation Primitive} {destination : VariableId} {reference : Reference}
    (creation : operation.creationDestination = some destination)
    (initialized : (destination, Slot.initialized reference) ∈ variables.entries) :
    ¬ Step Primitive (.state objects variables) operation (.state objects' variables') := by
  intro step
  have incompatible := variables.value_unique initialized
    (creation_requires_empty Primitive step creation)
  cases incompatible

theorem creation_rejects_absent
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot}
    {operation : Operation Primitive} {destination : VariableId}
    (creation : operation.creationDestination = some destination)
    (absent : destination ∉ variables.entries.map Prod.fst) :
    ¬ Step Primitive (.state objects variables) operation (.state objects' variables') := by
  intro step
  exact absent (List.mem_map_of_mem (creation_requires_empty Primitive step creation))

theorem createAggregate_rejects_duplicate_fields
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {variables variables' : FiniteMap VariableId Slot}
    {fields : List FieldName} {destination : VariableId}
    (duplicates : ¬ fields.Nodup) :
    ¬ Step Primitive (.state objects variables) (.createAggregate fields destination)
      (.state objects' variables') := by
  intro step
  obtain ⟨_, distinct, _⟩ := createAggregate_effects Primitive step
  exact duplicates distinct

-- Book examples assert complete successor states, including both the new object
-- and the destination owner. Anchor markers select the checked declaration.

-- ANCHOR: integer_primitive
example :
    let x : VariableId := ⟨0⟩
    let α : ObjectId := ⟨0⟩
    let allocated : State Int :=
      .state .empty ⟨[(x, .uninitialized)], by simp⟩
    let created : State Int :=
      .state ⟨[(α, .primitive 22)], by simp⟩
        ⟨[(x, .initialized (.owned α))], by simp⟩
    Step Int (State.initial Int) (.allocVariable x) allocated ∧
    Step Int allocated (.createPrimitive 22 x) created := by
  constructor
  · exact Step.allocVariable _ _ _ (by simp [FiniteMap.empty])
  · exact Step.createPrimitive _ _ _ _ (by simp) _ (by simp [FiniteMap.empty])
-- ANCHOR_END: integer_primitive

-- ANCHOR: empty_aggregate
example :
    let x : VariableId := ⟨0⟩
    let α : ObjectId := ⟨0⟩
    let allocated : State Primitive :=
      .state .empty ⟨[(x, .uninitialized)], by simp⟩
    let created : State Primitive :=
      .state ⟨[(α, .aggregate .empty)], by simp⟩
        ⟨[(x, .initialized (.owned α))], by simp⟩
    Step Primitive (State.initial Primitive) (.allocVariable x) allocated ∧
    Step Primitive allocated (.createAggregate [] x) created := by
  constructor
  · exact Step.allocVariable _ _ _ (by simp [FiniteMap.empty])
  · exact Step.createAggregate _ _ _ (by simp) _ (by simp) _ (by simp [FiniteMap.empty])
-- ANCHOR_END: empty_aggregate

-- ANCHOR: empty_array
example :
    let x : VariableId := ⟨0⟩
    let α : ObjectId := ⟨0⟩
    let allocated : State Primitive :=
      .state .empty ⟨[(x, .uninitialized)], by simp⟩
    let created : State Primitive :=
      .state ⟨[(α, .array #[])], by simp⟩
        ⟨[(x, .initialized (.owned α))], by simp⟩
    Step Primitive (State.initial Primitive) (.allocVariable x) allocated ∧
    Step Primitive allocated (.createArray 0 x) created := by
  constructor
  · exact Step.allocVariable _ _ _ (by simp [FiniteMap.empty])
  · exact Step.createArray _ _ _ _ (by simp) _ (by simp [FiniteMap.empty])
-- ANCHOR_END: empty_array

-- ANCHOR: aggregate_fields
example :
    let x : VariableId := ⟨0⟩
    let α : ObjectId := ⟨0⟩
    let allocated : State Primitive :=
      .state .empty ⟨[(x, .uninitialized)], by simp⟩
    let fields : FiniteMap FieldName Slot :=
      ⟨[("x", .uninitialized), ("y", .uninitialized)], by decide⟩
    let created : State Primitive :=
      .state ⟨[(α, .aggregate fields)], by simp⟩
        ⟨[(x, .initialized (.owned α))], by simp⟩
    Step Primitive (State.initial Primitive) (.allocVariable x) allocated ∧
    Step Primitive allocated (.createAggregate ["x", "y"] x) created := by
  constructor
  · exact Step.allocVariable _ _ _ (by simp [FiniteMap.empty])
  · exact Step.createAggregate _ _ _ (by decide) _ (by simp) _ (by simp [FiniteMap.empty])
-- ANCHOR_END: aggregate_fields

-- ANCHOR: array_slots
example :
    let x : VariableId := ⟨0⟩
    let α : ObjectId := ⟨0⟩
    let allocated : State Primitive :=
      .state .empty ⟨[(x, .uninitialized)], by simp⟩
    let created : State Primitive :=
      .state ⟨[(α, .array #[.uninitialized, .uninitialized])], by simp⟩
        ⟨[(x, .initialized (.owned α))], by simp⟩
    Step Primitive (State.initial Primitive) (.allocVariable x) allocated ∧
    Step Primitive allocated (.createArray 2 x) created := by
  constructor
  · exact Step.allocVariable _ _ _ (by simp [FiniteMap.empty])
  · exact Step.createArray _ _ _ _ (by simp) _ (by simp [FiniteMap.empty])
-- ANCHOR_END: array_slots

-- ANCHOR: nested_variables
example :
    let x : VariableId := ⟨0⟩
    let y : VariableId := ⟨1⟩
    let outer : State Primitive :=
      .state .empty ⟨[(x, .uninitialized)], by simp⟩
    let inner : State Primitive :=
      .state .empty ⟨[(y, .uninitialized), (x, .uninitialized)], by decide⟩
    Step Primitive (State.initial Primitive) (.allocVariable x) outer ∧
    Step Primitive outer (.allocVariable y) inner ∧
    (∀ after, ¬ Step Primitive inner (.deallocVariable x) after) ∧
    Step Primitive inner (.deallocVariable y) outer ∧
    Step Primitive outer (.deallocVariable x) (State.initial Primitive) := by
  constructor
  · exact Step.allocVariable _ _ _ (by simp [FiniteMap.empty])
  constructor
  · exact Step.allocVariable _ _ _ (by decide)
  constructor
  · intro after
    cases after with
    | state objects variables =>
      apply deallocVariable_rejects_non_top
      decide
  constructor
  · exact Step.deallocVariable _ _ _ (by simp) (by rfl)
  · exact Step.deallocVariable _ _ _ (by simp) (by rfl)
-- ANCHOR_END: nested_variables

end Dada.Heap
