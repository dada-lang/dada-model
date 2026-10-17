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

-- The first operation slice allocates and deallocates variable slots. Other
-- operations will extend this type; deallocation does not implicitly drop a value.
inductive Operation where
  | allocVariable (id : VariableId)
  | deallocVariable (id : VariableId)

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

-- Successful steps are relations; missing rules do not define faults. The heap
-- checks only current absence at allocation. The execution layer must supply a
-- new identity for each allocation lifetime: these rules alone permit reuse after
-- deallocation and do not establish lease invalidation or global freshness.
inductive Step : State Primitive → Operation → State Primitive → Prop where
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
      (empty : (id, Slot.uninitialized) ∈ variables.entries) :
      Step (.state objects variables) (.deallocVariable id)
        (.state objects (variables.erase id))

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
  | deallocVariable _ _ _ empty => exact empty

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

end Dada.Heap
