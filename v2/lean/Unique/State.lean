import Unique.Syntax

namespace Dada.Unique

-- A slot is allocated even when it no longer contains an owner.
abbrev Slot := Option ObjectId

structure Object where
  className : ClassName
  fields : List (FieldName × Slot)
  deriving DecidableEq, Repr

structure State where
  objects : List (ObjectId × Object)
  variables : List (VariableId × Slot)
  nextId : Nat
  deriving DecidableEq, Repr

def State.empty : State := ⟨[], [], 0⟩

inductive StoragePlace where
  | variable (name : VariableId)
  | field (object : ObjectId) (name : FieldName)
  deriving DecidableEq, Repr

def Stored (state : State) (place : StoragePlace) (slot : Slot) : Prop :=
  match place with
  | .variable name => (name, slot) ∈ state.variables
  | .field object name =>
      ∃ data, (object, data) ∈ state.objects ∧ (name, slot) ∈ data.fields

-- Updating a place replaces an existing slot; it neither creates a variable
-- nor adds an object's field. Empty slots remain present.
inductive Updated : State → StoragePlace → Slot → State → Prop where
  | variable (objects : List (ObjectId × Object)) (nextId : Nat)
      (leading suffix : List (VariableId × Slot)) (name : VariableId) (old new : Slot) :
      Updated ⟨objects, leading ++ (name, old) :: suffix, nextId⟩ (.variable name) new
        ⟨objects, leading ++ (name, new) :: suffix, nextId⟩
  | field (variables : List (VariableId × Slot)) (nextId : Nat)
      (before after : List (ObjectId × Object)) (parent : ObjectId) (className : ClassName)
      (leading suffix : List (FieldName × Slot)) (name : FieldName) (old new : Slot) :
      Updated ⟨before ++ (parent, ⟨className, leading ++ (name, old) :: suffix⟩) :: after,
          variables, nextId⟩ (.field parent name) new
        ⟨before ++ (parent, ⟨className, leading ++ (name, new) :: suffix⟩) :: after,
          variables, nextId⟩

def References (state : State) : List ObjectId :=
  state.variables.filterMap (fun binding => binding.2) ++
    state.objects.flatMap (fun entry => entry.2.fields.filterMap (fun field => field.2))

def Allocated (state : State) (object : ObjectId) : Prop :=
  object ∈ state.objects.map Prod.fst

-- Liveness follows owners from a variable, then through initialized fields.
inductive Live (state : State) : ObjectId → Prop where
  | variable {name object} : (name, some object) ∈ state.variables → Live state object
  | field {parent object data name} :
      Live state parent → (parent, data) ∈ state.objects →
      (name, some object) ∈ data.fields → Live state object

structure Configuration where
  state : State
  code : List Statement
  deriving Repr

def Configuration.initial (program : Program) : Configuration :=
  ⟨State.empty, program.body⟩

def Configuration.finished (configuration : Configuration) : Prop :=
  configuration.code = []

end Dada.Unique
