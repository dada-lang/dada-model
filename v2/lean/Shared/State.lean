import Shared.Syntax

namespace Dada.Shared

inductive Mode where
  | unique
  | shared
  deriving DecidableEq, Repr

-- Shared access is retained through every remaining projection.
def Mode.join : Mode → Mode → Mode
  | .unique, .unique => .unique
  | _, _ => .shared

def Kind.mode : Kind → Mode
  | .sharedStruct => .shared
  | _ => .unique

structure Reference where
  reference ::
  mode : Mode
  object : ObjectId
  deriving DecidableEq, Repr

def Reference.owned (object : ObjectId) : Reference := ⟨.unique, object⟩

def Reference.shared (object : ObjectId) : Reference := ⟨.shared, object⟩

-- An empty slot is still allocated, but contributes no owner.
abbrev Slot := Option Reference

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

def References (state : State) : List ObjectId :=
  state.variables.filterMap (fun binding => binding.2.map Reference.object) ++
    state.objects.flatMap (fun entry => entry.2.fields.filterMap
      (fun field => field.2.map Reference.object))

def Allocated (state : State) (object : ObjectId) : Prop :=
  object ∈ state.objects.map Prod.fst

-- Liveness follows owners from a variable, then through initialized fields.
inductive Live (state : State) : ObjectId → Prop where
  | variable {name reference} :
      (name, some reference) ∈ state.variables → Live state reference.object
  | field {parent reference data name} :
      Live state parent → (parent, data) ∈ state.objects →
      (name, some reference) ∈ data.fields → Live state reference.object

structure Configuration where
  state : State
  code : List Statement
  deriving Repr

def Configuration.initial (program : Program) : Configuration :=
  ⟨State.empty, program.body⟩

def Configuration.finished (configuration : Configuration) : Prop :=
  configuration.code = []

end Dada.Shared
