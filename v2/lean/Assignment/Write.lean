import Shared.Step

namespace Dada.Assignment
open Shared

-- Resolve the slot, not its contents. Empty slots have no reference to resolve.
inductive Writable (state : State) : Place → StoragePlace → Slot → Prop where
  | variable {name slot} :
      (name, slot) ∈ state.variables →
      Writable state (.variable name) (.variable name) slot
  | field {base source parent data name slot} :
      Resolve state base source parent .unique →
      (parent, data) ∈ state.objects →
      (name, slot) ∈ data.fields →
      Writable state (.field base name) (.field parent name) slot

def Replaceable (classes : Classes) (state : State) : Slot → Prop
  | none => True
  | some reference => StructReference classes state reference

-- Changing a slot preserves all allocation identities, including its parent.
inductive Write : State → StoragePlace → Reference → State → Prop where
  | variable (objects : List (ObjectId × Object)) (nextId : Nat)
      (leading suffix : List (VariableId × Slot)) (name : VariableId)
      (previous : Slot) (reference : Reference) :
      Write ⟨objects, leading ++ (name, previous) :: suffix, nextId⟩
        (.variable name) reference
        ⟨objects, leading ++ (name, some reference) :: suffix, nextId⟩
  | field (variables : List (VariableId × Slot)) (nextId : Nat)
      (before after : List (ObjectId × Object)) (parent : ObjectId) (className : ClassName)
      (leading suffix : List (FieldName × Slot)) (name : FieldName)
      (previous : Slot) (reference : Reference) :
      Write ⟨before ++ (parent, ⟨className, leading ++ (name, previous) :: suffix⟩) :: after,
          variables, nextId⟩
        (.field parent name) reference
        ⟨before ++ (parent, ⟨className, leading ++ (name, some reference) :: suffix⟩) :: after,
          variables, nextId⟩

theorem Write.nextId (written : Write before place reference after) :
    after.nextId = before.nextId := by cases written <;> rfl

theorem Write.objectKeys (written : Write before place reference after) :
    after.objects.map Prod.fst = before.objects.map Prod.fst := by
  cases written <;> simp

end Dada.Assignment
