import Destructors.Typing

namespace Dada.Assignment
open Shared Shared.Typing

-- A stable typing constraint, not an ABI: given/shared have the same layout
-- for a given nominal type, but this layer conservatively fixes permission too.
abbrev StorageType := FieldType

def storageType (ty : ValueType) : StorageType := ⟨ty.permission, ty.base⟩
def layoutKey (ty : StorageType) : ClassName := ty.className

structure Context where
  bindings : List (VariableId × StorageType)
  current : Environment
  deriving DecidableEq, Repr

def Context.WellFormed (context : Context) (classes : ClassTable) : Prop :=
  context.current.WellFormed classes ∧
  context.bindings.map Prod.fst = context.current.map Prod.fst ∧
  (∀ entry ∈ context.bindings, Admissible classes entry.2.toType) ∧
  (∀ entry ∈ context.current, ∀ ty ∈ entry.2,
    context.bindings.lookup entry.1 = some (storageType ty))

instance (context : Context) (classes : ClassTable) : Decidable (context.WellFormed classes) := by
  unfold Context.WellFormed
  infer_instance

def Context.empty : Context := ⟨[],[]⟩
def Context.withCurrent (context : Context) (current : Environment) : Context :=
  { context with current := current }

def replaceable (classes : ClassTable) : SlotDescription → Bool
  | none => true
  | some ty => decide (StructType classes ty)

-- Expand only the overwritten path. Keep siblings, replace the entire target
-- subtree with the incoming view, and normalize; negatives are not positives.
def replaceView (classes : ClassTable) (source incoming : ValueType) (path : Path) : ValueType :=
  let retained := source.nominal.entries.flatMap fun entry =>
    if path.isPrefixOf entry.path then []
    else match entry with
    | .negative _ => [entry]
    | .positive initialPath =>
      if initialPath.isPrefixOf path then
        match Unique.Typing.classAt classes.nominal source.base initialPath with
        | none => []
        | some target =>
          (Unique.Typing.remainingAfterMove classes.nominal target (path.drop initialPath.length)).map
            (Unique.Typing.Entry.prepend initialPath)
      else [entry]
  normalize classes ⟨source.permission, ⟨source.base,
    retained ++ incoming.nominal.entries.map (Unique.Typing.Entry.prepend path)⟩⟩

-- This is applied after RHS evaluation. An ancestor moved by that evaluation
-- is no longer available as the parent of a field destination.
def storeCurrent (classes : ClassTable) (context : Context) (place : Place) (incoming : ValueType) : Option Environment := do
  if !decide (context.WellFormed classes) || !decide (Admissible classes incoming) then none else do
    let (root,path) := splitPlace place
    let fixed ← context.bindings.lookup root
    let slot ← context.current.lookup root
    let result ← if path.isEmpty then do
      if storageType incoming != fixed || !replaceable classes slot then none
      else some (context.current.replace root (some incoming))
    else do
      let source ← slot
      let parentPath := path.take (path.length - 1)
      let field ← path.getLast?
      let parent ← focus classes source parentPath
      if parent.permission != .given then none else do
        let declaration ← classes.lookup parent.base
        let fieldType ← declaration.fields.lookup field
        let previous ← fieldDescription classes parent field
        if storageType incoming != fieldType || !replaceable classes previous then none
        else some (context.current.replace root (some (replaceView classes source incoming path)))
    some result

def store (classes : ClassTable) (context : Context) (place : Place)
    (incoming : ValueType) : Option Context := do
  let current ← storeCurrent classes context place incoming
  let after := context.withCurrent current
  if decide (after.WellFormed classes) then some after else none

theorem store_preserves_bindings (stored : store classes before place ty = some after) :
    after.bindings = before.bindings := by
  unfold store at stored
  cases h : storeCurrent classes before place ty <;> simp [h] at stored
  rw [← stored.2]
  rfl

theorem store_wellFormed (stored : store classes before place ty = some after) :
    after.WellFormed classes := by
  unfold store at stored
  cases h : storeCurrent classes before place ty <;> simp [h] at stored
  exact stored.2 ▸ stored.1

end Dada.Assignment
