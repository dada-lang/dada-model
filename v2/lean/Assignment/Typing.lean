import Assignment.Step
import Assignment.StorageTypes

namespace Dada.Assignment

open Shared Shared.Typing

-- Parameters and new bindings carry fixed types even when currently empty.
def initialContext (signature : Signature) : Context :=
  ⟨signature.parameters.map (fun p => (p.name, p.type)), signature.environment⟩

def bindingTypes (classes : ClassTable) (pattern : Unpacking.Pattern)
    (ty : ValueType) : Option (List (VariableId × StorageType)) := do
  match pattern with
  | .variable name => some [(name, storageType ty)]
  | .unpack name fields =>
    let declaration ← classes.lookup name
    fields.mapM fun (field, destination) => do
      let fixed ← declaration.fields.lookup field
      some (destination, fixed)

inductive ExprTyped (classes : ClassTable) : Context → Value → ValueType → Context → Prop where
  | lift {before after value ty} :
      before.WellFormed classes →
      Shared.Typing.ExprTyped classes before.current value ty after →
      (before.withCurrent after).WellFormed classes →
      ExprTyped classes before value ty (before.withCurrent after)

inductive ArgsTyped (classes : ClassTable) : Context → List Value → List FieldType → Context → Prop where
  | lift {before after values types} :
      before.WellFormed classes →
      Shared.Typing.ArgsTyped classes before.current values types after →
      (before.withCurrent after).WellFormed classes →
      ArgsTyped classes before values types (before.withCurrent after)

inductive BindingTyped (classes : ClassTable) : Context → Unpacking.Pattern → ValueType → Context → Prop where
  | lift {before after pattern ty fixed} :
      before.WellFormed classes →
      Shared.Typing.BindingTyped classes before.current pattern ty after →
      bindingTypes classes pattern ty = some fixed →
      (Context.mk (fixed ++ before.bindings) after).WellFormed classes →
      BindingTyped classes before pattern ty ⟨fixed ++ before.bindings, after⟩

inductive LocalTyped (classes : ClassTable) : Context → Unpacking.Statement → Context → Prop where
  | letValue {before middle after pattern value ty} :
      ExprTyped classes before value ty middle →
      BindingTyped classes middle pattern ty after →
      LocalTyped classes before ⟨pattern, value⟩ after

inductive ResultTyped (classes : ClassTable) : Context → Option Value → Option FieldType → Context → Prop where
  | none {environment} :
      environment.WellFormed classes → ResultTyped classes environment none none environment
  | some {before after value type} :
      ExprTyped classes before value type.toType after →
      ResultTyped classes before (some value) (some type) after

inductive DestinationTyped (classes : ClassTable) : Context → Option VariableId → Option FieldType → Context → Prop where
  | none {environment} :
      environment.WellFormed classes → DestinationTyped classes environment none none environment
  | some {before after name type} :
      BindingTyped classes before (.variable name) type.toType after →
      DestinationTyped classes before (some name) (some type) after

def Finished (classes : ClassTable) (context : Context) : Prop :=
  Destructors.Finished classes context.current

inductive StatementTyped (classes : ClassTable) (declarations : Declarations) : Context → Statement → Context → Prop where
  | local {before after statement} :
      LocalTyped classes before statement after →
      StatementTyped classes declarations before (.local statement) after
  | call {before middle after destination name arguments declaration} :
      (name, declaration) ∈ declarations →
      (∀ x ∈ destination, x ∉ before.current.map Prod.fst) →
      ArgsTyped classes before arguments (declaration.signature.parameters.map Functions.Parameter.type) middle →
      DestinationTyped classes middle destination declaration.signature.result after →
      StatementTyped classes declarations before (.call destination name arguments) after

  | store {before middle after place value ty} :
      ExprTyped classes before value ty middle →
      store classes middle place ty = some after →
      StatementTyped classes declarations before (.store place value) after
  | dropStruct {before after place ty} :
      ExprTyped classes before (.give place) ty after → StructType classes ty →
      StatementTyped classes declarations before (.dropStruct place) after

-- Elaboration of the single surface form `drop p`. The resolved class name
-- is carried by the core call, so execution needs no dynamic method lookup.
inductive DropTyped (classes : ClassTable) (declarations : Declarations) : Context → Place → Statement → Context → Prop where
  | struct {before after place ty} :
      ExprTyped classes before (.give place) ty after → StructType classes ty →
      DropTyped classes declarations before place (.dropStruct place) after
  | class {before after place owner declaration} :
      ExprTyped classes before (.give place) (.whole owner .given) after →
      (Destructors.Name.destructor owner, declaration) ∈ declarations →
      declaration.signature = ⟨[receiver owner .given], none⟩ →
      DropTyped classes declarations before place (.dropClass owner place) after

inductive SequenceTyped (classes : ClassTable) (declarations : Declarations) : Context → List Statement → Context → Prop where
  | nil {environment} :
      environment.WellFormed classes → SequenceTyped classes declarations environment [] environment
  | cons {before middle after statement rest} :
      StatementTyped classes declarations before statement middle →
      SequenceTyped classes declarations middle rest after →
      SequenceTyped classes declarations before (statement :: rest) after

def BodyTyped (classes : ClassTable) (declarations : Declarations) (signature : Signature)
    (body : Body) : Prop :=
  ∃ middle after,
    SequenceTyped classes declarations (initialContext signature) body.statements middle ∧
    ResultTyped classes middle body.result signature.result after ∧ Finished classes after

def DeclarationsTyped (classes : ClassTable) (declarations : Declarations) : Prop :=
  (declarations.map Prod.fst).Nodup ∧
    ∀ entry ∈ declarations,
      Destructors.Signature.WellFormed classes entry.1 entry.2.signature ∧
      BodyTyped classes declarations entry.2.signature entry.2.body

def ProgramTyped (program : Program) : Prop :=
  program.classes.WellFormed ∧ DeclarationsTyped program.classes program.declarations ∧
    ∃ finalEnvironment,
      SequenceTyped program.classes program.declarations Context.empty program.main finalEnvironment ∧
      Finished program.classes finalEnvironment

end Dada.Assignment
