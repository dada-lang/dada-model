import Functions.Step

namespace Dada.Functions

open Shared Shared.Typing

inductive ResultTyped (classes : ClassTable) : Environment → Option Value → Option FieldType → Environment → Prop where
  | none {environment} :
      environment.WellFormed classes → ResultTyped classes environment none none environment
  | some {before after value type} :
      ExprTyped classes before value type.toType after →
      ResultTyped classes before (some value) (some type) after

inductive DestinationTyped (classes : ClassTable) : Environment → Option VariableId → Option FieldType → Environment → Prop where
  | none {environment} :
      environment.WellFormed classes → DestinationTyped classes environment none none environment
  | some {before after name type} :
      BindingTyped classes before (.variable name) type.toType after →
      DestinationTyped classes before (some name) (some type) after

inductive StatementTyped (classes : ClassTable) (declarations : Declarations) : Environment → Statement → Environment → Prop where
  | local {before after statement} :
      Shared.Typing.StatementTyped classes before statement after →
      StatementTyped classes declarations before (.local statement) after
  | call {before middle after destination name arguments declaration} :
      (name, declaration) ∈ declarations →
      (∀ x ∈ destination, x ∉ before.map Prod.fst) →
      ArgsTyped classes before arguments (declaration.signature.parameters.map Parameter.type) middle →
      DestinationTyped classes middle destination declaration.signature.result after →
      StatementTyped classes declarations before (.call destination name arguments) after

inductive SequenceTyped (classes : ClassTable) (declarations : Declarations) : Environment → List Statement → Environment → Prop where
  | nil {environment} :
      environment.WellFormed classes → SequenceTyped classes declarations environment [] environment
  | cons {before middle after statement rest} :
      StatementTyped classes declarations before statement middle →
      SequenceTyped classes declarations middle rest after →
      SequenceTyped classes declarations before (statement :: rest) after

def BodyTyped (classes : ClassTable) (declarations : Declarations) (signature : Signature)
    (body : Body) : Prop :=
  ∃ middle after,
    SequenceTyped classes declarations signature.environment body.statements middle ∧
    ResultTyped classes middle body.result signature.result after

def DeclarationsTyped (classes : ClassTable) (declarations : Declarations) : Prop :=
  (declarations.map Prod.fst).Nodup ∧
    ∀ entry ∈ declarations,
      entry.2.signature.WellFormed classes entry.1 ∧
      BodyTyped classes declarations entry.2.signature entry.2.body

def ProgramTyped (program : Program) : Prop :=
  program.classes.WellFormed ∧ DeclarationsTyped program.classes program.declarations ∧
    ∃ finalEnvironment,
      SequenceTyped program.classes program.declarations [] program.main finalEnvironment

theorem DestinationTyped.shape
    (typed : DestinationTyped classes before destination result after) :
    DestinationMatches destination result := by
  cases typed <;> rfl

theorem call_arity
    (typed : StatementTyped classes declarations before (.call destination name arguments) after) :
    ∃ declaration, (name, declaration) ∈ declarations ∧
      arguments.length = declaration.signature.parameters.length ∧
      DestinationMatches destination declaration.signature.result := by
  cases typed with
  | call declared _ args dest =>
    exact ⟨_, declared, by simpa using args.length, dest.shape⟩

end Dada.Functions
