import Destructors.Step

namespace Dada.Destructors

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

def Finished (classes : ClassTable) (environment : Environment) : Prop :=
  ∀ name ty, (name, some ty) ∈ environment → StructType classes ty

-- In a well-typed declaration table, membership supplies the uniquely owned
-- whole receiver signature and excludes destructors on structs.
def Droppable (classes : ClassTable) (declarations : Declarations) (ty : ValueType) : Prop :=
  Admissible classes ty ∧ (StructType classes ty ∨
    (ty = .whole ty.base .given ∧ .destructor ty.base ∈ declarations.map Prod.fst))

instance (classes : ClassTable) (declarations : Declarations) (ty : ValueType) :
    Decidable (Droppable classes declarations ty) := by
  unfold Droppable
  infer_instance

inductive StatementTyped (classes : ClassTable) (declarations : Declarations) : Environment → Statement → Environment → Prop where
  | local {before after statement} :
      Shared.Typing.StatementTyped classes before statement after →
      StatementTyped classes declarations before (.local statement) after
  | call {before middle after destination name arguments declaration} :
      (name, declaration) ∈ declarations →
      (∀ x ∈ destination, x ∉ before.map Prod.fst) →
      ArgsTyped classes before arguments (declaration.signature.parameters.map Functions.Parameter.type) middle →
      DestinationTyped classes middle destination declaration.signature.result after →
      StatementTyped classes declarations before (.call destination name arguments) after

  | dropStruct {before after place ty} :
      ExprTyped classes before (.give place) ty after → StructType classes ty →
      StatementTyped classes declarations before (.dropStruct place) after

-- Elaboration of the single surface form `drop p`. The resolved class name
-- is carried by the core call, so execution needs no dynamic method lookup.
inductive DropTyped (classes : ClassTable) (declarations : Declarations) : Environment → Place → Statement → Environment → Prop where
  | struct {before after place ty} :
      ExprTyped classes before (.give place) ty after → StructType classes ty →
      DropTyped classes declarations before place (.dropStruct place) after
  | class {before after place owner declaration} :
      ExprTyped classes before (.give place) (.whole owner .given) after →
      (Name.destructor owner, declaration) ∈ declarations →
      declaration.signature = ⟨[receiver owner .given], none⟩ →
      DropTyped classes declarations before place (.dropClass owner place) after

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
    ResultTyped classes middle body.result signature.result after ∧ Finished classes after

def DeclarationsTyped (classes : ClassTable) (declarations : Declarations) : Prop :=
  (declarations.map Prod.fst).Nodup ∧
    ∀ entry ∈ declarations,
      Signature.WellFormed classes entry.1 entry.2.signature ∧
      BodyTyped classes declarations entry.2.signature entry.2.body

def ProgramTyped (program : Program) : Prop :=
  program.classes.WellFormed ∧ DeclarationsTyped program.classes program.declarations ∧
    ∃ finalEnvironment,
      SequenceTyped program.classes program.declarations [] program.main finalEnvironment ∧
      Finished program.classes finalEnvironment

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

theorem give_subtype (typed : ExprTyped classes before value ty after) :
    ∀ place, value = .give place → ∃ source,
      Shared.Typing.give classes before place = some (source, after) ∧ Subtype classes source ty := by
  induction typed using ExprTyped.rec (motive_2 := fun _ _ _ _ _ => True) with
  | give _ taken _ _ => intro place eq; cases eq; exact ⟨_, taken, .refl _ _⟩
  | giveShare => intro place eq; cases eq
  | new => intro place eq; cases eq
  | weaken _ _ subtype ih =>
    intro place eq
    obtain ⟨source, taken, previous⟩ := ih place eq
    exact ⟨source, taken, previous.trans subtype⟩
  | nil => trivial
  | cons => trivial

theorem drop_requires_declaration
    (typed : StatementTyped classes declarations before (.dropClass owner place) after) :
    .destructor owner ∈ declarations.map Prod.fst := by
  cases typed with
  | call declared _ _ _ => exact List.mem_map.mpr ⟨_, declared, rfl⟩

end Dada.Destructors
