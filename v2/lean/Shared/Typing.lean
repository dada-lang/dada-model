import Shared.TypingViews
import Shared.Unpacking

namespace Dada.Shared.Typing

-- Empty slots remain allocated; absence is a separate outer Option at lookup.
abbrev SlotDescription := Option ValueType
abbrev Environment := List (VariableId × SlotDescription)

def Environment.WellFormed (environment : Environment) (classes : ClassTable) : Prop :=
  (environment.map Prod.fst).Nodup ∧
    environment.all (fun entry => match entry.2 with
      | none => true
      | some ty => decide (Admissible classes ty)) = true

instance (environment : Environment) (classes : ClassTable) :
    Decidable (environment.WellFormed classes) := by
  unfold Environment.WellFormed
  infer_instance

def Environment.lookup (environment : Environment) (name : VariableId) :
    Option SlotDescription :=
  (environment.find? fun entry => entry.1 == name).map Prod.snd

def Environment.replace (environment : Environment) (name : VariableId)
    (description : SlotDescription) : Environment :=
  environment.map fun entry => if entry.1 = name then (name, description) else entry

def splitPlace : Place → VariableId × Path
  | .variable name => (name, [])
  | .field base name =>
      let (root, path) := splitPlace base
      (root, path ++ [name])

def placeFrom (root : VariableId) (path : Path) : Place :=
  path.foldl Place.field (.variable root)

theorem placeFrom_splitPlace (place : Place) :
    placeFrom (splitPlace place).1 (splitPlace place).2 = place := by
  induction place with
  | «variable» name => rfl
  | field base name ih =>
    simpa [splitPlace, placeFrom, List.foldl_append] using
      congrArg (fun p => Place.field p name) ih

-- Giving is a static operation: it never consults the heap or evaluation.
def give (classes : ClassTable) (environment : Environment) (place : Place) :
    Option (ValueType × Environment) := do
  let (root, path) := splitPlace place
  let source ← environment.lookup root
  let source ← source
  let result ← focus classes source path
  if result.permission = .shared then
    return (result, environment)
  else if path = [] then
    return (result, environment.replace root none)
  else
    let remaining ← emptyPath classes source path
    return (result, environment.replace root (some remaining))

def fieldDescription (classes : ClassTable) (ty : ValueType) (name : FieldName) :
    Option SlotDescription :=
  if Unique.Typing.negative ty.nominal [name] then some none
  else (focus classes ty [name]).map some

-- The well-formedness premises make the chapter's global convention explicit.
-- They inspect only finite static descriptions, not operational success.
mutual
inductive ExprTyped (classes : ClassTable) : Environment → Value → ValueType → Environment → Prop where
  | give {before after : Environment} {place : Place} {ty : ValueType} :
      before.WellFormed classes →
      Typing.give classes before place = some (ty, after) →
      Admissible classes ty → after.WellFormed classes →
      ExprTyped classes before (.give place) ty after
  | giveShare {before after : Environment} {place : Place} {ty : ValueType} :
      before.WellFormed classes →
      Typing.give classes before place = some (ty, after) →
      Admissible classes ty → after.WellFormed classes →
      ExprTyped classes before (.giveShare place) ty.shared after
  | new {before after : Environment} {name : ClassName} {declaration : TypedClass}
      {arguments : List Value} :
      (name, declaration) ∈ classes →
      ArgsTyped classes before arguments (declaration.fields.map Prod.snd) after →
      Admissible classes (ValueType.whole name) →
      ExprTyped classes before (.new name arguments) (ValueType.whole name) after
  | weaken {before after : Environment} {value : Value} {ty other : ValueType} :
      ExprTyped classes before value ty after →
      Admissible classes other → Subtype classes ty other →
      ExprTyped classes before value other after

inductive ArgsTyped (classes : ClassTable) : Environment → List Value → List FieldType → Environment → Prop where
  | nil {environment : Environment} :
      environment.WellFormed classes → ArgsTyped classes environment [] [] environment
  | cons {before middle after : Environment} {value : Value} {values : List Value}
      {field : FieldType} {fields : List FieldType} :
      ExprTyped classes before value field.toType middle →
      ArgsTyped classes middle values fields after →
      ArgsTyped classes before (value :: values) (field :: fields) after
end

-- Pattern order determines binding order; all field names must still be present.
inductive FieldBindings (classes : ClassTable) (ty : ValueType) : List (FieldName × VariableId) → Environment → Prop where
  | nil : FieldBindings classes ty [] []
  | cons {field : FieldName} {destination : VariableId} {description : SlotDescription}
      {fields : List (FieldName × VariableId)} {bindings : Environment} :
      fieldDescription classes ty field = some description →
      FieldBindings classes ty fields bindings →
      FieldBindings classes ty ((field, destination) :: fields)
        ((destination, description) :: bindings)

inductive BindingTyped (classes : ClassTable) : Environment → Unpacking.Pattern → ValueType → Environment → Prop where
  | variable {environment : Environment} {name : VariableId} {ty : ValueType} :
      environment.WellFormed classes → Admissible classes ty →
      name ∉ environment.map Prod.fst →
      BindingTyped classes environment (.variable name) ty ((name, some ty) :: environment)
  | unpack {before : Environment} {ty : ValueType} {name : ClassName}
      {declaration : TypedClass} {fields : List (FieldName × VariableId)}
      {bindings : Environment} :
      before.WellFormed classes → Admissible classes ty →
      ty.permission = .given → ty.nominal.className = name → (name, declaration) ∈ classes →
      (fields.map Prod.fst).Perm (declaration.fields.map Prod.fst) →
      (fields.map Prod.snd).Nodup →
      (∀ destination ∈ fields.map Prod.snd, destination ∉ before.map Prod.fst) →
      FieldBindings classes ty fields bindings →
      (bindings ++ before).WellFormed classes →
      BindingTyped classes before (.unpack name fields) ty (bindings ++ before)

inductive StatementTyped (classes : ClassTable) : Environment → Unpacking.Statement → Environment → Prop where
  | letValue {before middle after : Environment} {pattern : Unpacking.Pattern}
      {value : Value} {ty : ValueType} :
      ExprTyped classes before value ty middle →
      BindingTyped classes middle pattern ty after →
      StatementTyped classes before ⟨pattern, value⟩ after

inductive SequenceTyped (classes : ClassTable) : Environment → List Unpacking.Statement → Environment → Prop where
  | nil {environment : Environment} :
      environment.WellFormed classes → SequenceTyped classes environment [] environment
  | cons {before middle after : Environment} {statement : Unpacking.Statement}
      {rest : List Unpacking.Statement} :
      StatementTyped classes before statement middle →
      SequenceTyped classes middle rest after →
      SequenceTyped classes before (statement :: rest) after

def ProgramTyped (classes : ClassTable) (code : List Unpacking.Statement) : Prop :=
  classes.WellFormed ∧ ∃ finalEnvironment, SequenceTyped classes [] code finalEnvironment

theorem ArgsTyped.length (typed : ArgsTyped classes before values fields after) :
    values.length = fields.length := by
  induction typed using ArgsTyped.rec (motive_1 := fun _ _ _ _ _ => True) with
  | give => trivial
  | giveShare => trivial
  | new => trivial
  | weaken => trivial
  | nil => rfl
  | cons _ _ _ rest => simpa using rest

theorem FieldBindings.keys (typed : FieldBindings classes ty fields bindings) :
    bindings.map Prod.fst = fields.map Prod.snd := by
  induction typed with
  | nil => rfl
  | cons _ _ ih => simp [ih]

-- Weakening cannot disguise an unsuccessful give as a typed give.
theorem ExprTyped.give_requires_operation
    (typed : ExprTyped classes before value ty after) :
    ∀ place, value = .give place → ∃ result, Typing.give classes before place = some (result, after) := by
  induction typed using ExprTyped.rec (motive_2 := fun _ _ _ _ _ => True) with
  | give _ taken _ _ =>
    intro place equality
    cases equality
    exact ⟨_, taken⟩
  | giveShare => intro place equality; cases equality
  | new => intro place equality; cases equality
  | weaken _ _ _ ih => exact ih
  | nil => trivial
  | cons => trivial

theorem failed_give_not_typed (failed : Typing.give classes environment place = none) :
    ¬ ExprTyped classes environment (.give place) ty after := by
  intro typed
  obtain ⟨result, succeeded⟩ := typed.give_requires_operation place rfl
  rw [failed] at succeeded
  contradiction

theorem ExprTyped.give_permission
    (typed : ExprTyped classes before value ty after) :
    ∀ place, value = .give place → ∃ result,
      Typing.give classes before place = some (result, after) ∧
      result.permission = ty.permission := by
  induction typed using ExprTyped.rec (motive_2 := fun _ _ _ _ _ => True) with
  | give _ taken _ _ =>
    intro place equality
    cases equality
    exact ⟨_, taken, rfl⟩
  | giveShare => intro place equality; cases equality
  | new => intro place equality; cases equality
  | weaken _ _ subtype ih =>
    intro place equality
    obtain ⟨result, taken, permission⟩ := ih place equality
    exact ⟨result, taken, permission.trans subtype.1⟩
  | nil => trivial
  | cons => trivial

theorem ExprTyped.new_requires_arguments
    (typed : ExprTyped classes before value ty after) :
    ∀ name arguments, value = .new name arguments →
      ∃ declaration, (name, declaration) ∈ classes ∧
        ArgsTyped classes before arguments (declaration.fields.map Prod.snd) after := by
  induction typed using ExprTyped.rec (motive_2 := fun _ _ _ _ _ => True) with
  | give => intro name arguments equality; cases equality
  | giveShare => intro name arguments equality; cases equality
  | new declared arguments _ _ =>
    intro name values equality
    cases equality
    exact ⟨_, declared, arguments⟩
  | weaken _ _ _ ih => exact ih
  | nil => trivial
  | cons => trivial

end Dada.Shared.Typing
