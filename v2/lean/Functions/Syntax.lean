import Shared.Typing

namespace Dada.Functions

open Shared Shared.Typing

-- Call-free values and nominal storage are the explicitly inherited Shared
-- sublanguage. Calls have their own syntax, machine, and typing judgments.
inductive Name where
  | function (name : String)
  | method (owner : ClassName) (name : String)
  deriving DecidableEq, Repr

structure Parameter where
  name : VariableId
  type : FieldType
  deriving DecidableEq, Repr

structure Signature where
  parameters : List Parameter
  result : Option FieldType
  deriving DecidableEq, Repr

-- Surface receiver prefixes expand only the receiver parameter, not a call.
def receiver (owner : ClassName) (permission : Perm) : Parameter :=
  ⟨"self", ⟨permission, owner⟩⟩

def Signature.environment (signature : Signature) : Environment :=
  signature.parameters.map fun p => (p.name, some p.type.toType)

def Signature.WellFormed (classes : ClassTable) (name : Name)
    (signature : Signature) : Prop :=
  (signature.parameters.map Parameter.name).Nodup ∧
  (∀ p ∈ signature.parameters, Admissible classes p.type.toType) ∧
  (∀ ty ∈ signature.result, Admissible classes ty.toType) ∧
  match name with
  | .function _ => "self" ∉ signature.parameters.map Parameter.name
  | .method owner _ => match signature.parameters with
    | [] => False
    | first :: rest => first.name = "self" ∧ first.type.className = owner ∧
        "self" ∉ rest.map Parameter.name

instance (classes : ClassTable) (name : Name) (signature : Signature) :
    Decidable (signature.WellFormed classes name) := by
  unfold Signature.WellFormed
  cases name <;> cases signature.parameters <;> dsimp only <;> infer_instance

inductive Statement where
  | local (statement : Unpacking.Statement)
  | call (destination : Option VariableId) (name : Name) (arguments : List Value)
  deriving Repr

structure Body where
  statements : List Statement
  result : Option Value
  deriving Repr

structure Declaration where
  signature : Signature
  body : Body
  deriving Repr

abbrev Declarations := List (Name × Declaration)

structure Program where
  classes : ClassTable
  declarations : Declarations
  main : List Statement
  deriving Repr

end Dada.Functions
