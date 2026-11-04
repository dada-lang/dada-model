import Functions.Syntax

namespace Dada.Destructors

open Shared Shared.Typing

-- Call-free values and nominal storage are the explicitly inherited Shared
-- sublanguage. Calls have their own syntax, machine, and typing judgments.
inductive Name where
  | function (name : String)
  | method (owner : ClassName) (name : String)
  | destructor (owner : ClassName)
  deriving DecidableEq, Repr

abbrev Parameter := Functions.Parameter
abbrev Signature := Functions.Signature

-- Surface receiver prefixes expand only the receiver parameter, not a call.
def receiver (owner : ClassName) (permission : Perm) : Parameter :=
  ⟨"self", ⟨permission, owner⟩⟩

def Signature.WellFormed (classes : ClassTable) (name : Name)
    (signature : Signature) : Prop :=
  (signature.parameters.map Functions.Parameter.name).Nodup ∧
  (∀ p ∈ signature.parameters, Admissible classes p.type.toType) ∧
  (∀ ty ∈ signature.result, Admissible classes ty.toType) ∧
  match name with
  | .function _ => "self" ∉ signature.parameters.map Functions.Parameter.name
  | .destructor owner => signature = ⟨[receiver owner .given], none⟩ ∧
      ∃ declaration, (owner, declaration) ∈ classes ∧ declaration.kind = .classType
  | .method owner _ => match signature.parameters with
    | [] => False
    | first :: rest => first.name = "self" ∧ first.type.className = owner ∧
        "self" ∉ rest.map Functions.Parameter.name

inductive Statement where
  | local (statement : Unpacking.Statement)
  | call (destination : Option VariableId) (name : Name) (arguments : List Value)
  | dropStruct (place : Place)
  deriving Repr

-- Class drops are calls to a distinct namespace, never a user method named drop.
def Statement.dropClass (owner : ClassName) (place : Place) : Statement :=
  .call none (.destructor owner) [.give place]

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

end Dada.Destructors
