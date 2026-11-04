import Destructors.Syntax

namespace Dada.Assignment

open Shared Shared.Typing

-- Call-free values and nominal storage are the explicitly inherited Shared
-- sublanguage. Calls have their own syntax, machine, and typing judgments.
abbrev Name := Destructors.Name
abbrev Parameter := Destructors.Parameter
abbrev Signature := Destructors.Signature
abbrev receiver := Destructors.receiver

inductive Statement where
  | local (statement : Unpacking.Statement)
  | call (destination : Option VariableId) (name : Name) (arguments : List Value)
  | store (place : Place) (value : Value)
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

end Dada.Assignment
