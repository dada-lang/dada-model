import Std

namespace Dada.Shared

structure ObjectId where
  index : Nat
  deriving DecidableEq, Repr

instance : OfNat ObjectId n where
  ofNat := ⟨n⟩
abbrev VariableId := String
abbrev FieldName := String
abbrev ClassName := String

inductive Kind where
  | classType
  | structType
  | sharedStruct
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def Kind.isStruct : Kind → Bool
  | .classType => false
  | _ => true

structure Class where
  fields : List FieldName
  kind : Kind := .structType
  deriving DecidableEq, Repr

abbrev Classes := List (ClassName × Class)

-- Places name storage; evaluating a place alone does not produce a value.
inductive Place where
  | variable (name : VariableId)
  | field (base : Place) (name : FieldName)
  deriving DecidableEq, Repr

-- Value expressions produce owners; constructor operands evaluate left to right.
inductive Value where
  | give (source : Place)
  | giveShare (source : Place)
  | new (className : ClassName) (arguments : List Value)
  deriving Repr

structure Statement where
  letValue ::
  destination : VariableId
  value : Value
  deriving Repr

structure Program where
  classes : Classes
  body : List Statement
  deriving Repr

end Dada.Shared
