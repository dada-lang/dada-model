import Std

namespace Dada.Unique

structure ObjectId where
  index : Nat
  deriving DecidableEq, Repr

instance (n : Nat) : OfNat ObjectId n := ⟨⟨n⟩⟩
abbrev VariableId := String
abbrev FieldName := String
abbrev ClassName := String

structure Class where
  fields : List FieldName
  deriving DecidableEq, Repr

abbrev Classes := List (ClassName × Class)

-- Places name storage; evaluating a place alone does not produce a value.
inductive Place where
  | variable (name : VariableId)
  | field (base : Place) (name : FieldName)
  deriving DecidableEq, Repr

-- Constructor operands are expressions, evaluated from left to right.
-- The distinct syntax keeps places separate from values.
inductive Value where
  | give (source : Place)
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

end Dada.Unique
