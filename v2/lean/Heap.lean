import Std

namespace Dada.Heap

-- Primitive is a parameter of the whole model, implicit in uses of its types.
variable (Primitive : Type)

structure ObjectId where
  index : Nat
  deriving DecidableEq

structure FrameId where
  index : Nat
  deriving DecidableEq

abbrev FieldName := String

abbrev BindingName := String

-- A finite map with no duplicate keys; absence differs from uninitialized.
structure FiniteMap (Key Value : Type) where
  entries : List (Key × Value)
  uniqueKeys : (entries.map Prod.fst).Nodup

inductive Place where
  | binding (frame : FrameId) (name : BindingName)
  | field (object : ObjectId) (name : FieldName)
  | element (array : ObjectId) (index : Nat)

inductive Reference where
  | owned (object : ObjectId)
  | leased (place : Place)
  | showned (object : ObjectId)
  | shlease (object : ObjectId)

inductive Slot where
  | uninitialized
  | initialized (reference : Reference)

inductive Object where
  | primitive (value : Primitive)
  | aggregate (fields : FiniteMap FieldName Slot)
  | array (elements : Array Slot)

inductive Frame where
  | frame (bindings : FiniteMap BindingName Slot)

inductive State where
  | state
      (objects : FiniteMap ObjectId (Object Primitive))
      (frames : FiniteMap FrameId Frame)

inductive Projection where
  | field (name : FieldName)
  | index (index : Nat)

inductive AccessPath where
  | path (binding : BindingName) (projections : List Projection)

end Dada.Heap
