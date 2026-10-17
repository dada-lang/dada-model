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

-- First operation slice: frame creation. Other operations will extend this type.
inductive Operation where
  | createFrame (bindings : List BindingName)

-- Initialize a finite set of named bindings; duplicate names are not permitted.
def initialBindings (names : List BindingName) (distinct : names.Nodup) :
    FiniteMap BindingName Slot where
  entries := names.map fun name => (name, Slot.uninitialized)
  uniqueKeys := by simpa [List.map_map, Function.comp_def] using distinct

-- Allocation extends the finite map without replacing an existing entry.
def FiniteMap.insertFresh (map : FiniteMap Key Value) (key : Key) (value : Value)
    (fresh : key ∉ map.entries.map Prod.fst) : FiniteMap Key Value where
  entries := (key, value) :: map.entries
  uniqueKeys := List.nodup_cons.mpr ⟨fresh, map.uniqueKeys⟩

-- Successful steps are relations. The chosen fresh ID is part of the derivation,
-- not a returned reference outside the state. Missing rules do not define faults.
inductive Step : State Primitive → Operation → State Primitive → Prop where
  | createFrame
      (objects : FiniteMap ObjectId (Object Primitive))
      (frames : FiniteMap FrameId Frame)
      (names : List BindingName)
      (distinct : names.Nodup)
      (id : FrameId)
      (fresh : id ∉ frames.entries.map Prod.fst)
      (bindings : FiniteMap BindingName Slot)
      (bindings_eq : bindings = initialBindings names distinct)
      (frame : Frame)
      (frame_eq : frame = Frame.frame bindings)
      (frames' : FiniteMap FrameId Frame)
      (frames_eq : frames' = frames.insertFresh id frame fresh) :
      Step (.state objects frames) (.createFrame names) (.state objects frames')

-- This theorem concerns only the createFrame operation, including as Step grows.
theorem createFrame_preserves_objects
    {objects objects' : FiniteMap ObjectId (Object Primitive)}
    {frames frames' : FiniteMap FrameId Frame} {names : List BindingName}
    (step : Step Primitive (.state objects frames) (.createFrame names)
      (.state objects' frames')) : objects' = objects := by
  cases step
  rfl

theorem initialBindings_are_uninitialized
    (names : List BindingName) (distinct : names.Nodup)
    {name : BindingName} {slot : Slot}
    (member : (name, slot) ∈ (initialBindings names distinct).entries) :
    slot = .uninitialized := by
  simp only [initialBindings, List.mem_map, Prod.mk.injEq] at member
  obtain ⟨_, _, _, rfl⟩ := member
  rfl

end Dada.Heap
