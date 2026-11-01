/- Textual renderer fixtures only; these declarations do not specify Dada.
   The deliberately trivial transitions exercise source boundaries and syntax.
   See README.md in this directory. -/

namespace RendererFixture

structure ObjectId where
  index : Nat

structure VariableId where
  index : Nat

abbrev FieldName := String

inductive Slot where
  | uninitialized
  | initialized (value : Nat)

inductive Object (Primitive : Type) where
  | primitive (value : Primitive)
  | array (elements : Array Slot)

inductive Place where
  | variable (id : VariableId)
  | element (index : Nat)

structure State (Primitive : Type) where
  elements : Array Slot

def State.initial : State Primitive :=
  ⟨#[]⟩

def readSlot (elements : Array Slot) : Place → Option Slot
  | .variable id => elements[id.index]?
  | .element index => elements[index]?

/-- A write never creates a new element in this fixture. -/
def writeSlot (elements : Array Slot) (index : Nat) (slot : Slot) : Array Slot :=
  elements.set! index slot

def Stored (elements : Array Slot) (index : Nat) (slot : Slot) : Prop :=
  elements[index]? = some slot

def AllocatedObject (objects : List ObjectId) (id : ObjectId) : Prop :=
  id ∈ objects

def initialFields (names : List FieldName) : List (FieldName × Slot) :=
  names.map fun name => (name, .uninitialized)

inductive Operation (Primitive : Type) where
  | allocVariable (id : VariableId)
  | deallocVariable (id : VariableId)
  | createPrimitive (value : Primitive) (id : VariableId)
  | createAggregate (fields : List FieldName) (id : VariableId)
  | createArray (length : Nat) (id : VariableId)

inductive Step (Primitive : Type) : State Primitive → Operation Primitive → State Primitive → Prop where
  | allocVariable (state : State Primitive) (id : VariableId) :
      Step Primitive state (.allocVariable id) state
  | deallocVariable (state : State Primitive) (id : VariableId) :
      Step Primitive state (.deallocVariable id) state
  | createPrimitive (state : State Primitive) (value : Primitive) (id : VariableId) :
      Step Primitive state (.createPrimitive value id) state
  | createAggregate (state : State Primitive) (fields : List FieldName) (id : VariableId) :
      Step Primitive state (.createAggregate fields id) state
  | createArray (state : State Primitive) (length : Nat) (id : VariableId) :
      Step Primitive state (.createArray length id) state

theorem allocVariable_contents (state : State Primitive) (id : VariableId) :
    Step Primitive state (.allocVariable id) state := by
  exact .allocVariable state id

-- These names are stable selection targets, not heap-model claims.
theorem deallocVariable_requires_top
    {id : VariableId}
    (step : Step Primitive before (.deallocVariable id) after) : before = after := by
  cases step
  rfl

theorem deallocVariable_pops (state : State Primitive) (id : VariableId) :
    Step Primitive state (.deallocVariable id) state := by
  exact .deallocVariable state id

theorem copy_preserves_count {xs ys : List Nat} (written : xs = ys) : xs.length = ys.length := by
  exact congrArg (List.length (α := Nat)) written

theorem Transfer.preserves_count {xs ys : List Nat} (written : xs = ys) : xs.length = ys.length := by
  exact copy_preserves_count written

theorem Transfer.read (values : List Nat) : values = values := by
  rfl

-- ANCHOR: integer_primitive
example : let x : VariableId := ⟨0⟩
    let allocated : State Int := State.initial
    let created := allocated
    Step Int allocated (.createPrimitive 22 x) created := by
  exact .createPrimitive _ _ _
-- ANCHOR_END: integer_primitive

-- ANCHOR: nested_variables
example : Step Nat State.initial (.allocVariable ⟨0⟩) State.initial := by
  exact .allocVariable _ _
-- ANCHOR_END: nested_variables

-- ANCHOR: empty_array
example : Step Nat State.initial (.createArray 0 ⟨0⟩) State.initial := by
  exact .createArray _ _ _
-- ANCHOR_END: empty_array

end RendererFixture
