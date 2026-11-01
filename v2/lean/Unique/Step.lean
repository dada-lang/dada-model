import Unique.State

namespace Dada.Unique

-- Resolving a place reads the graph without changing any slot.
inductive Resolve (state : State) : Place → StoragePlace → ObjectId → Prop where
  | variable {name object} :
      (name, some object) ∈ state.variables →
      Resolve state (.variable name) (.variable name) object
  | field {base source parent data name object} :
      Resolve state base source parent →
      (parent, data) ∈ state.objects →
      (name, some object) ∈ data.fields →
      Resolve state (.field base name) (.field parent name) object

-- Removing an owner leaves precisely that allocated slot uninitialized.
-- The list decompositions specify exact effects even on arbitrary raw states.
inductive Take : State → StoragePlace → ObjectId → State → Prop where
  | variable (objects : List (ObjectId × Object)) (nextId : Nat)
      (leading suffix : List (VariableId × Slot)) (name : VariableId) (object : ObjectId) :
      Take ⟨objects, leading ++ (name, some object) :: suffix, nextId⟩
        (.variable name) object
        ⟨objects, leading ++ (name, none) :: suffix, nextId⟩
  | field (variables : List (VariableId × Slot)) (nextId : Nat)
      (before after : List (ObjectId × Object)) (parent : ObjectId) (className : ClassName)
      (leading suffix : List (FieldName × Slot)) (name : FieldName) (object : ObjectId) :
      Take ⟨before ++ (parent, ⟨className, leading ++ (name, some object) :: suffix⟩) :: after,
          variables, nextId⟩
        (.field parent name) object
        ⟨before ++ (parent, ⟨className, leading ++ (name, none) :: suffix⟩) :: after,
          variables, nextId⟩

def State.bind (state : State) (name : VariableId) (object : ObjectId) : State :=
  { state with variables := (name, some object) :: state.variables }

def State.allocate (state : State) (className : ClassName) (fields : List FieldName)
    (arguments : List ObjectId) : State :=
  ⟨(⟨state.nextId⟩, ⟨className, fields.zip (arguments.map some)⟩) :: state.objects,
    state.variables, state.nextId + 1⟩

-- Results are held by the surrounding expression until construction or binding.
-- No invariant is a premise of evaluation; preservation is proved separately.
mutual
inductive Eval (classes : Classes) : State → Value → State → ObjectId → Prop where
  | give {state cleared : State} {path : Place} {source : StoragePlace} {object : ObjectId} :
      Resolve state path source object →
      Take state source object cleared →
      Eval classes state (.give path) cleared object
  | new {state evaluated : State} {className : ClassName} {declaration : Class}
      {arguments : List Value} {objects : List ObjectId} :
      (className, declaration) ∈ classes →
      EvalArgs classes state arguments evaluated objects →
      objects.length = declaration.fields.length →
      ObjectId.mk evaluated.nextId ∉ evaluated.objects.map Prod.fst →
      Eval classes state (.new className arguments)
        (evaluated.allocate className declaration.fields objects) ⟨evaluated.nextId⟩

inductive EvalArgs (classes : Classes) : State → List Value → State → List ObjectId → Prop where
  | nil (state : State) : EvalArgs classes state [] state []
  | cons {before middle after : State} {argument : Value} {arguments : List Value}
      {object : ObjectId} {objects : List ObjectId} :
      Eval classes before argument middle object →
      EvalArgs classes middle arguments after objects →
      EvalArgs classes before (argument :: arguments) after (object :: objects)
end

inductive Step (classes : Classes) : Configuration → Configuration → Prop where
  | letValue {state evaluated : State} {destination : VariableId} {value : Value}
      {object : ObjectId} {rest : List Statement} :
      destination ∉ evaluated.variables.map Prod.fst →
      Eval classes state value evaluated object →
      Step classes ⟨state, ⟨destination, value⟩ :: rest⟩
        ⟨evaluated.bind destination object, rest⟩

inductive Steps (classes : Classes) : Configuration → Configuration → Prop where
  | refl (configuration : Configuration) : Steps classes configuration configuration
  | step {before middle after} :
      Step classes before middle → Steps classes middle after → Steps classes before after

def Stuck (classes : Classes) (configuration : Configuration) : Prop :=
  ¬ configuration.finished ∧ ¬ ∃ after, Step classes configuration after

end Dada.Unique
