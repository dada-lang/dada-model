import Shared.State

namespace Dada.Shared

-- Resolve records the effective permission of the whole path. A shared link
-- makes all subsequent access shared, even when a later stored link is unique.
inductive Resolve (state : State) : Place → StoragePlace → ObjectId → Mode → Prop where
  | variable {name reference} :
      (name, some reference) ∈ state.variables →
      Resolve state (.variable name) (.variable name) reference.object reference.mode
  | field {base source parent permission data name reference} :
      Resolve state base source parent permission →
      (parent, data) ∈ state.objects →
      (name, some reference) ∈ data.fields →
      Resolve state (.field base name) (.field parent name) reference.object
        (permission.join reference.mode)

-- Only a unique reference can be taken; copying leaves the source initialized.
inductive Take : State → StoragePlace → ObjectId → State → Prop where
  | variable (objects : List (ObjectId × Object)) (nextId : Nat)
      (leading suffix : List (VariableId × Slot)) (name : VariableId) (object : ObjectId) :
      Take ⟨objects, leading ++ (name, some (.owned object)) :: suffix, nextId⟩
        (.variable name) object
        ⟨objects, leading ++ (name, none) :: suffix, nextId⟩
  | field (variables : List (VariableId × Slot)) (nextId : Nat)
      (before after : List (ObjectId × Object)) (parent : ObjectId) (className : ClassName)
      (leading suffix : List (FieldName × Slot)) (name : FieldName) (object : ObjectId) :
      Take ⟨before ++ (parent, ⟨className, leading ++ (name, some (.owned object)) :: suffix⟩) :: after,
          variables, nextId⟩
        (.field parent name) object
        ⟨before ++ (parent, ⟨className, leading ++ (name, none) :: suffix⟩) :: after,
          variables, nextId⟩

-- A copy of a unique final field through shared access first promotes precisely
-- that stored owner to shared. This changes permissions, not object identity,
-- field names, or the represented field value.
inductive Promote : State → StoragePlace → ObjectId → State → Prop where
  | variable (objects : List (ObjectId × Object)) (nextId : Nat)
      (leading suffix : List (VariableId × Slot)) (name : VariableId) (object : ObjectId) :
      Promote ⟨objects, leading ++ (name, some (.owned object)) :: suffix, nextId⟩
        (.variable name) object
        ⟨objects, leading ++ (name, some (.shared object)) :: suffix, nextId⟩
  | field (variables : List (VariableId × Slot)) (nextId : Nat)
      (before after : List (ObjectId × Object)) (parent : ObjectId) (className : ClassName)
      (leading suffix : List (FieldName × Slot)) (name : FieldName) (object : ObjectId) :
      Promote ⟨before ++ (parent, ⟨className, leading ++ (name, some (.owned object)) :: suffix⟩) :: after,
          variables, nextId⟩
        (.field parent name) object
        ⟨before ++ (parent, ⟨className, leading ++ (name, some (.shared object)) :: suffix⟩) :: after,
          variables, nextId⟩

inductive Give : State → Place → Reference → State → Prop where
  | move {state cleared : State} {path : Place} {source : StoragePlace} {object : ObjectId} :
      Resolve state path source object .unique →
      Take state source object cleared →
      Give state path (.owned object) cleared
  | copy {state : State} {path : Place} {source : StoragePlace} {object : ObjectId} :
      Resolve state path source object .shared →
      Stored state source (some (.shared object)) →
      Give state path (.shared object) state
  | promote {state promoted : State} {path : Place} {source : StoragePlace} {object : ObjectId} :
      Resolve state path source object .shared →
      Promote state source object promoted →
      Give state path (.shared object) promoted

def State.bind (state : State) (name : VariableId) (reference : Reference) : State :=
  { state with variables := (name, some reference) :: state.variables }

def State.allocate (state : State) (className : ClassName) (fields : List FieldName)
    (references : List Reference) : State :=
  ⟨(⟨state.nextId⟩, ⟨className, fields.zip (references.map some)⟩) :: state.objects,
    state.variables, state.nextId + 1⟩

mutual
inductive Eval (classes : Classes) : State → Value → State → Reference → Prop where
  | give {state evaluated : State} {path : Place} {reference : Reference} :
      Give state path reference evaluated →
      Eval classes state (.give path) evaluated reference
  | giveShare {state evaluated : State} {path : Place} {reference : Reference} :
      Give state path reference evaluated →
      Eval classes state (.giveShare path) evaluated (.shared reference.object)
  | new {state evaluated : State} {className : ClassName} {declaration : Class}
      {arguments : List Value} {references : List Reference} :
      (className, declaration) ∈ classes →
      EvalArgs classes state arguments evaluated references →
      references.length = declaration.fields.length →
      ObjectId.mk evaluated.nextId ∉ evaluated.objects.map Prod.fst →
      Eval classes state (.new className arguments)
        (evaluated.allocate className declaration.fields references) (.owned ⟨evaluated.nextId⟩)

inductive EvalArgs (classes : Classes) : State → List Value → State → List Reference → Prop where
  | nil (state : State) : EvalArgs classes state [] state []
  | cons {before middle after : State} {argument : Value} {arguments : List Value}
      {reference : Reference} {references : List Reference} :
      Eval classes before argument middle reference →
      EvalArgs classes middle arguments after references →
      EvalArgs classes before (argument :: arguments) after (reference :: references)
end

inductive Step (classes : Classes) : Configuration → Configuration → Prop where
  | letValue {state evaluated : State} {destination : VariableId} {value : Value}
      {reference : Reference} {rest : List Statement} :
      destination ∉ evaluated.variables.map Prod.fst →
      Eval classes state value evaluated reference →
      Step classes ⟨state, ⟨destination, value⟩ :: rest⟩
        ⟨evaluated.bind destination reference, rest⟩

inductive Steps (classes : Classes) : Configuration → Configuration → Prop where
  | refl (configuration : Configuration) : Steps classes configuration configuration
  | step {before middle after} :
      Step classes before middle → Steps classes middle after → Steps classes before after

def Stuck (classes : Classes) (configuration : Configuration) : Prop :=
  ¬ configuration.finished ∧ ¬ ∃ after, Step classes configuration after

end Dada.Shared
