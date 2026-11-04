import Destructors.Syntax
import Shared.Frames

noncomputable section

namespace Dada.Destructors

open Shared

abbrev Store := List (VariableId × Slot)

structure Frame where
  variables : Store
  body : Body
  destination : Option VariableId
  deriving Repr

structure Configuration where
  objects : List (ObjectId × Object)
  nextId : Nat
  frames : List Frame
  deriving Repr

def Configuration.running (state : State) (body : Body)
    (frames : List Frame := []) (destination : Option VariableId := none) : Configuration :=
  ⟨state.objects, state.nextId, ⟨state.variables, body, destination⟩ :: frames⟩

def Configuration.initial (program : Program) : Configuration :=
  .running State.empty ⟨program.main, none⟩

def Configuration.finished (configuration : Configuration) : Prop :=
  configuration.frames = []

-- Flattening is only for reachability; evaluation uses the top frame alone.
def Configuration.rootState (configuration : Configuration) : State :=
  ⟨configuration.objects, configuration.frames.flatMap Frame.variables, configuration.nextId⟩

def Configuration.roots (configuration : Configuration) : List Reference :=
  configuration.rootState.variables.filterMap Prod.snd

-- A mathematical collector, not an executable graph-traversal algorithm.
def Configuration.collect (configuration : Configuration) : Configuration := by
  exact { configuration with objects := configuration.rootState.collect.objects }

theorem Configuration.collect_frames (configuration : Configuration) :
    configuration.collect.frames = configuration.frames := rfl

theorem Configuration.collect_nextId (configuration : Configuration) :
    configuration.collect.nextId = configuration.nextId := rfl

theorem Configuration.collect_eq_self (configuration : Configuration)
    (rooted : ∀ id data, (id, data) ∈ configuration.objects → Live configuration.rootState id) :
    configuration.collect = configuration := by
  classical
  have same : configuration.objects.filter (fun entry => decide (Live configuration.rootState entry.1)) =
      configuration.objects := List.filter_eq_self.mpr (by
    intro entry member
    simpa using rooted entry.1 entry.2 member)
  change { configuration with objects := (configuration.objects.filter
    (fun entry => decide (Live configuration.rootState entry.1))) } = configuration
  rw [same]

theorem live_has_root (live : Live state object) : ∃ name reference,
    (name, some reference) ∈ state.variables := by
  induction live with
  | «variable» member => exact ⟨_, _, member⟩
  | field _ _ _ ih => exact ih

theorem no_roots_not_live (objects : List (ObjectId × Object)) (nextId : Nat) (object : ObjectId) :
    ¬ Live ⟨objects, [], nextId⟩ object := by
  intro live
  obtain ⟨_, _, member⟩ := live_has_root live
  simp at member

theorem Configuration.collect_empty_frames (objects : List (ObjectId × Object)) (nextId : Nat) :
    (Configuration.mk objects nextId []).collect = ⟨[], nextId, []⟩ := by
  simp [Configuration.collect, State.collect, Configuration.rootState, no_roots_not_live]

theorem Configuration.collect_empty_heap (nextId : Nat) (frames : List Frame) :
    (Configuration.mk [] nextId frames).collect = ⟨[], nextId, frames⟩ := by
  simp [Configuration.collect, State.collect, Configuration.rootState]

def parameterStore (parameters : List Parameter) (references : List Reference) : Store :=
  (parameters.map Functions.Parameter.name).zip (references.map some)

inductive ResultEval (classes : Classes) : State → Option Value → State → Option Reference → Prop where
  | none (state : State) : ResultEval classes state none state none
  | some {before after value reference} :
      Eval classes before value after reference →
      ResultEval classes before (some value) after (some reference)

inductive Deliver : Store → Option VariableId → Option Reference → Store → Prop where
  | none (variables : Store) : Deliver variables none none variables
  | some {variables name reference} :
      name ∉ variables.map Prod.fst →
      Deliver variables (some name) (some reference) ((name, some reference) :: variables)

def DestinationMatches (destination : Option VariableId)
    (result : Option Shared.Typing.FieldType) : Prop :=
  destination.isSome = result.isSome

-- Frame completion is a runtime check of roots, not a view-based test.
def StoreFinished (classes : Classes) (state : State) : Prop :=
  ∀ name reference, (name, some reference) ∈ state.variables →
    StructReference classes state reference

-- Raw transitions transfer all temporary values before collection.
inductive RawStep (classes : Classes) (declarations : Declarations) : Configuration → Configuration → Prop where
  | local {before after statement rest result frames destination} :
      Unpacking.Step classes ⟨before, [statement]⟩ ⟨after, []⟩ →
      RawStep classes declarations
        (.running before ⟨.local statement :: rest, result⟩ frames destination)
        (.running after ⟨rest, result⟩ frames destination)
  | call {before evaluated destination name arguments rest result frames returnTo
      declaration references} :
      (name, declaration) ∈ declarations →
      DestinationMatches destination declaration.signature.result →
      (∀ x ∈ destination, x ∉ before.variables.map Prod.fst) →
      EvalArgs classes before arguments evaluated references →
      references.length = declaration.signature.parameters.length →
      RawStep classes declarations
        (.running before ⟨.call destination name arguments :: rest, result⟩ frames returnTo)
        (.running { evaluated with variables := parameterStore declaration.signature.parameters references }
          declaration.body (⟨evaluated.variables, ⟨rest, result⟩, returnTo⟩ :: frames) destination)
  | dropStruct {before evaluated place reference rest result frames destination} :
      Eval classes before (.give place) evaluated reference →
      StructReference classes evaluated reference →
      RawStep classes declarations
        (.running before ⟨.dropStruct place :: rest, result⟩ frames destination)
        (.running evaluated ⟨rest, result⟩ frames destination)
  | «return» {before evaluated result reference caller frames destination variables} :
      ResultEval classes before result evaluated reference →
      Deliver caller.variables destination reference variables →
      StoreFinished classes evaluated →
      RawStep classes declarations
        (.running before ⟨[], result⟩ (caller :: frames) destination)
        (.running { evaluated with variables := variables } caller.body frames caller.destination)
  | exit {objects nextId variables} :
      StoreFinished classes ⟨objects, variables, nextId⟩ →
      RawStep classes declarations
        (.running ⟨objects, variables, nextId⟩ ⟨[], none⟩) ⟨objects, nextId, []⟩

inductive Step (classes : Classes) (declarations : Declarations) : Configuration → Configuration → Prop where
  | collect {before raw} : RawStep classes declarations before raw →
      Step classes declarations before raw.collect

inductive Steps (classes : Classes) (declarations : Declarations) : Configuration → Configuration → Prop where
  | refl (configuration : Configuration) : Steps classes declarations configuration configuration
  | step {before middle after} :
      Step classes declarations before middle → Steps classes declarations middle after →
      Steps classes declarations before after

def Stuck (classes : Classes) (declarations : Declarations) (configuration : Configuration) : Prop :=
  ¬ configuration.finished ∧ ¬ ∃ after, Step classes declarations configuration after

theorem finished_no_step (finished : configuration.finished) :
    ¬ Step classes declarations configuration after := by
  intro step
  cases step with
  | collect raw => cases raw <;> simp_all [Configuration.finished, Configuration.running]

theorem terminal_heap_empty (step : Step classes declarations before after)
    (finished : after.finished) : after.objects = [] := by
  cases step with
  | collect raw =>
    cases raw <;> simp_all [Configuration.finished, Configuration.running,
      Configuration.collect_frames, Configuration.collect_empty_frames]

theorem Steps.trans (first : Steps classes declarations before middle)
    (second : Steps classes declarations middle after) : Steps classes declarations before after := by
  induction first with
  | refl => exact second
  | step step _ ih => exact .step step (ih second)

end Dada.Destructors

attribute [simp] Dada.Destructors.Configuration.collect_frames
  Dada.Destructors.Configuration.collect_nextId Dada.Destructors.no_roots_not_live
  Dada.Destructors.Configuration.collect_empty_frames Dada.Destructors.Configuration.collect_empty_heap

end
