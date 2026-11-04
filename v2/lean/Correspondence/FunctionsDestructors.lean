import Destructors.Safety

namespace Dada.Correspondence.FunctionsDestructors
open Shared Shared.Typing

-- This embedding has no destructor declarations or drop statements. It isolates
-- inherited behavior; the new frame-completion obligations remain explicit.
def name : Functions.Name → Destructors.Name
  | .function n => .function n
  | .method owner n => .method owner n

def statement : Functions.Statement → Destructors.Statement
  | .local s => .local s
  | .call destination target arguments => .call destination (name target) arguments

def body (b : Functions.Body) : Destructors.Body := ⟨b.statements.map statement, b.result⟩
def declaration (d : Functions.Declaration) : Destructors.Declaration := ⟨d.signature, body d.body⟩
def declarations (ds : Functions.Declarations) : Destructors.Declarations :=
  ds.map fun (n,d) => (name n, declaration d)
def frame (f : Functions.Frame) : Destructors.Frame := ⟨f.variables, body f.body, f.destination⟩
def configuration (c : Functions.Configuration) : Destructors.Configuration :=
  ⟨c.objects,c.nextId,c.frames.map frame⟩

theorem collect (c : Functions.Configuration) :
    configuration c.collect = (configuration c).collect := by
  simp only [configuration, Functions.Configuration.collect, Destructors.Configuration.collect,
    Functions.Configuration.rootState, Destructors.Configuration.rootState, List.flatMap_map,
    frame]

theorem running (state : State) (b : Functions.Body) (fs : List Functions.Frame) (dest : Option VariableId) :
    configuration (.running state b fs dest) = .running state (body b) (fs.map frame) dest := rfl

theorem resultEval (evaluation : Functions.ResultEval classes before value after reference) :
    Destructors.ResultEval classes before value after reference := by
  cases evaluation with
  | none => exact .none _
  | some e => exact .some e

theorem deliver (delivery : Functions.Deliver before destination reference after) :
    Destructors.Deliver before destination reference after := by
  cases delivery with
  | none => exact .none _
  | some fresh => exact .some fresh

-- A boundary guard is supplied for every possible return evaluation. For local
-- statements and calls the condition is vacuous, so those steps are unchanged.
def ExitAllowed (classes : Classes) (c : Functions.Configuration) : Prop :=
  ∀ state result fs dest,
    c = .running state ⟨[],result⟩ fs dest →
    ∀ evaluated reference, Functions.ResultEval classes state result evaluated reference →
      Destructors.StoreFinished classes evaluated

theorem raw_forward
    (step : Functions.RawStep classes ds before after)
    (allowed : ExitAllowed classes before) :
    Destructors.RawStep classes (declarations ds) (configuration before) (configuration after) := by
  cases step with
  | «local» operation => exact .local operation
  | @call before evaluated destination target arguments rest result frames returnTo decl references declared shape fresh evaluation lengths =>
    exact .call (declaration := declaration decl) (evaluated := evaluated) (List.mem_map.mpr ⟨_,declared,rfl⟩) shape fresh evaluation lengths
  | @«return» before evaluated result reference caller frames destination variables evaluation delivered =>
    exact .return (evaluated := evaluated) (resultEval evaluation) (deliver delivered) (allowed _ _ _ _ rfl _ _ evaluation)
  | exit => exact .exit (allowed _ _ _ _ rfl _ _ (.none _))

theorem step_forward
    (step : Functions.Step classes ds before after)
    (allowed : ExitAllowed classes before) :
    Destructors.Step classes (declarations ds) (configuration before) (configuration after) := by
  cases step with
  | collect raw => rw [collect]; exact .collect (raw_forward raw allowed)

theorem resultEval_backward (evaluation : Destructors.ResultEval classes before value after reference) :
    Functions.ResultEval classes before value after reference := by
  cases evaluation with
  | none => exact .none _
  | some e => exact .some e

theorem deliver_backward (delivery : Destructors.Deliver before destination reference after) :
    Functions.Deliver before destination reference after := by
  cases delivery with
  | none => exact .none _
  | some fresh => exact .some fresh

theorem name_injective : Function.Injective name := by
  intro a b eq
  cases a <;> cases b <;> simp_all [name]

theorem raw_backward {before : Functions.Configuration}
    (step : Destructors.RawStep classes (declarations ds) (configuration before) after) :
    ∃ successor, Functions.RawStep classes ds before successor ∧ after = configuration successor := by
  rcases before with ⟨objects,nextId,frames⟩
  cases frames with
  | nil => cases step
  | cons active rest =>
    rcases active with ⟨variables,⟨code,result⟩,destination⟩
    cases code with
    | nil =>
      cases rest with
      | nil =>
        cases step with
        | exit _ => exact ⟨_, .exit, rfl⟩
      | cons caller rest =>
        cases step with
        | «return» evaluation delivery _ =>
          exact ⟨_, .return (resultEval_backward evaluation) (deliver_backward delivery), rfl⟩
    | cons first tail =>
      cases first with
      | «local» localStatement =>
        cases step with
        | «local» operation => exact ⟨_, .local operation, rfl⟩
      | call dest target args =>
        cases step with
        | call declared shape fresh evaluation lengths =>
          obtain ⟨⟨oldName,oldDeclaration⟩, oldMember, equal⟩ := List.mem_map.mp declared
          have names := name_injective (congrArg Prod.fst equal)
          subst oldName
          have bodies := congrArg Prod.snd equal
          dsimp at bodies
          subst bodies
          exact ⟨_, .call oldMember shape fresh evaluation lengths, rfl⟩

theorem step_backward
    (step : Destructors.Step classes (declarations ds) (configuration before) after) :
    ∃ successor, Functions.Step classes ds before successor ∧ after = configuration successor := by
  cases step with
  | collect raw =>
    obtain ⟨successor, original, rfl⟩ := raw_backward raw
    exact ⟨successor.collect, .collect original, (collect successor).symm⟩

theorem step_correspondence (allowed : ExitAllowed classes before) :
    Destructors.Step classes (declarations ds) (configuration before) after ↔
      ∃ successor, Functions.Step classes ds before successor ∧ after = configuration successor := by
  constructor
  · exact step_backward
  · rintro ⟨successor, step, rfl⟩
    exact step_forward step allowed

theorem steps_backward (steps : Destructors.Steps classes (declarations ds) start after) :
    ∀ before, start = configuration before →
      ∃ successor, Functions.Steps classes ds before successor ∧ after = configuration successor := by
  induction steps with
  | refl => intro before eq; exact ⟨before, .refl _, eq⟩
  | step first _ ih =>
    intro before eq
    subst eq
    obtain ⟨middle, original, rfl⟩ := step_backward first
    obtain ⟨last, rest, eq⟩ := ih middle rfl
    exact ⟨last, .step original rest, eq⟩

theorem finished (c : Functions.Configuration) :
    (configuration c).finished ↔ c.finished := by
  simp [Destructors.Configuration.finished, Functions.Configuration.finished, configuration]

end Dada.Correspondence.FunctionsDestructors
