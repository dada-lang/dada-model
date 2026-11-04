import Shared.Liveness
import Shared.Unpacking

noncomputable section

namespace Dada.Shared

-- Collection is outside expression evaluation, after all temporary results transfer.
def State.collect (state : State) : State := by
  classical
  exact { state with objects := state.objects.filter (fun entry => decide (Live state entry.1)) }

theorem State.collect_eq_self (wf : WellFormed classes state) : state.collect = state := by
  classical
  have keep : state.objects.filter (fun entry => decide (Live state entry.1)) = state.objects :=
    List.filter_eq_self.mpr (by
      intro entry member
      simpa using wf.allocated_live (List.mem_map.mpr ⟨entry, member, rfl⟩))
  simp [State.collect, keep]

theorem Live.has_variable (live : Live state object) : ∃ name reference,
    (name, some reference) ∈ state.variables := by
  induction live with
  | «variable» member => exact ⟨_, _, member⟩
  | field _ _ _ ih => exact ih

theorem State.collect_no_variables (objects : List (ObjectId × Object)) (nextId : Nat) :
    (State.mk objects [] nextId).collect = ⟨[], [], nextId⟩ := by
  have dead : ∀ id, ¬ Live ⟨objects, [], nextId⟩ id := by
    intro id live
    obtain ⟨_, _, member⟩ := live.has_variable
    simp at member
  simp [State.collect, dead]

namespace Framed

structure Frame (Instruction : Type) where
  variables : List (VariableId × Slot)
  code : List Instruction
  deriving Repr

structure Configuration (Instruction : Type) where
  objects : List (ObjectId × Object)
  nextId : Nat
  frame : Option (Frame Instruction)
  deriving Repr

def Configuration.running (state : State) (code : List Instruction) : Configuration Instruction :=
  ⟨state.objects, state.nextId, some ⟨state.variables, code⟩⟩

def Configuration.terminal (nextId : Nat) : Configuration Instruction := ⟨[], nextId, none⟩

def Configuration.initial (code : List Instruction) : Configuration Instruction :=
  .running State.empty code

def Configuration.state (configuration : Configuration Instruction) : State :=
  ⟨configuration.objects, configuration.frame.map Frame.variables |>.getD [], configuration.nextId⟩

def Configuration.collect (configuration : Configuration Instruction) : Configuration Instruction :=
  { configuration with objects := configuration.state.collect.objects }

def Configuration.finished (configuration : Configuration Instruction) : Prop :=
  configuration.frame = none

def Configuration.remaining (configuration : Configuration Instruction) : Nat :=
  match configuration.frame with
  | none => 0
  | some frame => frame.code.length + 1

abbrev LocalStep (Instruction : Type) := State → List Instruction → State → List Instruction → Prop

def baseOperation (classes : Classes) : LocalStep Statement :=
  fun before code after rest => Dada.Shared.Step classes ⟨before, code⟩ ⟨after, rest⟩

def patternOperation (classes : Classes) : LocalStep Unpacking.Statement :=
  fun before code after rest => Unpacking.Step classes ⟨before, code⟩ ⟨after, rest⟩

-- The public machine always collects; local operations are auxiliary judgments.
inductive Step (operation : LocalStep Instruction) : Configuration Instruction → Configuration Instruction → Prop where
  | «local» {before after code rest} :
      operation before code after rest →
      Step operation (.running before code) (Configuration.running after rest).collect
  | exit {state} :
      Step operation (.running state []) (Configuration.mk state.objects state.nextId none).collect

inductive StepsExactly (operation : LocalStep Instruction) : Configuration Instruction → Nat → Configuration Instruction → Prop where
  | refl (configuration) : StepsExactly operation configuration 0 configuration
  | step {before middle after count} :
      Step operation before middle → StepsExactly operation middle count after →
      StepsExactly operation before (count + 1) after

def Steps (operation : LocalStep Instruction) (before after : Configuration Instruction) : Prop :=
  ∃ count, StepsExactly operation before count after

def Stuck (operation : LocalStep Instruction) (configuration : Configuration Instruction) : Prop :=
  ¬ configuration.finished ∧ ¬ ∃ after, Step operation configuration after

variable {Instruction : Type} {operation : LocalStep Instruction}

theorem collect_running (wf : WellFormed classes state) :
    (Configuration.running state code).collect = .running state code := by
  have same := congrArg State.objects (State.collect_eq_self wf)
  simpa [Configuration.collect, Configuration.running, Configuration.state] using
    congrArg (fun objects => Configuration.mk objects state.nextId (some ⟨state.variables, code⟩)) same

theorem collect_popped (objects : List (ObjectId × Object)) (nextId : Nat) :
    (Configuration.mk objects nextId (none : Option (Frame Instruction))).collect = .terminal nextId := by
  simp [Configuration.collect, Configuration.state, State.collect_no_variables, Configuration.terminal]

theorem local_step (step : operation before code after rest)
    (wf : WellFormed classes after) :
    Step operation (.running before code) (.running after rest) := by
  simpa only [collect_running wf] using Step.local step

theorem exit_step (state : State) :
    Step operation (Configuration.running state []) (.terminal state.nextId) := by
  simpa only [collect_popped] using (Step.exit (operation := operation) (state := state))

theorem finished_no_step (finished : configuration.finished) :
    ¬ Step operation configuration after := by
  intro step
  cases step <;> simp_all [Configuration.finished, Configuration.running]

theorem terminal_heap_empty (step : Step operation before after) (finished : after.finished) :
    after.objects = [] := by
  cases step with
  | «local» => simp [Configuration.finished, Configuration.collect, Configuration.running] at finished
  | exit => simp [collect_popped, Configuration.terminal]

theorem StepsExactly.trans (first : StepsExactly operation before count middle)
    (second : StepsExactly operation middle later after) :
    StepsExactly operation before (count + later) after := by
  induction first with
  | refl => simpa using second
  | step first _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      StepsExactly.step first (ih second)

theorem step_remaining
    (decreases : ∀ before code after rest, operation before code after rest → code.length = rest.length + 1)
    (step : Step operation before after) : before.remaining = after.remaining + 1 := by
  cases step with
  | «local» localStep =>
    simpa [Configuration.remaining, Configuration.collect, Configuration.running]
      using decreases _ _ _ _ localStep
  | exit => simp [Configuration.remaining, Configuration.collect, Configuration.running]

theorem StepsExactly.remaining
    (decreases : ∀ before code after rest, operation before code after rest → code.length = rest.length + 1)
    (steps : StepsExactly operation before count after) : before.remaining = count + after.remaining := by
  induction steps with
  | refl => simp
  | step first _ ih => have := step_remaining decreases first; omega

theorem terminal_wellFormed (classes : Classes) (nextId : Nat) :
    WellFormed classes (Configuration.terminal (Instruction := Instruction) nextId).state := by
  constructor <;> simp [Configuration.terminal, Configuration.state, References, Allocated, Owners]

theorem Step.preserves
    (preserves : ∀ before code after rest, WellFormed classes before →
      operation before code after rest → WellFormed classes after)
    (wf : WellFormed classes before.state) (step : Step operation before after) :
    WellFormed classes after.state := by
  cases step with
  | «local» localStep =>
    have next := preserves _ _ _ _ wf localStep
    rw [collect_running next]
    exact next
  | exit =>
    rw [collect_popped]
    exact terminal_wellFormed _ _

theorem StepsExactly.preserves
    (preserves : ∀ before code after rest, WellFormed classes before →
      operation before code after rest → WellFormed classes after)
    (wf : WellFormed classes before.state) (steps : StepsExactly operation before count after) :
    WellFormed classes after.state := by
  induction steps with
  | refl => exact wf
  | step first _ ih => exact ih (first.preserves preserves wf)

theorem base_preservation (classesWf : ClassesWellFormed classes)
    (wf : WellFormed classes before.state) (step : Step (baseOperation classes) before after) :
    WellFormed classes after.state :=
  step.preserves (fun _ _ _ _ wf operation => operation.preserves_wellFormed classesWf wf) wf

theorem pattern_preservation (classesWf : ClassesWellFormed classes)
    (wf : WellFormed classes before.state) (step : Step (patternOperation classes) before after) :
    WellFormed classes after.state :=
  step.preserves (fun _ _ _ _ wf operation => operation.preserves_wellFormed classesWf wf) wf

end Framed
end Dada.Shared
end
