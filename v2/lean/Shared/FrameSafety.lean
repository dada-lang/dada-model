import Shared.Frames
import Shared.TypingSafety

namespace Dada.Shared.Framed

open Typing

def ConfigurationTyped (classes : ClassTable) (configuration : Configuration Unpacking.Statement)
    (finalEnvironment : Environment) : Prop :=
  match configuration.frame with
  | none => configuration.objects = []
  | some frame => Typing.ConfigurationTyped classes ⟨configuration.state, frame.code⟩ finalEnvironment

theorem local_wellFormed (typed : Typing.ConfigurationTyped classes configuration finalEnvironment) :
    WellFormed classes.erase configuration.state := by
  obtain ⟨_, realized, _⟩ := typed
  exact realized.ownership.no_pending

theorem ConfigurationTyped.initial (classesWf : classes.WellFormed)
    (typed : SequenceTyped classes [] code finalEnvironment) :
    ConfigurationTyped classes (.initial code) finalEnvironment :=
  ⟨[], Realizes.empty classesWf, typed⟩

theorem ConfigurationTyped.progress
    (typed : ConfigurationTyped classes configuration finalEnvironment) :
    configuration.finished ∨ ∃ after, Step (patternOperation classes.erase) configuration after := by
  rcases configuration with ⟨objects, nextId, frame⟩
  cases frame with
  | none => exact .inl rfl
  | some frame =>
    rcases frame with ⟨variables, code⟩
    have localTyped : Typing.ConfigurationTyped classes ⟨⟨objects, variables, nextId⟩, code⟩ finalEnvironment := typed
    rcases localTyped.progress with finished | ⟨after, step⟩
    · change code = [] at finished
      subst code
      exact .inr ⟨_, exit_step ⟨objects, variables, nextId⟩⟩
    · exact .inr ⟨_, local_step (operation := patternOperation classes.erase)
        (before := ⟨objects, variables, nextId⟩) (code := code) (after := after.state)
        (rest := after.code) step (local_wellFormed (localTyped.preservation step))⟩

theorem ConfigurationTyped.preservation
    (typed : ConfigurationTyped classes before finalEnvironment)
    (step : Step (patternOperation classes.erase) before after) :
    ConfigurationTyped classes after finalEnvironment := by
  cases step with
  | «local» operation =>
    have next := Typing.ConfigurationTyped.preservation typed operation
    rw [collect_running (local_wellFormed next)]
    exact next
  | exit =>
    rw [collect_popped]
    rfl

theorem ConfigurationTyped.trace
    (typed : ConfigurationTyped classes before finalEnvironment)
    (trace : StepsExactly (patternOperation classes.erase) before count after) :
    ConfigurationTyped classes after finalEnvironment := by
  induction trace with
  | refl => exact typed
  | step first _ ih => exact ih (typed.preservation first)

theorem lift_local_trace
    (typed : Typing.ConfigurationTyped classes before finalEnvironment)
    (trace : Unpacking.StepsExactly classes.erase before count after) :
    StepsExactly (patternOperation classes.erase) (.running before.state before.code) count
      (.running after.state after.code) := by
  induction trace with
  | refl => exact .refl _
  | step first _ ih =>
    have next := typed.preservation first
    exact .step (local_step first (local_wellFormed next)) (ih next)

-- Keep the pre-exit state as a witness: it still realizes the final local environment.
theorem completion (typed : Typing.ConfigurationTyped classes before finalEnvironment) :
    ∃ observed,
      StepsExactly (patternOperation classes.erase) (.running before.state before.code)
        before.code.length (.running observed []) ∧
      Realizes classes finalEnvironment observed [] ∧
      StepsExactly (patternOperation classes.erase) (.running before.state before.code)
        (before.code.length + 1) (.terminal observed.nextId) := by
  obtain ⟨last, trace, finished, realized⟩ := typed.finishes
  have lifted := lift_local_trace typed trace
  change last.code = [] at finished
  rw [finished] at lifted
  exact ⟨last.state, lifted, realized, lifted.trans (.step (exit_step _) (.refl _))⟩

theorem ConfigurationTyped.finishes
    (typed : ConfigurationTyped classes configuration finalEnvironment) :
    ∃ nextId, StepsExactly (patternOperation classes.erase) configuration configuration.remaining
      (.terminal nextId) := by
  rcases configuration with ⟨objects, nextId, frame⟩
  cases frame with
  | none =>
    change objects = [] at typed
    subst objects
    exact ⟨nextId, .refl _⟩
  | some frame =>
    obtain ⟨observed, _, _, trace⟩ := completion typed
    exact ⟨observed.nextId, trace⟩

theorem program_safety (classesWf : classes.WellFormed)
    (typed : SequenceTyped classes [] code finalEnvironment)
    (execution : StepsExactly (patternOperation classes.erase) (.initial code) count configuration) :
    ¬ Stuck (patternOperation classes.erase) configuration ∧
    ConfigurationTyped classes configuration finalEnvironment ∧
    count + configuration.remaining = code.length + 1 ∧
    ∃ nextId,
      StepsExactly (patternOperation classes.erase) configuration configuration.remaining (.terminal nextId) ∧
      StepsExactly (patternOperation classes.erase) (.initial code) (code.length + 1) (.terminal nextId) := by
  have current := (ConfigurationTyped.initial classesWf typed).trace execution
  have length : count + configuration.remaining = code.length + 1 := by
    exact (execution.remaining (fun _ _ _ _ step => step.code_length)).symm
  obtain ⟨nextId, rest⟩ := current.finishes
  refine ⟨?_, current, length, nextId, rest, length ▸ execution.trans rest⟩
  intro stuck
  rcases current.progress with finished | next
  · exact stuck.1 finished
  · exact stuck.2 next

end Dada.Shared.Framed
