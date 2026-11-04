import Correspondence.SharedFunctions
import Shared.Frames

namespace Dada.Correspondence.SharedFunctions

open Shared

def embedFramed (configuration : Framed.Configuration Unpacking.Statement) : Functions.Configuration :=
  ⟨configuration.objects, configuration.nextId,
    match configuration.frame with
    | none => []
    | some frame => [⟨frame.variables, ⟨frame.code.map Functions.Statement.local, none⟩, none⟩]⟩

theorem embedFramed_collect (configuration : Framed.Configuration Unpacking.Statement) :
    embedFramed configuration.collect = (embedFramed configuration).collect := by
  rcases configuration with ⟨objects, nextId, frame⟩
  cases frame <;> simp [embedFramed, Framed.Configuration.collect, Framed.Configuration.state,
    Functions.Configuration.collect, Functions.Configuration.rootState]

theorem framed_step_forward
    (step : Framed.Step (Framed.patternOperation classes) before after) :
    Functions.Step classes declarations (embedFramed before) (embedFramed after) := by
  cases step with
  | «local» operation =>
    rw [embedFramed_collect]
    exact .collect (raw_forward operation)
  | @exit state =>
    rw [Framed.collect_popped]
    exact exit_forward (configuration := ⟨state, []⟩) rfl

theorem framed_step_backward
    (step : Functions.Step classes declarations (embedFramed before) after) :
    ∃ successor, Framed.Step (Framed.patternOperation classes) before successor ∧ after = embedFramed successor := by
  rcases before with ⟨objects, nextId, frame⟩
  cases frame with
  | none => exact False.elim (Functions.finished_no_step (configuration := embedFramed ⟨objects, nextId, none⟩) rfl step)
  | some frame =>
    rcases frame with ⟨variables, code⟩
    change Functions.Step classes declarations (embed ⟨⟨objects, variables, nextId⟩, code⟩) after at step
    cases step with
    | collect raw =>
      rcases raw_backward raw with ⟨successor, operation, rfl⟩ | ⟨finished, rfl⟩
      · exact ⟨(Framed.Configuration.running successor.state successor.code).collect,
          .local (before := ⟨objects, variables, nextId⟩) (code := code) operation,
          (embedFramed_collect (.running successor.state successor.code)).symm⟩
      · change code = [] at finished
        subst code
        exact ⟨_, Framed.exit_step ⟨objects, variables, nextId⟩,
          Functions.Configuration.collect_empty_frames _ _⟩

theorem framed_step_correspondence :
    Functions.Step classes declarations (embedFramed before) after ↔
      ∃ successor, Framed.Step (Framed.patternOperation classes) before successor ∧ after = embedFramed successor := by
  constructor
  · exact framed_step_backward
  · rintro ⟨successor, step, rfl⟩
    exact framed_step_forward step

theorem framed_steps_forward
    (steps : Framed.StepsExactly (Framed.patternOperation classes) before count after) :
    Functions.Steps classes declarations (embedFramed before) (embedFramed after) := by
  induction steps with
  | refl => exact .refl _
  | step first _ ih => exact .step (framed_step_forward first) ih

theorem framed_steps_backward (steps : Functions.Steps classes declarations start after) :
    ∀ before, start = embedFramed before →
      ∃ successor, Framed.Steps (Framed.patternOperation classes) before successor ∧ after = embedFramed successor := by
  induction steps with
  | refl => intro before equality; exact ⟨before, ⟨0, .refl _⟩, equality⟩
  | step first _ ih =>
    intro before equality
    subst equality
    obtain ⟨middle, original, rfl⟩ := framed_step_backward first
    obtain ⟨last, ⟨count, rest⟩, equality⟩ := ih middle rfl
    exact ⟨last, ⟨count + 1, .step original rest⟩, equality⟩

theorem framed_finished_correspondence :
    (embedFramed configuration).finished ↔ configuration.finished := by
  rcases configuration with ⟨objects, nextId, frame⟩
  cases frame <;> simp [embedFramed, Functions.Configuration.finished, Framed.Configuration.finished]

theorem framed_stuck_correspondence :
    Functions.Stuck classes declarations (embedFramed configuration) ↔
      Framed.Stuck (Framed.patternOperation classes) configuration := by
  simp only [Functions.Stuck, Framed.Stuck, framed_finished_correspondence]
  constructor
  · rintro ⟨unfinished, noStep⟩
    exact ⟨unfinished, fun ⟨after, step⟩ => noStep ⟨_, framed_step_forward step⟩⟩
  · rintro ⟨unfinished, noStep⟩
    refine ⟨unfinished, ?_⟩
    rintro ⟨after, step⟩
    obtain ⟨successor, original, _⟩ := framed_step_backward step
    exact noStep ⟨successor, original⟩

end Dada.Correspondence.SharedFunctions
