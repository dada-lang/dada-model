import Functions.Typing

namespace Dada.Correspondence.SharedFunctions

open Shared

def embed (configuration : Unpacking.Configuration) : Functions.Configuration :=
  .running configuration.state ⟨configuration.code.map Functions.Statement.local, none⟩

def terminal (configuration : Unpacking.Configuration) : Functions.Configuration :=
  ⟨[], configuration.state.nextId, []⟩

theorem collect_embed (wf : WellFormed classes configuration.state) :
    (embed configuration).collect = embed configuration := by
  apply Functions.Configuration.collect_eq_self
  intro id data member
  have live := wf.allocated_live (List.mem_map.mpr ⟨(id, data), member, rfl⟩)
  simpa [embed, Functions.Configuration.rootState, Functions.Configuration.running] using live

theorem raw_forward (step : Unpacking.Step classes before after) :
    Functions.RawStep classes declarations (embed before) (embed after) := by
  cases step with
  | letValue eval bind => exact .local (.letValue eval bind)

theorem raw_backward (step : Functions.RawStep classes declarations (embed before) after) :
    (∃ successor, Unpacking.Step classes before successor ∧ after = embed successor) ∨
    (before.finished ∧ after = ⟨before.state.objects, before.state.nextId, []⟩) := by
  rcases before with ⟨⟨objects, variables, nextId⟩, code⟩
  cases code with
  | nil =>
    cases step
    exact .inr ⟨rfl, rfl⟩
  | cons statement rest =>
    cases step with
    | «local» localStep =>
      cases localStep with
      | letValue eval bind => exact .inl ⟨_, .letValue eval bind, rfl⟩

theorem step_forward (classesWf : ClassesWellFormed classes)
    (wf : WellFormed classes before.state) (step : Unpacking.Step classes before after) :
    Functions.Step classes declarations (embed before) (embed after) := by
  have transition := Functions.Step.collect (raw_forward (declarations := declarations) step)
  rwa [collect_embed (step.preserves_wellFormed classesWf wf)] at transition

theorem exit_forward (finished : configuration.finished) :
    Functions.Step classes declarations (embed configuration) (terminal configuration) := by
  rcases configuration with ⟨⟨objects, variables, nextId⟩, code⟩
  cases finished
  simpa [embed, terminal] using
    (Functions.Step.collect (Functions.RawStep.exit (classes := classes)
      (declarations := declarations) (objects := objects) (variables := variables) (nextId := nextId)))

theorem step_backward (classesWf : ClassesWellFormed classes)
    (wf : WellFormed classes before.state)
    (step : Functions.Step classes declarations (embed before) after) :
    (∃ successor, Unpacking.Step classes before successor ∧ after = embed successor) ∨
      (before.finished ∧ after = terminal before) := by
  cases step with
  | collect raw =>
    rcases raw_backward raw with ⟨successor, oldStep, rfl⟩ | ⟨finished, rfl⟩
    · exact .inl ⟨successor, oldStep, collect_embed (oldStep.preserves_wellFormed classesWf wf)⟩
    · exact .inr ⟨finished, Functions.Configuration.collect_empty_frames _ _⟩

theorem step_correspondence (classesWf : ClassesWellFormed classes)
    (wf : WellFormed classes before.state) :
    Functions.Step classes declarations (embed before) after ↔
      (∃ successor, Unpacking.Step classes before successor ∧ after = embed successor) ∨
      (before.finished ∧ after = terminal before) := by
  constructor
  · exact step_backward classesWf wf
  · rintro (⟨successor, step, rfl⟩ | ⟨finished, rfl⟩)
    · exact step_forward classesWf wf step
    · exact exit_forward finished

theorem steps_forward (classesWf : ClassesWellFormed classes)
    (wf : WellFormed classes before.state) (steps : Unpacking.Steps classes before after) :
    Functions.Steps classes declarations (embed before) (embed after) := by
  induction steps with
  | refl => exact .refl _
  | step step _ ih =>
    exact .step (step_forward classesWf wf step) (ih (step.preserves_wellFormed classesWf wf))

theorem steps_backward (classesWf : ClassesWellFormed classes)
    (steps : Functions.Steps classes declarations start after) :
    ∀ before, WellFormed classes before.state → start = embed before →
      ∃ successor, Unpacking.Steps classes before successor ∧
        (after = embed successor ∨ (successor.finished ∧ after = terminal successor)) := by
  induction steps with
  | refl =>
    intro before _ equality
    exact ⟨before, .refl _, .inl equality⟩
  | step step rest ih =>
    intro before wf equality
    subst equality
    rcases step_backward classesWf wf step with ⟨middle, first, rfl⟩ | ⟨finished, rfl⟩
    · obtain ⟨last, trace, result⟩ := ih middle (first.preserves_wellFormed classesWf wf) rfl
      exact ⟨last, .step first trace, result⟩
    · cases rest with
      | refl => exact ⟨before, .refl _, .inr ⟨finished, rfl⟩⟩
      | step impossible _ => exact False.elim (Functions.finished_no_step (configuration := terminal before) rfl impossible)

theorem finished_correspondence :
    configuration.finished ↔
      Functions.Step classes declarations (embed configuration) (terminal configuration) := by
  constructor
  · exact exit_forward
  · intro step
    generalize equality : terminal configuration = target at step
    cases step with
    | collect raw =>
      rcases raw_backward raw with ⟨successor, _, rfl⟩ | ⟨finished, _⟩
      · have frames := congrArg Functions.Configuration.frames equality
        simp [embed, terminal, Functions.Configuration.running] at frames
      · exact finished

theorem stuck_correspondence (classesWf : ClassesWellFormed classes)
    (wf : WellFormed classes configuration.state) :
    Functions.Stuck classes declarations (embed configuration) ↔
      Unpacking.Stuck classes configuration := by
  constructor
  · rintro ⟨_, noStep⟩
    exact ⟨fun finished => noStep ⟨_, exit_forward finished⟩,
      fun ⟨after, step⟩ => noStep ⟨_, step_forward classesWf wf step⟩⟩
  · rintro ⟨unfinished, noStep⟩
    refine ⟨by simp [Functions.Configuration.finished, embed, Functions.Configuration.running], ?_⟩
    rintro ⟨after, step⟩
    rcases step_backward classesWf wf step with ⟨successor, oldStep, _⟩ | ⟨finished, _⟩
    · exact noStep ⟨successor, oldStep⟩
    · exact unfinished finished

theorem typing_forward
    (typed : Typing.SequenceTyped classes before code after) :
    Functions.SequenceTyped classes declarations before (code.map Functions.Statement.local) after := by
  induction typed with
  | nil wf => exact .nil wf
  | cons statement _ ih => exact .cons (.local statement) ih

theorem typing_backward
    (typed : Functions.SequenceTyped classes declarations before code after) :
    ∀ original, code = original.map Functions.Statement.local →
      Typing.SequenceTyped classes before original after := by
  induction typed with
  | nil wf =>
    intro original equality
    have : original = [] := by simpa using equality.symm
    subst original
    exact .nil wf
  | cons statement _ ih =>
    intro original equality
    cases original with
    | nil => simp at equality
    | cons first rest =>
      simp only [List.map_cons, List.cons.injEq] at equality
      obtain ⟨rfl, tail⟩ := equality
      cases statement with
      | «local» typed => exact .cons typed (ih rest tail)

theorem typing_correspondence :
    Functions.SequenceTyped classes declarations before (code.map Functions.Statement.local) after ↔
      Typing.SequenceTyped classes before code after :=
  ⟨fun typed => typing_backward typed code rfl, typing_forward⟩

end Dada.Correspondence.SharedFunctions
