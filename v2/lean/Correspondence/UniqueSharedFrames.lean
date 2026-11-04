import Correspondence.UniqueSharedUnpacking
import Unique.Frames
import Shared.Frames

namespace Dada.Correspondence.Framed

-- Reachability ignores the added unique permission tags.
theorem live_forward (live : Unique.Live state object) :
    Shared.Live (embedState state) (embedId object) := by
  induction live with
  | «variable» stored =>
    exact .variable (reference := embedReference _) (List.mem_map.mpr ⟨(_, _), stored, rfl⟩)
  | field _ stored field ih =>
    exact .field ih (List.mem_map.mpr ⟨(_, _), stored, rfl⟩)
      (List.mem_map.mpr ⟨(_, _), field, rfl⟩)

theorem live_erase (live : Shared.Live state object) :
    Unique.Live (eraseState state) (eraseId object) := by
  induction live with
  | «variable» stored =>
    exact .variable (List.mem_map.mpr ⟨(_, _), stored, rfl⟩)
  | field _ stored field ih =>
    exact .field ih (List.mem_map.mpr ⟨(_, _), stored, rfl⟩)
      (List.mem_map.mpr ⟨(_, _), field, rfl⟩)

theorem live_correspondence :
    Shared.Live (embedState state) (embedId object) ↔ Unique.Live state object :=
  ⟨fun live => by simpa using live_erase live, live_forward⟩

theorem collect_correspondence (state : Unique.State) :
    (embedState state).collect = embedState state.collect := by
  classical
  have objects : (state.objects.map (fun entry => (embedId entry.1, embedObject entry.2))).filter
      (fun entry => decide (Shared.Live (embedState state) entry.1)) =
      (state.objects.filter (fun entry => decide (Unique.Live state entry.1))).map
        (fun entry => (embedId entry.1, embedObject entry.2)) := by
    induction state.objects with
    | nil => rfl
    | cons entry rest ih =>
      simp only [List.map_cons, List.filter_cons]
      simp only [live_correspondence]
      split <;> simp_all
  change Shared.State.mk _ _ _ = Shared.State.mk _ _ _
  exact congrArg (fun objects => Shared.State.mk objects (embedSlots state.variables) state.nextId) objects

def embed (instruction : I → J) (configuration : Unique.Framed.Configuration I) : Shared.Framed.Configuration J :=
  ⟨(embedState configuration.state).objects, configuration.nextId,
    configuration.frame.map fun frame => ⟨embedSlots frame.variables, frame.code.map instruction⟩⟩

theorem embed_collect (instruction : I → J) (configuration : Unique.Framed.Configuration I) :
    embed instruction configuration.collect = (embed instruction configuration).collect := by
  have same := congrArg Shared.State.objects (collect_correspondence configuration.state)
  rcases configuration with ⟨objects, nextId, frame⟩
  cases frame <;> simp_all [embed, Unique.Framed.Configuration.collect,
    Shared.Framed.Configuration.collect, Unique.Framed.Configuration.state,
    Shared.Framed.Configuration.state, embedState, embedSlots]

-- Abstract over the instruction translation to cover both binding grammars.
theorem step_forward {original : Unique.Framed.LocalStep I} {translated : Shared.Framed.LocalStep J}
    (instruction : I → J)
    (forward : ∀ state code after rest, original state code after rest →
      translated (embedState state) (code.map instruction) (embedState after) (rest.map instruction))
    (step : Unique.Framed.Step original before after) :
    Shared.Framed.Step translated (embed instruction before) (embed instruction after) := by
  cases step with
  | «local» operation =>
    rw [embed_collect]
    exact .local (forward _ _ _ _ operation)
  | @exit state =>
    rw [Unique.Framed.collect_popped]
    exact Shared.Framed.exit_step (embedState state)

theorem step_backward {original : Unique.Framed.LocalStep I} {translated : Shared.Framed.LocalStep J}
    (instruction : I → J)
    (backward : ∀ state code after rest,
      translated (embedState state) (code.map instruction) after rest →
      ∃ next remaining, original state code next remaining ∧ after = embedState next ∧ rest = remaining.map instruction)
    (step : Shared.Framed.Step translated (embed instruction before) after) :
    ∃ successor, Unique.Framed.Step original before successor ∧ after = embed instruction successor := by
  rcases before with ⟨objects, nextId, frame⟩
  cases frame with
  | none => exact False.elim (Shared.Framed.finished_no_step (configuration := embed instruction ⟨objects, nextId, none⟩) rfl step)
  | some frame =>
    rcases frame with ⟨variables, code⟩
    change Shared.Framed.Step translated
      (.running (embedState ⟨objects, variables, nextId⟩) (code.map instruction)) after at step
    generalize equality : Shared.Framed.Configuration.running
      (embedState ⟨objects, variables, nextId⟩) (code.map instruction) = start at step
    cases step with
    | @«local» beforeState afterState beforeCode afterCode operation =>
      cases beforeState
      have sameState := congrArg Shared.Framed.Configuration.state equality
      have sameCode := congrArg (fun c => c.frame.map Shared.Framed.Frame.code) equality
      simp only [Shared.Framed.Configuration.state, Shared.Framed.Configuration.running,
        Option.map_some, Option.getD_some] at sameState
      simp only [Shared.Framed.Configuration.running, Option.map_some, Option.some.injEq] at sameCode
      rw [← sameState, ← sameCode] at operation
      obtain ⟨next, rest, originalStep, rfl, rfl⟩ := backward _ _ _ _ operation
      exact ⟨(Unique.Framed.Configuration.running next rest).collect,
        .local (before := ⟨objects, variables, nextId⟩) originalStep,
        (embed_collect instruction (.running next rest)).symm⟩
    | exit =>
      have sameId := congrArg Shared.Framed.Configuration.nextId equality
      have sameCode := congrArg (fun c => c.frame.map Shared.Framed.Frame.code) equality
      simp only [Shared.Framed.Configuration.running, Option.map_some, Option.some.injEq,
        List.map_eq_nil_iff] at sameCode
      subst code
      refine ⟨_, Unique.Framed.exit_step ⟨objects, variables, nextId⟩, ?_⟩
      rw [Shared.Framed.collect_popped]
      simpa [embed, Unique.Framed.Configuration.terminal, Unique.Framed.Configuration.state,
        Shared.Framed.Configuration.terminal, Shared.Framed.Configuration.running, embedState] using
        congrArg (fun n => Shared.Framed.Configuration.terminal (Instruction := J) n) sameId.symm

theorem base_step_correspondence :
    Shared.Framed.Step (Shared.Framed.baseOperation (embedClasses classes))
      (embed embedStatement before) after ↔
    ∃ successor, Unique.Framed.Step (Unique.Framed.baseOperation classes) before successor ∧
      after = embed embedStatement successor := by
  constructor
  · apply step_backward embedStatement
    intro state code next rest step
    obtain ⟨successor, original, same⟩ := Dada.Correspondence.step_backward (before := ⟨state, code⟩) (after := ⟨next, rest⟩) step
    have states := congrArg Shared.Configuration.state same
    exact ⟨successor.state, successor.code, original, states, by simpa [Dada.Correspondence.embedConfiguration] using congrArg (fun c => c.code) same⟩
  · rintro ⟨successor, step, rfl⟩
    exact step_forward embedStatement (fun state code after rest step => Dada.Correspondence.step_forward
      (before := ⟨state, code⟩) (after := ⟨after, rest⟩) step) step

theorem pattern_step_correspondence :
    Shared.Framed.Step (Shared.Framed.patternOperation (embedClasses classes))
      (embed Unpacking.embedStatement before) after ↔
    ∃ successor, Unique.Framed.Step (Unique.Framed.patternOperation classes) before successor ∧
      after = embed Unpacking.embedStatement successor := by
  constructor
  · apply step_backward Unpacking.embedStatement
    intro state code next rest step
    obtain ⟨successor, original, same⟩ := Unpacking.step_backward (before := ⟨state, code⟩) (after := ⟨next, rest⟩) step
    exact ⟨successor.state, successor.code, original, congrArg Shared.Unpacking.Configuration.state same,
      by simpa [Unpacking.embedConfiguration] using congrArg Shared.Unpacking.Configuration.code same⟩
  · rintro ⟨successor, step, rfl⟩
    exact step_forward Unpacking.embedStatement (fun state code after rest step => Unpacking.step_forward
      (before := ⟨state, code⟩) (after := ⟨after, rest⟩) step) step

theorem finished_correspondence (instruction : I → J) (configuration : Unique.Framed.Configuration I) :
    (embed instruction configuration).finished ↔ configuration.finished := by
  simp [embed, Shared.Framed.Configuration.finished, Unique.Framed.Configuration.finished]

theorem initial_correspondence (instruction : I → J) (code : List I) :
    embed instruction (.initial code) = .initial (code.map instruction) := rfl

theorem base_stuck_correspondence :
    Shared.Framed.Stuck (Shared.Framed.baseOperation (embedClasses classes)) (embed embedStatement configuration) ↔
    Unique.Framed.Stuck (Unique.Framed.baseOperation classes) configuration := by
  simp only [Shared.Framed.Stuck, Unique.Framed.Stuck, finished_correspondence]
  constructor
  · rintro ⟨unfinished, noStep⟩
    refine ⟨unfinished, ?_⟩
    rintro ⟨after, step⟩
    exact noStep ⟨_, base_step_correspondence.mpr ⟨after, step, rfl⟩⟩
  · rintro ⟨unfinished, noStep⟩
    refine ⟨unfinished, ?_⟩
    rintro ⟨after, step⟩
    obtain ⟨successor, original, _⟩ := base_step_correspondence.mp step
    exact noStep ⟨successor, original⟩

theorem base_boundary_correspondence (classes : Unique.Classes)
    (code : List Unique.Statement) (configuration : Unique.Framed.Configuration Unique.Statement) :
    embed embedStatement (.initial code) = .initial (code.map embedStatement) ∧
    ((embed embedStatement configuration).finished ↔ configuration.finished) ∧
    (Shared.Framed.Stuck (Shared.Framed.baseOperation (embedClasses classes)) (embed embedStatement configuration) ↔
      Unique.Framed.Stuck (Unique.Framed.baseOperation classes) configuration) :=
  ⟨initial_correspondence _ _, finished_correspondence _ _, base_stuck_correspondence⟩

theorem base_trace_correspondence
    (steps : Shared.Framed.StepsExactly (Shared.Framed.baseOperation (embedClasses classes)) start count after) :
    ∀ before, start = embed embedStatement before →
      ∃ successor, Unique.Framed.StepsExactly (Unique.Framed.baseOperation classes) before count successor ∧
        after = embed embedStatement successor := by
  induction steps with
  | refl => intro before equality; exact ⟨before, .refl _, equality⟩
  | step first _ ih =>
    intro before equality
    subst equality
    obtain ⟨middle, original, rfl⟩ := base_step_correspondence.mp first
    obtain ⟨last, rest, equality⟩ := ih middle rfl
    exact ⟨last, .step original rest, equality⟩

end Dada.Correspondence.Framed
