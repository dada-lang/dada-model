import Shared.TypedConfigurations
import Shared.TypingGiveSoundness
import Shared.TypingBindingSoundness

namespace Dada.Shared.Typing

section FromExpressionSoundness

variable {classes : ClassTable}
variable (expressionSound : ∀ before value ty after,
  ExprTyped classes before value ty after → ExpressionSound classes before value ty after)

include expressionSound

theorem ConfigurationTyped.progress_of_expression
    (typed : ConfigurationTyped classes configuration finalEnvironment) :
    configuration.finished ∨ ∃ after, Unpacking.Step classes.erase configuration after := by
  obtain ⟨current, realized, sequence⟩ := typed
  rcases configuration with ⟨state, code⟩
  cases code with
  | nil => exact Or.inl rfl
  | cons statement rest =>
    cases sequence with
    | cons first remaining =>
      cases first with
      | letValue expression binding =>
        have sound := expressionSound _ _ _ _ expression state [] realized
        obtain ⟨evaluated, object, evaluation⟩ := sound.1
        have current := sound.2 evaluated object evaluation
        obtain ⟨after, operation⟩ := binding.exists_bind current
        exact Or.inr ⟨⟨after, rest⟩, .letValue evaluation operation⟩

theorem ConfigurationTyped.preservation_of_expression
    (typed : ConfigurationTyped classes before finalEnvironment)
    (step : Unpacking.Step classes.erase before after) :
    ConfigurationTyped classes after finalEnvironment := by
  obtain ⟨current, realized, sequence⟩ := typed
  cases step with
  | letValue evaluation operation =>
    cases sequence with
    | cons first rest =>
      cases first with
      | letValue expression binding =>
        have evaluated := (expressionSound _ _ _ _ expression _ [] realized).2 _ _ evaluation
        exact ⟨_, binding.preserves_realization evaluated operation, rest⟩

theorem ConfigurationTyped.trace_of_expression
    (typed : ConfigurationTyped classes before finalEnvironment)
    (trace : Unpacking.Steps classes.erase before after) :
    ConfigurationTyped classes after finalEnvironment := by
  induction trace with
  | refl => exact typed
  | step first _ rest =>
    exact rest (typed.preservation_of_expression expressionSound first)

theorem ConfigurationTyped.finishes_of_expression
    (typed : ConfigurationTyped classes configuration finalEnvironment) :
    ∃ final, Unpacking.StepsExactly classes.erase configuration configuration.code.length final ∧
      final.finished ∧ Realizes classes finalEnvironment final.state [] := by
  have decreasing : ∀ (count : Nat) (configuration : Unpacking.Configuration), configuration.code.length = count →
      ConfigurationTyped classes configuration finalEnvironment →
      ∃ final, Unpacking.StepsExactly classes.erase configuration count final ∧
        final.finished ∧ Realizes classes finalEnvironment final.state [] := by
    intro count
    induction count with
    | zero =>
      intro configuration empty typed
      have finished : configuration.finished := List.length_eq_zero_iff.mp empty
      exact ⟨configuration, .refl _, finished, typed.finished finished⟩
    | succ count ih =>
      intro configuration length typed
      rcases typed.progress_of_expression expressionSound with finished | ⟨after, step⟩
      · have empty : configuration.code = [] := finished
        simp [empty] at length
      · have shorter := step.code_length
        have nextLength : after.code.length = count := by omega
        obtain ⟨final, rest, finished, realized⟩ := ih after nextLength
          (typed.preservation_of_expression expressionSound step)
        exact ⟨final, .step step rest, finished, realized⟩
  exact decreasing _ configuration rfl typed

end FromExpressionSoundness

-- The public results discharge the expression premise with the proved static
-- soundness theorem; no operational-success assumption appears here.
theorem expression_soundness
    (typed : ExprTyped classes before value ty after)
    (realized : Realizes classes before state pending) :
    (∃ result object, Eval classes.erase state value result object) ∧
    (∀ result object, Eval classes.erase state value result object →
      Realizes classes after result (pending ++ [(object, ty)])) := by
  have sound := typed.sound state pending realized
  refine ⟨sound.1, fun result object evaluated => ?_⟩
  exact (sound.2 result object evaluated).perm (by simpa using (List.perm_middle (a := (object, ty)) (l₁ := pending) (l₂ := [])).symm)

theorem ConfigurationTyped.progress
    (typed : ConfigurationTyped classes configuration finalEnvironment) :
    configuration.finished ∨ ∃ after, Unpacking.Step classes.erase configuration after :=
  typed.progress_of_expression (fun _ _ _ _ expression => expression.sound)

theorem ConfigurationTyped.preservation
    (typed : ConfigurationTyped classes before finalEnvironment)
    (step : Unpacking.Step classes.erase before after) :
    ConfigurationTyped classes after finalEnvironment :=
  typed.preservation_of_expression (fun _ _ _ _ expression => expression.sound) step

theorem ConfigurationTyped.trace
    (typed : ConfigurationTyped classes before finalEnvironment)
    (steps : Unpacking.Steps classes.erase before after) :
    ConfigurationTyped classes after finalEnvironment :=
  typed.trace_of_expression (fun _ _ _ _ expression => expression.sound) steps

theorem ConfigurationTyped.finishes
    (typed : ConfigurationTyped classes configuration finalEnvironment) :
    ∃ final, Unpacking.StepsExactly classes.erase configuration configuration.code.length final ∧
      final.finished ∧ Realizes classes finalEnvironment final.state [] :=
  typed.finishes_of_expression (fun _ _ _ _ expression => expression.sound)

-- Every finite execution prefix remains safe and can be completed. The counted
-- continuation gives exactly one transition per original statement overall.
theorem program_safety (classesWf : classes.WellFormed)
    (typed : SequenceTyped classes [] code finalEnvironment)
    (execution : Unpacking.Steps classes.erase ⟨State.empty, code⟩ configuration) :
    ¬ Unpacking.Stuck classes.erase configuration ∧
    (configuration.finished ∨ ∃ next, Unpacking.Step classes.erase configuration next) ∧
    ∃ final prefixLength,
      Unpacking.StepsExactly classes.erase ⟨State.empty, code⟩ prefixLength configuration ∧
      Unpacking.StepsExactly classes.erase configuration configuration.code.length final ∧
      prefixLength + configuration.code.length = code.length ∧
      Unpacking.StepsExactly classes.erase ⟨State.empty, code⟩ code.length final ∧
      final.finished ∧ Realizes classes finalEnvironment final.state [] := by
  have initial : ConfigurationTyped classes ⟨State.empty, code⟩ finalEnvironment :=
    ⟨[], Realizes.empty classesWf, typed⟩
  have current := initial.trace execution
  have progress := current.progress
  refine ⟨?_, progress, ?_⟩
  · intro stuck
    rcases progress with finished | next
    · exact stuck.1 finished
    · exact stuck.2 next
  · obtain ⟨final, completion, finished, realized⟩ := current.finishes
    obtain ⟨count, counted⟩ := execution.counted
    have length : count + configuration.code.length = code.length := counted.length.symm
    exact ⟨final, count, counted, completion, length,
      length ▸ counted.trans completion, finished, realized⟩

end Dada.Shared.Typing
