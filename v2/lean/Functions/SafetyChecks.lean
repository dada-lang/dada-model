import Functions.Safety
import Functions.Checks

namespace Dada.Functions.Checks

-- ANCHOR: nested_safety
example :
    (∀ configuration, Steps classes.erase nestedTable (.initial nestedProgram) configuration →
      ConfigurationTyped classes nestedTable configuration ∧ ¬ Stuck classes.erase nestedTable configuration) ∧
    ConfigurationTyped classes nestedTable nestedReturned ∧
    ConfigurationTyped classes nestedTable ⟨[],1,[]⟩ := by
  refine ⟨fun configuration trace => ?_, ?_, ?_⟩
  · have safe := program_safety nested_typed trace
    exact ⟨safe.1,safe.2.2⟩
  · exact (program_safety nested_typed nested_execution).1
  · have exit : RawStep classes.erase nestedTable nestedReturned ⟨nestedReturned.objects,1,[]⟩ := .exit
    have collected := Step.collect exit
    simp only [Configuration.collect_empty_frames] at collected
    exact (program_safety nested_typed nested_execution).1.preservation collected
-- ANCHOR_END: nested_safety

private theorem recursion_typed : ProgramTyped recursionProgram := by
  have statement : StatementTyped classes recursionTable [] (.call none (.function "recur") []) [] :=
    .call (declaration := recur) (by simp [recursionTable]) (by simp)
      (.nil (by decide)) (.none (by decide))
  refine ⟨by decide, ⟨by decide, ?_⟩, [], .cons statement (.nil (by decide))⟩
  intro entry member
  have : entry = (.function "recur", recur) := by simpa [recursionProgram,recursionTable] using member
  subst entry
  exact ⟨by decide, [], [], .cons statement (.nil (by decide)), .none (by decide)⟩

-- ANCHOR: recursion_safety
example : ∀ depth,
    ConfigurationTyped classes recursionTable (recursionState depth) ∧
    ¬ Stuck classes.erase recursionTable (recursionState depth) ∧
    Step classes.erase recursionTable (recursionState depth) (recursionState (depth+1)) := by
  intro depth
  have safe := program_safety recursion_typed (recursion_reachable depth)
  exact ⟨safe.1,safe.2.2,recursive_step depth⟩
-- ANCHOR_END: recursion_safety

end Dada.Functions.Checks
