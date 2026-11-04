import Shared.Frames
import Shared.KindSafety

namespace Dada.Shared.Framed

theorem terminal_kindCorrect (classes : Classes) (nextId : Nat) :
    KindCorrect classes (Configuration.terminal (Instruction := Statement) nextId).state [] := by
  constructor <;> simp [Configuration.terminal, Configuration.state, Owners]

theorem base_kind_preservation (classesWf : ClassesWellFormed classes)
    (wf : WellFormedState classes before.state)
    (step : Step (baseOperation classes) before after) : WellFormedState classes after.state := by
  cases step with
  | «local» operation =>
    have next := operation.preserves_wellFormed classesWf wf.1
    rw [collect_running next]
    exact ⟨next, operation.preserves_kinds classesWf wf.1 wf.2⟩
  | exit =>
    rw [collect_popped]
    exact ⟨terminal_wellFormed _ _, terminal_kindCorrect _ _⟩

theorem base_soundness (classesWf : ClassesWellFormed classes)
    (trace : StepsExactly (baseOperation classes) (.initial code) count after) :
    WellFormedState classes after.state := by
  have preserve : ∀ start n finish, WellFormedState classes start.state →
      StepsExactly (baseOperation classes) start n finish → WellFormedState classes finish.state := by
    intro start n finish wf execution
    induction execution with
    | refl => exact wf
    | step next _ rest => exact rest (base_kind_preservation classesWf wf next)
  exact preserve _ _ _ ⟨WellFormed.empty _, KindCorrect.empty _⟩ trace

end Dada.Shared.Framed
