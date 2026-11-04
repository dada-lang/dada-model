import Unique.Frames
import Unique.FrameSafety

namespace Dada.Unique.Framed.Checks

def classes : Classes := [("Token", ⟨[]⟩)]
def code : List Statement := [⟨"t", .new "Token" []⟩]
def observed : State := ⟨[(0, ⟨"Token", []⟩)], [("t", some 0)], 1⟩

theorem allocated : Dada.Unique.Step classes ⟨State.empty, code⟩ ⟨observed, []⟩ :=
  .letValue (by decide) (.new (declaration := ⟨[]⟩) (objects := [])
    (by decide) (.nil _) rfl (by decide))

theorem observed_wellFormed : WellFormed classes observed :=
  allocated.preserves_wellFormed (by simp [ClassesWellFormed, classes]) (WellFormed.empty _)

-- ANCHOR: lifetime
example :
    Step (baseOperation classes) (.initial []) (Configuration.terminal (Instruction := Statement) 0) ∧
    Step (baseOperation classes) (.initial code) (.running observed []) ∧
    ("t", some 0) ∈ observed.variables ∧
    ¬ (Configuration.running observed ([] : List Statement)).finished ∧
    StepsExactly (baseOperation classes) (.initial code) 2 (.terminal 1) ∧
    (Configuration.terminal (Instruction := Statement) 1).finished := by
  refine ⟨exit_step State.empty, local_step allocated observed_wellFormed, by decide,
    by simp [Configuration.running, Configuration.finished], ?_, rfl⟩
  exact .step (local_step allocated observed_wellFormed) (.step (exit_step observed) (.refl _))
-- ANCHOR_END: lifetime

end Dada.Unique.Framed.Checks
