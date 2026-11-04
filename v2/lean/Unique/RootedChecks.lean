import Unique.TypingSafety

namespace Dada.Unique.RootedChecks

def classes : Classes := [("Token", ⟨[]⟩), ("Box", ⟨["value"]⟩)]
def youngerChild : State :=
  ⟨[(1, ⟨"Box", [("value", some 2)]⟩), (2, ⟨"Token", []⟩)], [("b", some 1)], 3⟩
def takenChild : State :=
  ⟨[(1, ⟨"Box", [("value", none)]⟩), (2, ⟨"Token", []⟩)], [("b", some 1)], 3⟩

theorem youngerChild_wellFormed : WellFormed classes youngerChild := by
  constructor
  · decide
  · decide
  · intro id data member
    simp only [youngerChild, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h <;> cases h
    · exact ⟨⟨["value"]⟩, by decide, rfl, by decide⟩
    · exact ⟨⟨[]⟩, by decide, rfl, by decide⟩
  · intro id data member
    simp only [youngerChild, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h <;> cases h <;> decide
  · intro id allocated
    have member : id = 1 ∨ id = 2 := by simpa [Allocated, youngerChild] using allocated
    rcases member with rfl | rfl
    · exact .variable (name := "b") (by decide)
    · exact .field (parent := 1) (name := "value") (data := ⟨"Box", [("value", some 2)]⟩)
        (.variable (name := "b") (by decide)) (by decide) (by decide)
  · decide
  · intro id
    simp [References, Allocated, youngerChild]

theorem take_younger : Take youngerChild (.field 1 "value") 2 takenChild :=
  .field [("b", some 1)] 3 [] [(2, ⟨"Token", []⟩)] 1 "Box" [] [] "value" 2

-- ANCHOR: younger_child
example : WellFormed classes youngerChild ∧
    ¬ ((2 : ObjectId).index < (1 : ObjectId).index) ∧
    WellFormedWith classes takenChild [2] := by
  exact ⟨youngerChild_wellFormed, by decide, take_younger.preserves_pending youngerChild_wellFormed.with_empty⟩
-- ANCHOR_END: younger_child

def unreachableCycle : State := ⟨[(1, ⟨"Box", [("value", some 1)]⟩)], [], 2⟩

-- ANCHOR: unreachable_cycle
example : ¬ WellFormed classes unreachableCycle := by
  intro wf
  have noLive : ∀ id, ¬ Live unreachableCycle id := by
    intro id live
    induction live with
    | «variable» member => exact List.not_mem_nil member
    | field _ _ _ ih => exact ih
  exact noLive 1 (wf.rooted 1 (by simp [Allocated, unreachableCycle]))
-- ANCHOR_END: unreachable_cycle

end Dada.Unique.RootedChecks
