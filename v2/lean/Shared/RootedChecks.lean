import Shared.Liveness

namespace Dada.Shared.RootedChecks

def classes : Classes := [("Node", ⟨["next"], .structType⟩), ("Leaf", ⟨[], .classType⟩),
  ("Parent", ⟨["child"], .classType⟩)]

def newerChild : State :=
  ⟨[(⟨0⟩, ⟨"Parent", [("child", some (.owned ⟨1⟩))]⟩), (⟨1⟩, ⟨"Leaf", []⟩)],
    [("p", some (.owned ⟨0⟩))], 2⟩

-- ANCHOR: newer_child
example : WellFormed classes newerChild := by
  refine ⟨by decide, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · intro id data member
    simp only [newerChild, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h <;> cases h
    · exact ⟨⟨["child"], .classType⟩, by decide, rfl, by decide⟩
    · exact ⟨⟨[], .classType⟩, by decide, rfl, by decide⟩
  · intro id data member
    simp only [newerChild, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h <;> cases h <;> decide
  · intro object allocated
    have cases : object = ⟨0⟩ ∨ object = ⟨1⟩ := by simpa [Allocated, newerChild] using allocated
    rcases cases with rfl | rfl
    · exact .variable (name := "p") (reference := .owned ⟨0⟩) (by decide)
    · exact .field (parent := ⟨0⟩) (name := "child") (reference := .owned ⟨1⟩)
        (.variable (name := "p") (reference := .owned ⟨0⟩) (by decide))
        (data := ⟨"Parent", [("child", some (.owned ⟨1⟩))]⟩) (by decide) (by decide)
  · simp [Owners, newerChild, Compatible, Reference.owned]
  · intro object
    simp [References, Allocated, newerChild, Reference.owned]
-- ANCHOR_END: newer_child

def sharedCycle : State :=
  ⟨[(⟨0⟩, ⟨"Node", [("next", some (.shared ⟨1⟩))]⟩),
    (⟨1⟩, ⟨"Node", [("next", some (.shared ⟨0⟩))]⟩)],
    [("root", some (.shared ⟨0⟩))], 2⟩

-- ANCHOR: shared_cycle
example : WellFormed classes sharedCycle := by
  refine ⟨by decide, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · intro id data member
    simp only [sharedCycle, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h <;> cases h
    all_goals exact ⟨⟨["next"], .structType⟩, by decide, rfl, by decide⟩
  · intro id data member
    simp only [sharedCycle, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h <;> cases h <;> decide
  · intro object allocated
    have cases : object = ⟨0⟩ ∨ object = ⟨1⟩ := by simpa [Allocated, sharedCycle] using allocated
    rcases cases with rfl | rfl
    · exact .variable (name := "root") (reference := .shared ⟨0⟩) (by decide)
    · exact .field (parent := ⟨0⟩) (name := "next") (reference := .shared ⟨1⟩)
        (.variable (name := "root") (reference := .shared ⟨0⟩) (by decide))
        (data := ⟨"Node", [("next", some (.shared ⟨1⟩))]⟩) (by decide) (by decide)
  · simp [Owners, sharedCycle, Compatible, Reference.shared]
  · intro object
    simp [References, Allocated, sharedCycle, Reference.shared, or_comm]
-- ANCHOR_END: shared_cycle

def mixedCycle : State :=
  ⟨[(⟨0⟩, ⟨"Node", [("next", some (.owned ⟨1⟩))]⟩),
    (⟨1⟩, ⟨"Node", [("next", some (.shared ⟨0⟩))]⟩)],
    [("root", some (.shared ⟨0⟩))], 2⟩

-- ANCHOR: mixed_cycle
example : WellFormed classes mixedCycle := by
  refine ⟨by decide, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · intro id data member
    simp only [mixedCycle, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h <;> cases h
    all_goals exact ⟨⟨["next"], .structType⟩, by decide, rfl, by decide⟩
  · intro id data member
    simp only [mixedCycle, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h <;> cases h <;> decide
  · intro object allocated
    have cases : object = ⟨0⟩ ∨ object = ⟨1⟩ := by simpa [Allocated, mixedCycle] using allocated
    rcases cases with rfl | rfl
    · exact .variable (name := "root") (reference := .shared ⟨0⟩) (by decide)
    · exact .field (parent := ⟨0⟩) (name := "next") (reference := .owned ⟨1⟩)
        (.variable (name := "root") (reference := .shared ⟨0⟩) (by decide))
        (data := ⟨"Node", [("next", some (.owned ⟨1⟩))]⟩) (by decide) (by decide)
  · simp [Owners, mixedCycle, Compatible, Reference.shared, Reference.owned]
  · intro object
    simp [References, Allocated, mixedCycle, Reference.shared, Reference.owned, or_comm]
-- ANCHOR_END: mixed_cycle

-- ANCHOR: unrooted_cycle
example : ¬ WellFormed classes { sharedCycle with variables := [] } := by
  intro wf
  have noLive : ∀ object, ¬ Live { sharedCycle with variables := [] } object := by
    intro object live
    induction live with
    | «variable» member => simp at member
    | field _ _ _ ih => exact ih
  exact noLive ⟨0⟩ (wf.rooted ⟨0⟩ (by simp [Allocated, sharedCycle]))
-- ANCHOR_END: unrooted_cycle

end Dada.Shared.RootedChecks
