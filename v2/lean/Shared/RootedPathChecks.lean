import Shared.TypingGiveSoundness

namespace Dada.Shared.RootedPathChecks
open Typing

-- These states test the widened invariant; the present constructor-only
-- language cannot construct the cycle from an empty state.
def classes : ClassTable :=
  [("A", ⟨[("f", ⟨.given, "B"⟩)], .structType⟩),
   ("B", ⟨[("g", ⟨.shared, "A"⟩)], .structType⟩)]

def cyclic : State :=
  ⟨[(⟨0⟩, ⟨"A", [("f", some (.owned ⟨1⟩))]⟩),
    (⟨1⟩, ⟨"B", [("g", some (.shared ⟨0⟩))]⟩)],
    [("a", some (.shared ⟨0⟩))], 2⟩

theorem cyclic_wellFormed : WellFormed classes.erase cyclic := by
  refine ⟨by decide, by decide, ?_, ?_, ?_, by simp [Owners, Compatible, cyclic, Reference.owned, Reference.shared], ?_⟩
  · intro id data member
    simp only [cyclic, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h <;> cases h
    · exact ⟨⟨["f"], .structType⟩, by decide, rfl, by decide⟩
    · exact ⟨⟨["g"], .structType⟩, by decide, rfl, by decide⟩
  · intro id data member
    simp only [cyclic, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h <;> cases h <;> decide
  · intro id allocated
    simp only [Allocated, cyclic, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at allocated
    rcases allocated with rfl | rfl
    · exact .variable (name := "a") (reference := .shared ⟨0⟩) (by decide)
    · exact .field (parent := ⟨0⟩) (data := ⟨"A", [("f", some (.owned ⟨1⟩))]⟩)
        (name := "f") (reference := .owned ⟨1⟩)
        (.variable (name := "a") (reference := .shared ⟨0⟩) (by decide)) (by decide) (by decide)
  · intro id
    simp [References, Allocated, cyclic, Reference.owned, Reference.shared]
    constructor
    · rintro (h | h | h) <;> simp_all
    · rintro (h | h) <;> simp_all

def removed : State :=
  ⟨[(⟨0⟩, ⟨"A", [("f", none)]⟩),
    (⟨1⟩, ⟨"B", [("g", some (.shared ⟨0⟩))]⟩)],
    [("a", some (.shared ⟨0⟩))], 2⟩

def promoted : State :=
  ⟨[(⟨0⟩, ⟨"A", [("f", some (.shared ⟨1⟩))]⟩),
    (⟨1⟩, ⟨"B", [("g", some (.shared ⟨0⟩))]⟩)],
    [("a", some (.shared ⟨0⟩))], 2⟩

def fieldPlace : Place := .field (.variable "a") "f"

theorem resolves_shared : Resolve cyclic fieldPlace (.field ⟨0⟩ "f") ⟨1⟩ .shared :=
  .field (data := ⟨"A", [("f", some (.owned ⟨1⟩))]⟩)
    (reference := .owned ⟨1⟩)
    (.variable (name := "a") (reference := .shared ⟨0⟩) (by decide)) (by decide) (by decide)

theorem promotes : Promote cyclic (.field ⟨0⟩ "f") ⟨1⟩ promoted :=
  .field _ _ [] [(⟨1⟩, ⟨"B", [("g", some (.shared ⟨0⟩))]⟩)] ⟨0⟩ "A" [] [] "f" ⟨1⟩

-- ANCHOR: mixed_cycle
example : classes.WellFormed ∧ WellFormed classes.erase cyclic :=
  ⟨by decide, cyclic_wellFormed⟩
-- ANCHOR_END: mixed_cycle

-- Raw Take alone does not justify the old target-interior preservation lemma.
-- It cuts an edge that is unique in storage but only shared from any root.
-- ANCHOR: raw_take_changes_interior
example :
    Take cyclic (.field ⟨0⟩ "f") ⟨1⟩ removed ∧
    readPath cyclic (.owned ⟨1⟩) ["g", "f"] = some (some (.shared ⟨1⟩)) ∧
    readPath removed (.owned ⟨1⟩) ["g", "f"] = some none := by
  exact ⟨.field _ _ [] [(⟨1⟩, ⟨"B", [("g", some (.shared ⟨0⟩))]⟩)]
    ⟨0⟩ "A" [] [] "f" ⟨1⟩, by decide, by decide⟩
-- ANCHOR_END: raw_take_changes_interior

-- ANCHOR: give_preserves_shared_cycle
example :
    Give cyclic fieldPlace (.shared ⟨1⟩) promoted ∧
    (¬ ∃ source, Resolve cyclic fieldPlace source ⟨1⟩ .unique) ∧
    (∀ path, readPath promoted (.shared ⟨1⟩) path = readPath cyclic (.shared ⟨1⟩) path) := by
  have given : Give cyclic fieldPlace (.shared ⟨1⟩) promoted := .promote resolves_shared promotes
  have afterWf := given.preserves_pending cyclic_wellFormed.with_pending
  refine ⟨given, ?_, ?_⟩
  · rintro ⟨source, unique⟩
    have impossible := (resolve_deterministic cyclic_wellFormed.with_pending resolves_shared unique).2.2
    cases impossible
  · intro path
    exact promote_readPath_eq cyclic_wellFormed.with_pending afterWf promotes
      (route_of_resolve resolves_shared) (route_of_resolve resolves_shared) path
-- ANCHOR_END: give_preserves_shared_cycle

end Dada.Shared.RootedPathChecks
