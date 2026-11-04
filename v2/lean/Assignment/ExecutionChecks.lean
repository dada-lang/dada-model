import Assignment.Checks

namespace Dada.Assignment.Checks
open Shared

def beforeRefill : State :=
  ⟨[(⟨1⟩, ⟨"Wrapper", [("resource", none)]⟩)], [("w", some (.owned ⟨1⟩))], 2⟩

def afterRefill : State :=
  ⟨[(⟨2⟩, ⟨"Resource", []⟩), (⟨1⟩, ⟨"Wrapper", [("resource", some (.owned ⟨2⟩))]⟩)],
    [("w", some (.owned ⟨1⟩))], 3⟩

theorem refill_raw : RawStep classes.erase []
    (.running beforeRefill ⟨[.store (.field (.variable "w") "resource") (.new "Resource" [])], none⟩)
    (.running afterRefill ⟨[], none⟩) := by
  apply RawStep.store
    (evaluated := beforeRefill.allocate "Resource" [] [])
    (reference := .owned ⟨2⟩) (target := .field ⟨1⟩ "resource") (previous := none)
  · exact .new (declaration := ⟨[], .classType⟩) (by decide) (.nil _) rfl (by decide) (by simp [StructArguments])
  · exact .field (data := ⟨"Wrapper", [("resource", none)]⟩) (.variable (reference := .owned ⟨1⟩) (by decide)) (by decide) (by decide)
  · trivial
  · exact .field _ _ [(⟨2⟩, ⟨"Resource", []⟩)] [] ⟨1⟩ "Wrapper" [] [] "resource" none (.owned ⟨2⟩)

-- ANCHOR: younger_child
example :
    Step classes.erase []
      (.running beforeRefill ⟨[.store (.field (.variable "w") "resource") (.new "Resource" [])], none⟩)
      (.running afterRefill ⟨[], none⟩) ∧
    Shared.WellFormed classes.erase afterRefill ∧
    ¬ (∀ id data name reference, (id, data) ∈ afterRefill.objects →
      (name, some reference) ∈ data.fields → reference.object.index < id.index) := by
  refine ⟨?_, ?_, ?_⟩
  · have collected : (Configuration.running afterRefill ⟨[], none⟩).collect =
        Configuration.running afterRefill ⟨[], none⟩ := by
      apply Configuration.collect_eq_self
      intro id data member
      simp only [Configuration.running, afterRefill, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with h | h
      · cases h
        exact .field (parent := ⟨1⟩) (reference := .owned ⟨2⟩) (name := "resource") (data := ⟨"Wrapper", [("resource", some (.owned ⟨2⟩))]⟩) (.variable (name := "w") (reference := .owned ⟨1⟩) (by decide)) (by decide) (by decide)
      · cases h
        exact .variable (name := "w") (reference := .owned ⟨1⟩) (by decide)
    rw [← collected]
    exact .collect refill_raw
  · refine ⟨by decide, by decide, ?_, ?_, ?_, ?_, ?_⟩
    · intro id data member
      simp only [afterRefill, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with h | h <;> cases h
      · exact ⟨⟨[], .classType⟩, by decide, rfl, by decide⟩
      · exact ⟨⟨["resource"], .classType⟩, by decide, rfl, by decide⟩
    · intro id data member
      simp only [afterRefill, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with h | h <;> cases h <;> decide
    · intro object allocated
      have cases : object = ⟨2⟩ ∨ object = ⟨1⟩ := by simpa [Allocated, afterRefill] using allocated
      rcases cases with rfl | rfl
      · exact .field (parent := ⟨1⟩) (reference := .owned ⟨2⟩) (name := "resource")
          (data := ⟨"Wrapper", [("resource", some (.owned ⟨2⟩))]⟩)
          (.variable (name := "w") (reference := .owned ⟨1⟩) (by decide)) (by decide) (by decide)
      · exact .variable (name := "w") (reference := .owned ⟨1⟩) (by decide)
    · simp [Owners, afterRefill, Compatible, Reference.owned]
    · intro object
      simp [References, Allocated, afterRefill, Reference.owned, or_comm]
  · intro older
    have impossible := older ⟨1⟩ ⟨"Wrapper", [("resource", some (.owned ⟨2⟩))]⟩ "resource" (.owned ⟨2⟩) (by decide) (by decide)
    contradiction
-- ANCHOR_END: younger_child

def beforeStructStore : State :=
  ⟨[(⟨0⟩, ⟨"SharedPoint", []⟩)], [("s", some (.shared ⟨0⟩))], 1⟩

def afterStructStore : State :=
  ⟨[(⟨1⟩, ⟨"SharedPoint", []⟩), (⟨0⟩, ⟨"SharedPoint", []⟩)],
    [("s", some (.shared ⟨1⟩))], 2⟩

-- ANCHOR: struct_collection
example :
    RawStep classes.erase []
      (.running beforeStructStore ⟨[.store (.variable "s") (.new "SharedPoint" [])], none⟩)
      (.running afterStructStore ⟨[], none⟩) ∧
    ¬ Live (Configuration.running afterStructStore ⟨[], none⟩).rootState ⟨0⟩ ∧
    Live (Configuration.running afterStructStore ⟨[], none⟩).rootState ⟨1⟩ := by
  refine ⟨?_, ?_, .variable (name := "s") (reference := .shared ⟨1⟩) (by decide)⟩
  · apply RawStep.store (evaluated := beforeStructStore.allocate "SharedPoint" [] [])
      (reference := .shared ⟨1⟩) (target := .variable "s") (previous := some (.shared ⟨0⟩))
    · exact .new (declaration := ⟨[], .sharedStruct⟩) (by decide) (.nil _) rfl (by decide)
        (by simp [StructArguments])
    · exact .variable (by decide)
    · exact ⟨⟨"SharedPoint", []⟩, ⟨[], .sharedStruct⟩, by decide, by decide, rfl⟩
    · exact .variable _ _ [] [] "s" _ _
  · have onlyOne : ∀ id, Live (Configuration.running afterStructStore ⟨[], none⟩).rootState id → id = ⟨1⟩ := by
      intro id live
      induction live with
      | «variable» member =>
        simp only [Configuration.rootState, Configuration.running, afterStructStore,
          List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
          List.not_mem_nil, or_false, Prod.mk.injEq, Option.some.injEq] at member
        rw [member.2]
        rfl
      | field _ obj field _ =>
        simp only [Configuration.rootState, Configuration.running, afterStructStore,
          List.mem_cons, List.not_mem_nil, or_false] at obj
        rcases obj with h | h <;> cases h <;> contradiction
    intro live
    have impossible := onlyOne _ live
    cases impossible
-- ANCHOR_END: struct_collection

end Dada.Assignment.Checks
