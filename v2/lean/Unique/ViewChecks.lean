import Unique.Views

namespace Dada.Unique.Typing

def viewClasses : ClassTable :=
  [("Token", ⟨[]⟩),
   ("Pair", ⟨[("left", "Token"), ("right", "Token")]⟩),
   ("Box", ⟨[("item", "Pair")]⟩),
   ("Baz", ⟨[]⟩), ("Bar", ⟨[("baz", "Baz")]⟩), ("Foo", ⟨[("bar", "Bar")]⟩)]

theorem viewClasses_wellFormed : viewClasses.WellFormed := by decide

private theorem pair_path_cases {path : Path} {name : ClassName}
 (h : classAt viewClasses "Pair" path = some name) :
 (path = [] ∧ name = "Pair") ∨
 (path = ["left"] ∧ name = "Token") ∨
 (path = ["right"] ∧ name = "Token") := by
 cases path with
 | nil => simp [classAt] at h; simp [h]
 | cons f rest =>
   by_cases left : f = "left"
   · subst f
     cases rest with
     | nil => simp [classAt, viewClasses, List.lookup] at h; simp [h]
     | cons g tail => simp [classAt, viewClasses, List.lookup] at h
   · by_cases right : f = "right"
     · subst f
       cases rest with
       | nil => simp [classAt, viewClasses, List.lookup] at h; simp [h]
       | cons g tail => simp [classAt, viewClasses, List.lookup] at h
     · have leftb : (f == "left") = false := by simp [left]
       have rightb : (f == "right") = false := by simp [right]
       simp [classAt, viewClasses, List.lookup, leftb, rightb] at h

private theorem pair_view_full (ty : ViewType) (base : ty.className = "Pair")
 (left : Pos viewClasses ty ["left"] ∨ Neg ty ["left"])
 (right : Pos viewClasses ty ["right"] ∨ Neg ty ["right"]) : Full viewClasses ty := by
 intro path _ name declaration atPath atClass field member
 have casesPath :
   (path = [] ∧ name = "Pair") ∨
   (path = ["left"] ∧ name = "Token") ∨
   (path = ["right"] ∧ name = "Token") := by
   exact pair_path_cases (by simpa [base] using atPath)
 rcases casesPath with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
 · have hd : declaration = ⟨[("left", "Token"), ("right", "Token")]⟩ :=
     (Option.some.inj atClass).symm
   subst declaration
   simp only [List.mem_cons, List.not_mem_nil, or_false] at member
   rcases member with rfl | rfl
   · exact left
   · exact right
 · have hd : declaration = ⟨[]⟩ := (Option.some.inj atClass).symm
   subst declaration
   exact False.elim (List.not_mem_nil member)
 · have hd : declaration = ⟨[]⟩ := (Option.some.inj atClass).symm
   subst declaration
   exact False.elim (List.not_mem_nil member)

private theorem box_path_cases {path : Path} {name : ClassName}
 (h : classAt viewClasses "Box" path = some name) :
 (path = [] ∧ name = "Box") ∨
 (path = ["item"] ∧ name = "Pair") ∨
 (path = ["item", "left"] ∧ name = "Token") ∨
 (path = ["item", "right"] ∧ name = "Token") := by
 cases path with
 | nil => simp [classAt] at h; simp [h]
 | cons f rest =>
   by_cases item : f = "item"
   · subst f
     change classAt viewClasses "Pair" rest = some name at h
     rcases pair_path_cases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp
   · have itemb : (f == "item") = false := by simp [item]
     simp [classAt, viewClasses, List.lookup, itemb] at h

private theorem box_hole_full : Full viewClasses
    ⟨"Box", [.negative ["item", "left"], .positive ["item", "right"]]⟩ := by
 intro path _ name declaration atPath atClass field member
 rcases box_path_cases atPath with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
 · have hd : declaration = ⟨[("item", "Pair")]⟩ := (Option.some.inj atClass).symm
   subst declaration
   have hf : field = ("item", "Pair") := by simpa using member
   subst field
   decide
 · have hd : declaration = ⟨[("left", "Token"), ("right", "Token")]⟩ :=
     (Option.some.inj atClass).symm
   subst declaration
   simp only [List.mem_cons, List.not_mem_nil, or_false] at member
   rcases member with rfl | rfl <;> decide
 · have hd : declaration = ⟨[]⟩ := (Option.some.inj atClass).symm
   subst declaration
   exact False.elim (List.not_mem_nil member)
 · have hd : declaration = ⟨[]⟩ := (Option.some.inj atClass).symm
   subst declaration
   exact False.elim (List.not_mem_nil member)

private theorem view_fullness :
    Full viewClasses (.whole "Pair") ∧
    ¬ Full viewClasses ⟨"Pair", [.positive ["left"]]⟩ ∧
    Full viewClasses ⟨"Pair", [.negative ["left"], .positive ["right"]]⟩ ∧
    ¬ Full viewClasses ⟨"Box", [.negative ["item", "left"]]⟩ ∧
    Full viewClasses ⟨"Box", [.negative ["item", "left"], .positive ["item", "right"]]⟩ := by
 refine ⟨pair_view_full _ rfl (by decide) (by decide), ?_,
   pair_view_full _ rfl (by decide) (by decide), ?_, box_hole_full⟩
 · intro full
   have status := full [] (by decide) "Pair"
     ⟨[("left", "Token"), ("right", "Token")]⟩ rfl rfl ("right", "Token") (by simp)
   have absent : ¬ (Pos viewClasses ⟨"Pair", [.positive ["left"]]⟩ ["right"] ∨
       Neg ⟨"Pair", [.positive ["left"]]⟩ ["right"]) := by decide
   exact absent status
 · intro full
   have status := full ["item"] (by decide) "Pair"
     ⟨[("left", "Token"), ("right", "Token")]⟩ rfl rfl ("right", "Token") (by simp)
   have absent : ¬ (Pos viewClasses ⟨"Box", [.negative ["item", "left"]]⟩ ["item", "right"] ∨
       Neg ⟨"Box", [.negative ["item", "left"]]⟩ ["item", "right"]) := by decide
   exact absent status

-- ANCHOR: view_information
example :
    (Pos viewClasses ⟨"Pair", [.positive ["left"]]⟩ ["left"] ∧
    ¬ Pos viewClasses ⟨"Pair", [.positive ["left"]]⟩ ["right"] ∧
    ¬ Neg ⟨"Pair", [.positive ["left"]]⟩ ["right"] ∧
    Pos viewClasses ⟨"Box", [.negative ["item", "left"]]⟩ ["item"] ∧
    Neg ⟨"Box", [.negative ["item", "left"]]⟩ ["item", "left"] ∧
    ¬ Pos viewClasses ⟨"Box", [.negative ["item", "left"]]⟩ ["item", "right"]) ∧
    (Full viewClasses (.whole "Pair") ∧
    ¬ Full viewClasses ⟨"Pair", [.positive ["left"]]⟩ ∧
    Full viewClasses ⟨"Pair", [.negative ["left"], .positive ["right"]]⟩ ∧
    ¬ Full viewClasses ⟨"Box", [.negative ["item", "left"]]⟩ ∧
    Full viewClasses ⟨"Box", [.negative ["item", "left"], .positive ["item", "right"]]⟩) := by
  exact ⟨by decide, view_fullness⟩
-- ANCHOR_END: view_information

-- ANCHOR: normalize_nested_whole
example :
    normalize viewClasses ⟨"Foo", [.positive ["bar", "baz"]]⟩ = .whole "Foo" ∧
    normalize viewClasses ⟨"Foo", [.positive ["bar"]]⟩ = .whole "Foo" := by
  decide
-- ANCHOR_END: normalize_nested_whole

-- ANCHOR: normalization_boundaries
example :
    normalize viewClasses ⟨"Pair", [.positive ["left"]]⟩ =
      ⟨"Pair", [.positive ["left"]]⟩ ∧
    normalize viewClasses ⟨"Pair", [.negative ["left"], .positive ["right"]]⟩ =
      ⟨"Pair", [.negative ["left"], .positive ["right"]]⟩ ∧
    normalize viewClasses ⟨"Token", []⟩ = .whole "Token" ∧
    normalize viewClasses ⟨"Pair", []⟩ = ⟨"Pair", []⟩ := by
  decide
-- ANCHOR_END: normalization_boundaries

-- Source entries form a set: their input order does not change the normal form.
-- ANCHOR: normalization_entry_order
example :
    normalize viewClasses ⟨"Pair", [.positive ["right"], .negative ["left"]]⟩ =
      normalize viewClasses ⟨"Pair", [.negative ["left"], .positive ["right"]]⟩ ∧
    normalize viewClasses ⟨"Pair", [.positive ["right"], .positive ["left"]]⟩ =
      .whole "Pair" := by
  decide
-- ANCHOR_END: normalization_entry_order

-- ANCHOR: invalid_views
example :
    ¬ (⟨"Box", [.positive ["item"], .negative ["item", "left"]]⟩ : ViewType).WellFormed
      viewClasses ∧
    ¬ (⟨"Pair", [.positive ["left"], .negative ["left"]]⟩ : ViewType).WellFormed
      viewClasses ∧
    ¬ (⟨"Token", [.negative []]⟩ : ViewType).WellFormed viewClasses ∧
    ¬ (⟨"Token", [.positive ["missing"]]⟩ : ViewType).WellFormed viewClasses := by
  decide
-- ANCHOR_END: invalid_views

-- ANCHOR: focus_current_view
example :
    focus viewClasses
      ⟨"Box", [.negative ["item", "left"], .positive ["item", "right"]]⟩ ["item"] =
      some ⟨"Pair", [.negative ["left"], .positive ["right"]]⟩ ∧
    focus viewClasses (.whole "Box") [] = some (.whole "Box") ∧
    focus viewClasses ⟨"Pair", [.positive ["right"]]⟩ ["left"] = none := by
  decide
-- ANCHOR_END: focus_current_view

-- ANCHOR: empty_nested_path
example :
    emptyPath viewClasses (.whole "Box") ["item", "left"] =
      some ⟨"Box", [.negative ["item", "left"], .positive ["item", "right"]]⟩ ∧
    emptyPath viewClasses
      ⟨"Box", [.negative ["item", "left"], .positive ["item", "right"]]⟩ ["item"] =
      some ⟨"Box", [.negative ["item"]]⟩ ∧
    emptyPath viewClasses ⟨"Pair", [.positive ["right"]]⟩ ["left"] = none ∧
    emptyPath viewClasses ⟨"Pair", [.negative ["left"], .positive ["right"]]⟩ ["left"] =
      none := by
  decide
-- ANCHOR_END: empty_nested_path

-- Recursion in the class table does not cause normalization to unfold it.
def recursiveViewClasses : ClassTable := [("Loop", ⟨[("next", "Loop")]⟩)]

example : normalize recursiveViewClasses ⟨"Loop", [.positive ["next", "next"]]⟩ =
    .whole "Loop" := by decide

-- ANCHOR: cannot_recover_unknown_field
example : ¬ Subtype viewClasses ⟨"Pair", [.positive ["left"]]⟩ (.whole "Pair") := by
  intro strengthens
  have required := strengthens.2.1 ["right"] (by decide)
  have unknown : ¬ Pos viewClasses
      (normalize viewClasses ⟨"Pair", [.positive ["left"]]⟩) ["right"] := by decide
  exact unknown required
-- ANCHOR_END: cannot_recover_unknown_field

end Dada.Unique.Typing
