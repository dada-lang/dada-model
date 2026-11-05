import Assignment.StorageTypes
import Shared.TypingViewLemmas

namespace Dada.Assignment.View
open Unique.Typing

def retained (classes : ClassTable) (ty : ViewType) (path : Path) : List Entry :=
  ty.entries.flatMap fun entry =>
    if path.isPrefixOf entry.path then []
    else match entry with
    | .negative _ => [entry]
    | .positive initialPath =>
      if initialPath.isPrefixOf path then
        match classAt classes ty.className initialPath with
        | none => []
        | some target =>
          (remainingAfterMove classes target (path.drop initialPath.length)).map
            (Entry.prepend initialPath)
      else [entry]

theorem covers_avoids {entry : Entry} {target path : Path}
    (cover : Covers [entry] path)
    (left : ¬target <+: entry.path)
    (right : ∀ initialPath, entry = .positive initialPath → ¬initialPath <+: target) :
    ¬target <+: path := by
  obtain ⟨other, member, covered⟩ := cover
  have eq := List.mem_singleton.mp member
  subst other
  intro pre
  rcases covered with ⟨entryPrefix, _⟩ | ⟨initialPath, eq, entryPrefix⟩
  · exact left (pre.trans entryPrefix)
  · rcases List.prefix_or_prefix_of_prefix pre entryPrefix with h | h
    · exact left (by simpa [eq, Entry.path] using h)
    · exact right initialPath eq h

theorem retained_covers {classes : ClassTable} {ty : ViewType} {target path : Path}
    (valid : (classAt classes ty.className path).isSome = true)
    (cover : Covers (retained classes ty target) path) :
    Pos classes ty path ∧ ¬target <+: path := by
  obtain ⟨entry, member, covered⟩ := cover
  obtain ⟨source, sourceMember, member⟩ := List.mem_flatMap.mp member
  split at member
  · simp at member
  next notBelow =>
    have notBelow := fun h => notBelow (List.isPrefixOf_iff_prefix.mpr h)
    cases source with
    | negative negativePath =>
      have eq := List.mem_singleton.mp member
      subst entry
      exact ⟨pos_iff.mpr ⟨valid, Or.inr ⟨_, sourceMember, covered⟩⟩,
        covers_avoids ⟨_, by simp, covered⟩ notBelow (by simp)⟩
    | positive initialPath =>
      dsimp only at member
      split at member
      next above =>
        have above := List.isPrefixOf_iff_prefix.mp above
        have targetEq := List.prefix_iff_eq_append.mp above
        split at member
        · simp at member
        next name found =>
          obtain ⟨sibling, siblingMember, eq⟩ := List.mem_map.mp member
          subst entry
          obtain ⟨siblingPath, rfl, left, right⟩ := remainingAfterMove_entries siblingMember
          have sourcePositive : Pos classes ty path := by
            apply positive_entry_related sourceMember _ valid
            rcases covered with ⟨pre, _⟩ | ⟨p, eq, pre⟩
            · have initPre : initialPath <+: initialPath ++ siblingPath := ⟨_, rfl⟩
              exact List.prefix_or_prefix_of_prefix initPre (by simpa [Entry.prepend, Entry.path] using pre)
            · simp only [Entry.prepend, Entry.positive.injEq] at eq
              subst p
              exact Or.inl ((show initialPath <+: initialPath ++ siblingPath from ⟨_, rfl⟩).trans pre)
          refine ⟨sourcePositive, covers_avoids (entry := .positive (initialPath ++ siblingPath))
            ⟨_, by simp [Entry.prepend], covered⟩ ?_ ?_⟩
          · change ¬target <+: initialPath ++ siblingPath
            rw [←targetEq]
            simpa using left
          · intro p eq
            simp only [Entry.positive.injEq] at eq
            subst p
            rw [←targetEq]
            simpa using right
      next notAbove =>
        have eq := List.mem_singleton.mp member
        subst entry
        refine ⟨pos_iff.mpr ⟨valid, Or.inr ⟨_, sourceMember, covered⟩⟩,
          covers_avoids ⟨_, by simp, covered⟩ notBelow ?_⟩
        intro p eq
        have eq := Entry.positive.inj eq
        subst p
        exact fun h => notAbove (List.isPrefixOf_iff_prefix.mpr h)

theorem retained_negative {classes : ClassTable} {ty : ViewType} {target path : Path}
    (member : Entry.negative path ∈ retained classes ty target) :
    Neg ty path ∧ ¬target <+: path := by
  obtain ⟨entry, sourceMember, member⟩ := List.mem_flatMap.mp member
  split at member
  · simp at member
  next notBelow =>
    cases entry with
    | negative p =>
      have eq := List.mem_singleton.mp member
      cases eq
      exact ⟨List.contains_iff_mem.mpr sourceMember, fun h =>
        notBelow (List.isPrefixOf_iff_prefix.mpr h)⟩
    | positive p =>
      dsimp only at member
      split at member
      · split at member
        · simp at member
        · obtain ⟨entry, entryMember, eq⟩ := List.mem_map.mp member
          obtain ⟨path, rfl, _, _⟩ := remainingAfterMove_entries entryMember
          simp [Entry.prepend] at eq
      · simp at member


theorem covers_prepend_general (entries : List Entry) (target query : Path) :
    Covers (entries.map (Entry.prepend target)) (target ++ query) ↔ Covers entries query := by
  constructor
  · rintro ⟨entry, member, covered⟩
    obtain ⟨source, sourceMember, eq⟩ := List.mem_map.mp member
    subst entry
    refine ⟨source, sourceMember, ?_⟩
    rcases covered with ⟨pre, length⟩ | ⟨initial, same, pre⟩
    · exact .inl ⟨by simpa using pre, by simpa using length⟩
    · cases source with
      | positive path =>
        simp only [Entry.prepend, Entry.positive.injEq] at same
        subst initial
        exact .inr ⟨path, rfl, by simpa using pre⟩
      | negative path => simp [Entry.prepend] at same
  · rintro ⟨entry, member, covered⟩
    refine ⟨entry.prepend target, List.mem_map.mpr ⟨entry, member, rfl⟩, ?_⟩
    rcases covered with ⟨pre, length⟩ | ⟨path, rfl, pre⟩
    · exact .inl ⟨by simpa using pre, by simpa using length⟩
    · exact .inr ⟨target ++ path, rfl, by simpa using pre⟩

theorem prefixed_positive {classes : ClassTable} {source incoming : ViewType} {target query : Path}
    (atClass : classAt classes source.className target = some incoming.className)
    (parentKnown : ∀ path, path <+: target → path.length < target.length → Pos classes source path)
    (valid : (classAt classes source.className query).isSome = true)
    (cover : Covers (incoming.entries.map (Entry.prepend target)) query) :
    (Pos classes source query ∧ ¬target <+: query) ∨
      ∃ suffix, query = target ++ suffix ∧ Pos classes incoming suffix := by
  by_cases inside : target <+: query
  · obtain ⟨suffix, rfl⟩ := inside
    right
    refine ⟨suffix, rfl, pos_iff.mpr ⟨?_, .inr ((covers_prepend_general _ _ _).mp cover)⟩⟩
    simpa [classAt_append, atClass] using valid
  · left
    refine ⟨?_, inside⟩
    obtain ⟨entry, member, covered⟩ := cover
    obtain ⟨sourceEntry, member, rfl⟩ := List.mem_map.mp member
    have before : query <+: target := by
      rcases covered with ⟨pre, _⟩ | ⟨initial, same, pre⟩
      · have targetPrefix : target <+: (sourceEntry.prepend target).path := by simp
        exact (List.prefix_or_prefix_of_prefix pre targetPrefix).resolve_right inside
      · cases sourceEntry with
        | positive path =>
          simp only [Entry.prepend, Entry.positive.injEq] at same
          subst initial
          exact False.elim (inside ((show target <+: target ++ path from ⟨path,rfl⟩).trans pre))
        | negative path => simp [Entry.prepend] at same
    exact parentKnown query before (Nat.lt_of_le_of_ne before.length_le (by
      intro same
      have eq := before.eq_of_length same
      subst query
      exact inside (by simp)))

theorem prefixed_negative {entries : List Entry} {target query : Path}
    (member : Entry.negative query ∈ entries.map (Entry.prepend target)) :
    ∃ suffix, query = target ++ suffix ∧ Entry.negative suffix ∈ entries := by
  obtain ⟨entry, member, same⟩ := List.mem_map.mp member
  cases entry with
  | positive path => simp [Entry.prepend] at same
  | negative path =>
    simp only [Entry.prepend, Entry.negative.injEq] at same
    exact ⟨path, same.symm, member⟩

theorem replacement_positive {classes : ClassTable} (classesWF : classes.WellFormed)
    {source incoming : ViewType} {target query : Path}
    (nonempty : target ≠ [])
    (atClass : classAt classes source.className target = some incoming.className)
    (parentKnown : ∀ path, path <+: target → path.length < target.length → Pos classes source path)
    (known : Pos classes (normalize classes ⟨source.className,
      retained classes source target ++ incoming.entries.map (Entry.prepend target)⟩) query) :
    (Pos classes source query ∧ ¬target <+: query) ∨
      ∃ suffix, query = target ++ suffix ∧ Pos classes incoming suffix := by
  obtain ⟨valid, root | ⟨entry, member, covered⟩⟩ := pos_iff.mp (normalize_pos classesWF known)
  · subst query
    exact .inl ⟨pos_iff.mpr ⟨valid, .inl rfl⟩, by simpa using nonempty⟩
  · rcases List.mem_append.mp member with retainedMember | incomingMember
    · exact .inl (retained_covers valid ⟨entry, retainedMember, covered⟩)
    · exact prefixed_positive atClass parentKnown valid ⟨entry, incomingMember, covered⟩

theorem replacement_negative {classes : ClassTable} {source incoming : ViewType} {target query : Path}
    (known : Neg (normalize classes ⟨source.className,
      retained classes source target ++ incoming.entries.map (Entry.prepend target)⟩) query) :
    (Neg source query ∧ ¬target <+: query) ∨
      ∃ suffix, query = target ++ suffix ∧ Neg incoming suffix := by
  have member := List.contains_iff_mem.mp (normalize_neg known)
  rcases List.mem_append.mp member with retainedMember | incomingMember
  · exact .inl (retained_negative retainedMember)
  · obtain ⟨suffix, same, member⟩ := prefixed_negative incomingMember
    exact .inr ⟨suffix, same, List.contains_iff_mem.mpr member⟩

end Dada.Assignment.View

namespace Dada.Assignment
open Shared Shared.Typing

@[simp] theorem replaceView_permission (classes : ClassTable) (source incoming : ValueType) (path : Path) :
    (replaceView classes source incoming path).permission = source.permission := rfl

@[simp] theorem replaceView_base (classes : ClassTable) (source incoming : ValueType) (path : Path) :
    (replaceView classes source incoming path).base = source.base := rfl

theorem replaceView_positive {classes : ClassTable} (classesWF : classes.WellFormed)
    {source incoming : ValueType} {target query : Path}
    (nonempty : target ≠ [])
    (atClass : Unique.Typing.classAt classes.nominal source.base target = some incoming.base)
    (parentKnown : ∀ path, path <+: target → path.length < target.length → Pos classes source path)
    (known : Pos classes (replaceView classes source incoming target) query) :
    (Pos classes source query ∧ ¬target <+: query) ∨
      ∃ suffix, query = target ++ suffix ∧ Pos classes incoming suffix := by
  exact View.replacement_positive classesWF.nominal nonempty atClass parentKnown known

theorem replaceView_negative {classes : ClassTable} {source incoming : ValueType} {target query : Path}
    (known : Neg (replaceView classes source incoming target) query) :
    (Neg source query ∧ ¬target <+: query) ∨
      ∃ suffix, query = target ++ suffix ∧ Neg incoming suffix := by
  exact View.replacement_negative known

end Dada.Assignment
