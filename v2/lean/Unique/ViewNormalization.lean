import Unique.ViewSoundness

namespace Dada.Unique.Typing

private theorem disjoint_pair {entries : List Entry}
    (disjoint : entriesDisjoint entries = true) {left right : Entry}
    (leftMem : left ∈ entries) (rightMem : right ∈ entries) (different : left ≠ right) :
    ¬left.path <+: right.path ∧ ¬right.path <+: left.path := by
  induction entries with
  | nil => simp at leftMem
  | cons entry rest ih =>
    simp only [entriesDisjoint, Bool.and_eq_true] at disjoint
    rcases List.mem_cons.mp leftMem with rfl | leftTail
    · have rightMem := (List.mem_cons.mp rightMem).resolve_left (Ne.symm different)
      have h := List.all_eq_true.mp disjoint.1 right rightMem
      have h := Bool.and_eq_true_iff.mp h
      exact ⟨fun pre => by simpa [List.isPrefixOf_iff_prefix.mpr pre] using h.1,
        fun pre => by simpa [List.isPrefixOf_iff_prefix.mpr pre] using h.2⟩
    · rcases List.mem_cons.mp rightMem with rfl | rightMem
      · have h := List.all_eq_true.mp disjoint.1 left leftTail
        have h : ¬right.path <+: left.path ∧ ¬left.path <+: right.path := by
          have h := Bool.and_eq_true_iff.mp h
          exact ⟨fun pre => by simpa [List.isPrefixOf_iff_prefix.mpr pre] using h.1,
            fun pre => by simpa [List.isPrefixOf_iff_prefix.mpr pre] using h.2⟩
        exact ⟨h.2,h.1⟩
      · exact ih disjoint.2 leftTail rightMem

private def Consistent (entries : List Entry) : Prop :=
  ∀ path, Entry.negative path ∈ entries → ¬Covers entries path

private theorem disjoint_consistent {entries : List Entry}
    (disjoint : entriesDisjoint entries = true) : Consistent entries := by
  intro path member ⟨entry, entryMember, cover⟩
  by_cases same : entry = .negative path
  · subst entry
    rcases cover with ⟨_, lt⟩ | ⟨_, impossible, _⟩
    · exact Nat.lt_irrefl _ lt
    · contradiction
  · have pairs := disjoint_pair disjoint member entryMember (Ne.symm same)
    rcases cover with ⟨pre, _⟩ | ⟨_, rfl, pre⟩
    · exact pairs.1 pre
    · exact pairs.2 pre

theorem ViewType.WellFormed.pos_not_neg {classes : ClassTable} {ty : ViewType}
    (wf : ty.WellFormed classes) {path : Path} (known : Pos classes ty path) : ¬Neg ty path := by
  intro negative
  have member := List.contains_iff_mem.mp negative
  obtain ⟨_, root | cover⟩ := pos_iff.mp known
  · subst path
    have valid := List.all_eq_true.mp wf.2.1 (.negative []) member
    simp [Entry.valid] at valid
  · exact disjoint_consistent wf.2.2 path member cover

private theorem selected_consistent {entries : List Entry} {field : FieldName}
    (consistent : Consistent entries) :
    Consistent (entries.filterMap (Entry.dropPrefix [field])) := by
  intro path member cover
  exact consistent _ (selected_negative member) (selected_covers cover)

private theorem normalized_negative {classes : ClassTable} (classesWF : classes.WellFormed)
    {fuel : Nat} {name : ClassName} {entries : List Entry} {path : Path}
    (consistent : Consistent entries)
    (noRoot : Entry.negative [] ∉ entries)
    (valid : (classAt classes name path).isSome = true)
    (member : Entry.negative path ∈ entries) :
    Entry.negative path ∈ normalizeEntries classes fuel name entries := by
  have nonempty : path ≠ [] := by intro eq; subst path; exact noRoot member
  induction fuel generalizing name entries path with
  | zero =>
    rw [normalizeEntries]
    split
    next whole =>
      have root := List.contains_iff_mem.mp whole
      exact False.elim (consistent path member ⟨.positive [], root,
        Or.inr ⟨[], rfl, by simp⟩⟩)
    next =>
      split
      · exact member
      · split
        next empty =>
          have emptyEntries := List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp empty).2
          simp [emptyEntries] at member
        · exact member
  | succ fuel ih =>
    rw [normalizeEntries]
    split
    next whole =>
      have root := List.contains_iff_mem.mp whole
      exact False.elim (consistent path member ⟨.positive [], root,
        Or.inr ⟨[], rfl, by simp⟩⟩)
    next notWhole =>
      split
      · exact member
      next declaration found =>
        split
        next empty =>
          have emptyEntries := List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp empty).2
          simp [emptyEntries] at member
        next notEmpty =>
          dsimp only
          split
          next complete =>
            have normalizedWhole : normalizeEntries classes (fuel+1) name entries = [.positive []] := by
              rw [normalizeEntries]
              simp only [notWhole, found]
              simp only [notEmpty]
              exact ite_eq_left complete
            have outputPos : Pos classes ⟨name, normalizeEntries classes (fuel+1) name entries⟩ path := by
              rw [normalizedWhole]
              exact pos_iff.mpr ⟨valid, Or.inr ⟨.positive [], by simp,
                Or.inr ⟨[], rfl, by simp⟩⟩⟩
            have inputPos := pos_iff.mp (normalizeEntries_pos classesWF outputPos)
            exact False.elim (consistent path member (inputPos.2.resolve_left nonempty))
          next =>
            cases path with
            | nil => contradiction
            | cons field rest =>
              cases targetFound : declaration.fields.lookup field with
              | none => simp [classAt, found, targetFound] at valid
              | some target =>
                have targetMember : (field, target) ∈ declaration.fields := by
                  obtain ⟨before, after, eq, _⟩ := List.lookup_eq_some_iff.mp targetFound
                  simp [eq]
                apply List.mem_flatMap.mpr
                refine ⟨(field,target), targetMember, ?_⟩
                dsimp only
                have selected : Entry.negative rest ∈ entries.filterMap (Entry.dropPrefix [field]) := by
                  exact List.mem_filterMap.mpr ⟨.negative (field::rest), member, by simp⟩
                split
                next empty =>
                  have empty := List.isEmpty_iff.mp empty
                  simp [empty] at selected
                next =>
                  split
                  next root =>
                    have root := List.contains_iff_mem.mp root
                    by_cases restEmpty : rest = []
                    · simp [restEmpty]
                    · have cover : Covers (entries.filterMap (Entry.dropPrefix [field])) [] :=
                        ⟨.negative rest, selected, Or.inl ⟨by simp, List.length_pos_iff.mpr restEmpty⟩⟩
                      exact False.elim (selected_consistent consistent [] root cover)
                  next noRootSelected =>
                    apply List.mem_map.mpr
                    refine ⟨.negative rest, ?_, rfl⟩
                    apply ih (selected_consistent consistent)
                    · exact fun h => noRootSelected (List.contains_iff_mem.mpr h)
                    · simpa [classAt, found, targetFound] using valid
                    · exact selected
                    · intro eq; subst rest
                      exact noRootSelected (List.contains_iff_mem.mpr selected)

 theorem normalize_neg_iff {classes : ClassTable} (classesWF : classes.WellFormed)
    {ty : ViewType} (wf : ty.WellFormed classes) (path : Path) :
    Neg (normalize classes ty) path ↔ Neg ty path := by
  constructor
  · exact normalize_neg
  · intro negative
    have member := List.contains_iff_mem.mp negative
    apply List.contains_iff_mem.mpr
    apply normalized_negative classesWF (disjoint_consistent wf.2.2)
    · intro root
      have valid := List.all_eq_true.mp wf.2.1 (.negative []) root
      simp [Entry.valid] at valid
    · have valid := List.all_eq_true.mp wf.2.1 (.negative path) member
      exact (Bool.and_eq_true_iff.mp valid).1
    · exact member

private theorem normalizeEntries_nonempty_of_positive {classes : ClassTable} {fuel : Nat}
    {name : ClassName} {entries : List Entry} {path : Path}
    (valid : (classAt classes name path).isSome = true)
    (member : Entry.positive path ∈ entries) :
    normalizeEntries classes fuel name entries ≠ [] := by
  induction fuel generalizing name entries path with
  | zero =>
    rw [normalizeEntries]
    split
    · simp
    · split
      · exact List.ne_nil_of_mem member
      · split
        · simp
        · exact List.ne_nil_of_mem member
  | succ fuel ih =>
    rw [normalizeEntries]
    split
    · simp
    next notWhole =>
      split
      · exact List.ne_nil_of_mem member
      next declaration found =>
        split
        · simp
        · dsimp only
          split
          · simp
          · cases path with
            | nil => exact False.elim (notWhole (List.contains_iff_mem.mpr member))
            | cons field rest =>
              cases targetFound : declaration.fields.lookup field with
              | none => simp [classAt, found, targetFound] at valid
              | some target =>
                have targetMember : (field,target) ∈ declaration.fields := by
                  obtain ⟨before, after, eq, _⟩ := List.lookup_eq_some_iff.mp targetFound
                  simp [eq]
                have selected : Entry.positive rest ∈ entries.filterMap (Entry.dropPrefix [field]) :=
                  List.mem_filterMap.mpr ⟨.positive (field::rest), member, by simp⟩
                have selectedNonempty := List.ne_nil_of_mem selected
                intro empty
                have noMember := List.flatMap_eq_nil_iff.mp empty (field,target) targetMember
                dsimp only at noMember
                split at noMember
                next absent => exact selectedNonempty (List.isEmpty_iff.mp absent)
                next =>
                  split at noMember
                  · simp at noMember
                  · have noMember := List.map_eq_nil_iff.mp noMember
                    exact ih (by simpa [classAt, found, targetFound] using valid) selected noMember

private theorem covers_root {entries : List Entry} {path : Path} (cover : Covers entries path) :
    Covers entries [] := by
  obtain ⟨entry, member, covered⟩ := cover
  refine ⟨entry, member, ?_⟩
  rcases covered with ⟨_, lt⟩ | ⟨p, rfl, _⟩
  · exact Or.inl ⟨by simp, Nat.lt_of_le_of_lt (Nat.zero_le _) lt⟩
  · cases p with
    | nil => exact Or.inr ⟨[], rfl, by simp⟩
    | cons head tail => exact Or.inl ⟨by simp, by simp [Entry.path]⟩

private theorem selected_paths_valid {classes : ClassTable} {name : ClassName} {entries : List Entry}
    {field : FieldName} {declaration : TypedClass} {target : ClassName}
    (found : classes.lookup name = some declaration)
    (targetFound : declaration.fields.lookup field = some target)
    (valid : ∀entry ∈ entries, (classAt classes name entry.path).isSome = true) :
    ∀entry ∈ entries.filterMap (Entry.dropPrefix [field]),
      (classAt classes target entry.path).isSome = true := by
  intro entry member
  obtain ⟨source, sourceMember, selected⟩ := List.mem_filterMap.mp member
  have eq := Entry.dropPrefix_eq_some selected
  subst source
  simpa [classAt, found, targetFound] using valid _ sourceMember

private theorem selected_covers_inv {entries : List Entry} {field : FieldName} {path : Path}
    (notWhole : Entry.positive [] ∉ entries) (cover : Covers entries (field :: path)) :
    Covers (entries.filterMap (Entry.dropPrefix [field])) path := by
  obtain ⟨entry, member, covered⟩ := cover
  cases entry with
  | negative entryPath =>
    cases entryPath with
    | nil => rcases covered with ⟨pre, _⟩ | ⟨_, impossible, _⟩ <;> simp_all [Entry.path]
    | cons other rest =>
      rcases covered with ⟨pre, len⟩ | ⟨_, impossible, _⟩
      · have pre : field = other ∧ path <+: rest := by simpa [Entry.path] using pre
        obtain ⟨rfl, tailPre⟩ := pre
        exact ⟨.negative rest, List.mem_filterMap.mpr ⟨_, member, by simp⟩,
          Or.inl ⟨tailPre, by simpa [Entry.path] using len⟩⟩
      · contradiction
  | positive entryPath =>
    cases entryPath with
    | nil => exact False.elim (notWhole member)
    | cons other rest =>
      have cover : Covers [Entry.positive (other :: rest)] (field :: path) :=
        ⟨_, by simp, covered⟩
      obtain ⟨same, selected⟩ := covers_cons_prepend_inv (entry := .positive rest) covered
      subst other
      obtain ⟨entry, singleton, covered⟩ := selected
      have eq := List.mem_singleton.mp singleton
      subst entry
      exact ⟨.positive rest, List.mem_filterMap.mpr ⟨_, member, by simp⟩, covered⟩

private theorem covers_of_nonempty {entries : List Entry} (nonempty : entries ≠ [])
    (noRoot : Entry.negative [] ∉ entries) : Covers entries [] := by
  obtain ⟨entry, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  refine ⟨entry, member, ?_⟩
  cases entry with
  | positive path =>
    cases path with
    | nil => exact Or.inr ⟨[], rfl, by simp⟩
    | cons head rest => exact Or.inl ⟨by simp, by simp [Entry.path]⟩
  | negative path =>
    cases path with
    | nil => exact False.elim (noRoot member)
    | cons head rest => exact Or.inl ⟨by simp, by simp [Entry.path]⟩

private theorem normalized_positive {classes : ClassTable} (classesWF : classes.WellFormed)
    {fuel : Nat} {name : ClassName} {entries : List Entry} {path : Path}
    (consistent : Consistent entries)
    (pathsValid : ∀entry ∈ entries, (classAt classes name entry.path).isSome = true)
    (known : Pos classes ⟨name, entries⟩ path) :
    Pos classes ⟨name, normalizeEntries classes fuel name entries⟩ path := by
  induction fuel generalizing name entries path with
  | zero =>
    rw [normalizeEntries]
    split
    · exact pos_iff.mpr ⟨known.valid, Or.inr ⟨.positive [], by simp, Or.inr ⟨[], rfl, by simp⟩⟩⟩
    · split
      · exact known
      · split
        · exact pos_iff.mpr ⟨known.valid, Or.inr ⟨.positive [], by simp, Or.inr ⟨[], rfl, by simp⟩⟩⟩
        · exact known
  | succ fuel ih =>
    rw [normalizeEntries]
    split
    · exact pos_iff.mpr ⟨known.valid, Or.inr ⟨.positive [], by simp, Or.inr ⟨[], rfl, by simp⟩⟩⟩
    next notWhole =>
      split
      · exact known
      next declaration found =>
        split
        · exact pos_iff.mpr ⟨known.valid, Or.inr ⟨.positive [], by simp, Or.inr ⟨[], rfl, by simp⟩⟩⟩
        · dsimp only
          split
          · exact pos_iff.mpr ⟨known.valid, Or.inr ⟨.positive [], by simp, Or.inr ⟨[], rfl, by simp⟩⟩⟩
          · cases path with
            | nil => exact Pos.root _ _
            | cons field rest =>
              have valid := known.valid
              cases targetFound : declaration.fields.lookup field with
              | none => simp [classAt, found, targetFound] at valid
              | some target =>
                have targetMember : (field,target) ∈ declaration.fields := by
                  obtain ⟨before, after, eq, _⟩ := List.lookup_eq_some_iff.mp targetFound
                  simp [eq]
                have cover : Covers entries (field::rest) := by
                  exact (pos_iff.mp known).2.resolve_left (by simp)
                have selectedCover := selected_covers_inv
                  (fun h => notWhole (List.contains_iff_mem.mpr h)) cover
                have selectedConsistent := selected_consistent (field := field) consistent
                have selectedNoRoot : Entry.negative [] ∉ entries.filterMap (Entry.dropPrefix [field]) := by
                  intro negative
                  exact selectedConsistent [] negative (covers_root selectedCover)
                have selectedValid := selected_paths_valid found targetFound pathsValid
                have selectedPositive : Pos classes
                    ⟨target, entries.filterMap (Entry.dropPrefix [field])⟩ rest := by
                  refine pos_iff.mpr ⟨?_, Or.inr selectedCover⟩
                  simpa [classAt, found, targetFound] using valid
                have outputPositive := ih selectedConsistent selectedValid selectedPositive
                have outputNonempty : normalizeEntries classes fuel target
                    (entries.filterMap (Entry.dropPrefix [field])) ≠ [] := by
                  obtain ⟨entry, member, _⟩ := selectedCover
                  cases entry with
                  | positive p => exact normalizeEntries_nonempty_of_positive (selectedValid _ member) member
                  | negative p =>
                    exact List.ne_nil_of_mem
                      (normalized_negative classesWF selectedConsistent selectedNoRoot (selectedValid _ member) member)
                have outputCover : Covers
                    (normalizeEntries classes fuel target (entries.filterMap (Entry.dropPrefix [field]))) rest := by
                  rcases (pos_iff.mp outputPositive).2 with root | cover
                  · subst rest
                    exact covers_of_nonempty outputNonempty
                      (fun h => selectedNoRoot (normalizeEntries_negative h))
                  · exact cover
                obtain ⟨entry, member, covered⟩ := (covers_prepend _ field rest).mpr outputCover
                refine pos_iff.mpr ⟨valid, Or.inr ⟨entry, ?_, covered⟩⟩
                apply List.mem_flatMap.mpr
                refine ⟨(field,target), targetMember, ?_⟩
                dsimp only
                have selectedNonempty : (entries.filterMap (Entry.dropPrefix [field])).isEmpty = false := by
                  apply List.isEmpty_eq_false_iff.mpr
                  obtain ⟨entry, member, _⟩ := selectedCover
                  exact List.ne_nil_of_mem member
                have noRootBool : (entries.filterMap (Entry.dropPrefix [field])).contains (.negative []) = false :=
                  Bool.eq_false_iff.mpr (fun h => selectedNoRoot (List.contains_iff_mem.mp h))
                simpa only [selectedNonempty, Bool.false_eq_true, ↓reduceIte, noRootBool] using member

theorem normalize_pos_iff {classes : ClassTable} (classesWF : classes.WellFormed)
    {ty : ViewType} (wf : ty.WellFormed classes) (path : Path) :
    Pos classes (normalize classes ty) path ↔ Pos classes ty path := by
  constructor
  · exact normalize_pos classesWF
  · apply normalized_positive classesWF (disjoint_consistent wf.2.2)
    intro entry member
    exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp wf.2.1 entry member)).1

end Dada.Unique.Typing
