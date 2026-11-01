import Unique.Views

namespace Dada.Unique.Typing

@[simp] theorem Entry.path_prepend (initialPath : Path) (entry : Entry) :
    (entry.prepend initialPath).path = initialPath ++ entry.path := by
  cases entry <;> rfl

@[simp] theorem Entry.dropPrefix_cons (field other : FieldName) (path : Path) :
    Entry.dropPrefix [field] (.positive (other :: path)) =
      if field = other then some (.positive path) else none := by
  simp [Entry.dropPrefix, Entry.path, List.isPrefixOf_cons_cons]

@[simp] theorem Entry.dropPrefix_negative_cons (field other : FieldName) (path : Path) :
    Entry.dropPrefix [field] (.negative (other :: path)) =
      if field = other then some (.negative path) else none := by
  simp [Entry.dropPrefix, Entry.path, List.isPrefixOf_cons_cons]

@[simp] theorem Entry.dropPrefix_nil (field : FieldName) (entry : Entry)
    (empty : entry.path = []) : Entry.dropPrefix [field] entry = none := by
  simp [Entry.dropPrefix, empty]

theorem Entry.dropPrefix_eq_some {initialPath : Path} {entry result : Entry}
    (selected : entry.dropPrefix initialPath = some result) : entry = result.prepend initialPath := by
  unfold Entry.dropPrefix at selected
  split at selected
  next initialPathOf =>
    have h := List.isPrefixOf_iff_prefix.mp initialPathOf
    have append : initialPath ++ entry.path.drop initialPath.length = entry.path :=
      List.prefix_iff_eq_append.mp h
    cases entry <;> simp only [Option.some.injEq] at selected <;> subst result
    · exact congrArg Entry.positive append.symm
    · exact congrArg Entry.negative append.symm
  next => contradiction

theorem selected_negative {entries : List Entry} {field : FieldName} {path : Path}
    (member : Entry.negative path ∈ entries.filterMap (Entry.dropPrefix [field])) :
    Entry.negative (field :: path) ∈ entries := by
  obtain ⟨entry, member, selected⟩ := List.mem_filterMap.mp member
  have eq := Entry.dropPrefix_eq_some selected
  simpa [eq, Entry.prepend] using member

theorem normalizeEntries_negative {classes : ClassTable} {fuel : Nat}
    {name : ClassName} {entries : List Entry} {path : Path}
    (member : Entry.negative path ∈ normalizeEntries classes fuel name entries) :
    Entry.negative path ∈ entries := by
  induction fuel generalizing name entries path with
  | zero =>
    rw [normalizeEntries] at member
    split at member
    · simp at member
    · split at member
      · exact member
      · split at member
        · simp at member
        · exact member
  | succ fuel ih =>
    rw [normalizeEntries] at member
    split at member
    · simp at member
    · split at member
      · exact member
      · split at member
        · simp at member
        · dsimp only at member
          split at member
          · simp at member
          · obtain ⟨⟨field,target⟩, _, member⟩ := List.mem_flatMap.mp member
            dsimp only at member
            split at member
            · simp at member
            · split at member
              next contains =>
                simp only [List.mem_singleton] at member
                have found := List.contains_iff_mem.mp contains
                have h := selected_negative found
                cases member
                exact h
              next =>
                obtain ⟨entry, found, eq⟩ := List.mem_map.mp member
                cases entry with
                | positive rest => simp [Entry.prepend] at eq
                | negative rest =>
                  simp only [Entry.prepend, List.singleton_append, Entry.negative.injEq] at eq
                  subst path
                  exact selected_negative (ih found)

theorem normalize_neg {classes : ClassTable} {ty : ViewType} {path : Path}
    (known : Neg (normalize classes ty) path) : Neg ty path := by
  exact List.contains_iff_mem.mpr (normalizeEntries_negative (List.contains_iff_mem.mp known))

def Covers (entries : List Entry) (path : Path) : Prop :=
  ∃ entry ∈ entries,
    (path <+: entry.path ∧ path.length < entry.path.length) ∨
    ∃ initialPath, entry = .positive initialPath ∧ initialPath <+: path

theorem pos_iff {classes : ClassTable} {name : ClassName} {entries : List Entry} {path : Path} :
    Pos classes ⟨name, entries⟩ path ↔
      (classAt classes name path).isSome = true ∧ (path = [] ∨ Covers entries path) := by
  simp only [Pos, positive, Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff,
    List.any_eq_true, Covers, Bool.and_eq_true, decide_eq_true_eq, List.isPrefixOf_iff_prefix]
  constructor
  · rintro ⟨valid, root | ⟨entry, member, h⟩⟩
    · exact ⟨valid, Or.inl root⟩
    · refine ⟨valid, Or.inr ⟨entry, member, ?_⟩⟩
      rcases h with ⟨lt, pre⟩ | positive
      · exact Or.inl ⟨pre, lt⟩
      · cases entry with
        | positive p => exact Or.inr ⟨p, rfl, List.isPrefixOf_iff_prefix.mp positive⟩
        | negative p => contradiction
  · rintro ⟨valid, root | ⟨entry, member, h⟩⟩
    · exact ⟨valid, Or.inl root⟩
    · refine ⟨valid, Or.inr ⟨entry, member, ?_⟩⟩
      rcases h with ⟨pre, lt⟩ | ⟨p, rfl, pre⟩
      · exact Or.inl ⟨lt, pre⟩
      · exact Or.inr (List.isPrefixOf_iff_prefix.mpr pre)

theorem covers_prepend (entries : List Entry) (field : FieldName) (path : Path) :
    Covers (entries.map (Entry.prepend [field])) (field :: path) ↔ Covers entries path := by
  simp only [Covers, List.mem_map]
  constructor
  · rintro ⟨entry, ⟨source, member, rfl⟩, h⟩
    refine ⟨source, member, ?_⟩
    rcases h with ⟨pre, len⟩ | ⟨initialPath, eq, pre⟩
    · exact Or.inl ⟨by simpa using pre, by simpa using len⟩
    · cases source with
      | positive p =>
        simp only [Entry.prepend, List.singleton_append, Entry.positive.injEq] at eq
        subst initialPath
        exact Or.inr ⟨p, rfl, by simpa using pre⟩
      | negative p => simp [Entry.prepend] at eq
  · rintro ⟨entry, member, h⟩
    refine ⟨entry.prepend [field], ⟨entry, member, rfl⟩, ?_⟩
    rcases h with ⟨pre, len⟩ | ⟨p, rfl, pre⟩
    · exact Or.inl ⟨by simpa using pre, by simpa using len⟩
    · exact Or.inr ⟨field :: p, rfl, by simpa using pre⟩

theorem selected_covers {entries : List Entry} {field : FieldName} {path : Path}
    (cover : Covers (entries.filterMap (Entry.dropPrefix [field])) path) :
    Covers entries (field :: path) := by
  obtain ⟨entry, member, h⟩ := cover
  obtain ⟨source, member, selected⟩ := List.mem_filterMap.mp member
  have eq := Entry.dropPrefix_eq_some selected
  subst source
  refine ⟨entry.prepend [field], member, ?_⟩
  rcases h with ⟨pre, len⟩ | ⟨p, rfl, pre⟩
  · exact Or.inl ⟨by simpa using pre, by simpa using len⟩
  · exact Or.inr ⟨field :: p, rfl, by simpa using pre⟩

theorem selected_root_covers {entries : List Entry} {field : FieldName}
    (nonempty : (entries.filterMap (Entry.dropPrefix [field])).isEmpty = false)
    (noNegative : (entries.filterMap (Entry.dropPrefix [field])).contains (.negative []) = false) :
    Covers entries [field] := by
  obtain ⟨entry, member⟩ := List.exists_mem_of_ne_nil _ (List.isEmpty_eq_false_iff.mp nonempty)
  obtain ⟨source, member, selected⟩ := List.mem_filterMap.mp member
  have eq := Entry.dropPrefix_eq_some selected
  subst source
  refine ⟨entry.prepend [field], member, ?_⟩
  cases entry with
  | positive path =>
    cases path with
    | nil => exact Or.inr ⟨[field], rfl, ⟨[], by simp⟩⟩
    | cons head rest => exact Or.inl ⟨by simp [Entry.path, Entry.prepend], by simp [Entry.path, Entry.prepend]⟩
  | negative path =>
    cases path with
    | nil =>
      have : Entry.negative [] ∈ entries.filterMap (Entry.dropPrefix [field]) :=
        List.mem_filterMap.mpr ⟨_, member, selected⟩
      have := List.contains_iff_mem.mpr this
      simp_all
    | cons head rest => exact Or.inl ⟨by simp [Entry.path, Entry.prepend], by simp [Entry.path, Entry.prepend]⟩

private theorem lookup_mem {Key Value : Type} [BEq Key] [LawfulBEq Key]
    {entries : List (Key × Value)} {key : Key} {value : Value}
    (found : entries.lookup key = some value) : (key, value) ∈ entries := by
  obtain ⟨before, after, rfl, _⟩ := List.lookup_eq_some_iff.mp found
  simp

private theorem lookup_member_unique {Key Value : Type} [BEq Key] [LawfulBEq Key]
    {entries : List (Key × Value)} {key : Key} {value : Value}
    (distinct : (entries.map Prod.fst).Nodup) (member : (key, value) ∈ entries) :
    entries.lookup key = some value := by
  induction entries with
  | nil => simp at member
  | cons entry rest ih =>
    obtain ⟨entryKey, entryValue⟩ := entry
    simp only [List.map_cons, List.nodup_cons] at distinct
    rcases List.mem_cons.mp member with eq | member
    · cases eq; simp
    · have different : key ≠ entryKey := by
        intro eq; subst key
        exact distinct.1 (List.mem_map.mpr ⟨_, member, rfl⟩)
      simpa [List.lookup_cons, show (key == entryKey) = false from beq_eq_false_iff_ne.mpr different] using ih distinct.2 member

theorem covers_cons_prepend_inv {entry : Entry} {field other : FieldName} {path : Path}
    (cover : (field :: path <+: (entry.prepend [other]).path ∧
      (field :: path).length < (entry.prepend [other]).path.length) ∨
      ∃ initialPath, entry.prepend [other] = .positive initialPath ∧
        initialPath <+: field :: path) :
    field = other ∧ Covers [entry] path := by
  rcases cover with ⟨pre, lt⟩ | ⟨initialPath, eq, pre⟩
  · simp only [Entry.path_prepend, List.singleton_append, List.cons_prefix_cons] at pre
    obtain ⟨rfl, pre⟩ := pre
    exact ⟨rfl, entry, by simp, Or.inl ⟨pre, by simpa using lt⟩⟩
  · cases entry with
    | positive rest =>
      simp only [Entry.prepend, List.singleton_append, Entry.positive.injEq] at eq
      subst initialPath
      simp only [List.cons_prefix_cons] at pre
      obtain ⟨rfl, pre⟩ := pre
      exact ⟨rfl, .positive rest, by simp, Or.inr ⟨rest, rfl, pre⟩⟩
    | negative rest => simp [Entry.prepend] at eq

private def normalizeChildren (classes : ClassTable) (fuel : Nat)
    (fields : List (FieldName × ClassName)) (entries : List Entry) : List Entry :=
  fields.flatMap fun (field, target) =>
    let selected := entries.filterMap (Entry.dropPrefix [field])
    if selected.isEmpty then []
    else if selected.contains (.negative []) then [.negative [field]]
    else (normalizeEntries classes fuel target selected).map (Entry.prepend [field])

private theorem children_sound {classes : ClassTable} {fuel : Nat}
    (ih : ∀ name entries path,
      Pos classes ⟨name, normalizeEntries classes fuel name entries⟩ path →
      Pos classes ⟨name, entries⟩ path)
    {name : ClassName} {declaration : TypedClass} {entries : List Entry}
    (found : classes.lookup name = some declaration)
    (distinct : (declaration.fields.map Prod.fst).Nodup)
    {field : FieldName} {path : Path}
    (valid : (classAt classes name (field :: path)).isSome = true)
    (cover : Covers (normalizeChildren classes fuel declaration.fields entries) (field :: path)) :
    Pos classes ⟨name, entries⟩ (field :: path) := by
  obtain ⟨entry, member, cover⟩ := cover
  obtain ⟨⟨other,target⟩, fieldMember, member⟩ := List.mem_flatMap.mp member
  dsimp only at member
  split at member
  · simp at member
  · rename_i nonempty
    split at member
    · have eq : entry = .negative [other] := List.mem_singleton.mp member
      subst entry
      rcases cover with ⟨pre, len⟩ | ⟨_, impossible, _⟩
      · simp [Entry.path] at len
      · contradiction
    · rename_i noNegative
      obtain ⟨child, childMember, eq⟩ := List.mem_map.mp member
      subst entry
      obtain ⟨rfl, childCover⟩ := covers_cons_prepend_inv cover
      have targetFound := lookup_member_unique distinct fieldMember
      have childValid : (classAt classes target path).isSome = true := by
        simpa [classAt, found, targetFound] using valid
      have childPositive : Pos classes
          ⟨target, normalizeEntries classes fuel target
            (entries.filterMap (Entry.dropPrefix [field]))⟩ path := by
        refine pos_iff.mpr ⟨childValid, Or.inr ?_⟩
        obtain ⟨child', singleton, covered⟩ := childCover
        have eq := List.mem_singleton.mp singleton
        subst child'
        exact ⟨child, childMember, covered⟩
      have sourcePositive := pos_iff.mp (ih _ _ _ childPositive)
      refine pos_iff.mpr ⟨valid, Or.inr ?_⟩
      rcases sourcePositive.2 with rfl | cover
      · exact selected_root_covers (Bool.eq_false_iff.mpr nonempty)
          (Bool.eq_false_iff.mpr noNegative)
      · exact selected_covers cover

theorem normalizeEntries_pos {classes : ClassTable} (classesWF : classes.WellFormed)
    {fuel : Nat} {name : ClassName} {entries : List Entry} {path : Path}
    (known : Pos classes ⟨name, normalizeEntries classes fuel name entries⟩ path) :
    Pos classes ⟨name, entries⟩ path := by
  induction fuel generalizing name entries path with
  | zero =>
    rw [normalizeEntries] at known
    split at known
    next whole =>
      obtain ⟨valid, _⟩ := pos_iff.mp known
      exact pos_iff.mpr ⟨valid, Or.inr ⟨.positive [], List.contains_iff_mem.mp whole,
        Or.inr ⟨[], rfl, by simp⟩⟩⟩
    next =>
      split at known
      · exact known
      next declaration found =>
        split at known
        next empty =>
          have emptyFields := List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp empty).1
          cases path with
          | nil => exact Pos.root _ _
          | cons field rest =>
            have valid := known.valid
            simp [classAt, found, emptyFields] at valid
        · exact known
  | succ fuel ih =>
    rw [normalizeEntries] at known
    split at known
    next whole =>
      obtain ⟨valid, _⟩ := pos_iff.mp known
      exact pos_iff.mpr ⟨valid, Or.inr ⟨.positive [], List.contains_iff_mem.mp whole,
        Or.inr ⟨[], rfl, by simp⟩⟩⟩
    next =>
      split at known
      · exact known
      next declaration found =>
        split at known
        next empty =>
          have emptyFields := List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp empty).1
          cases path with
          | nil => exact Pos.root _ _
          | cons field rest =>
            have valid := known.valid
            simp [classAt, found, emptyFields] at valid
        next =>
          dsimp only at known
          have distinct := (classesWF.2 (name, declaration) (lookup_mem found)).1
          cases path with
          | nil => exact Pos.root _ _
          | cons field rest =>
            split at known
            next complete =>
              have valid := known.valid
              have allChildren := (Bool.and_eq_true_iff.mp complete).2
              cases targetFound : declaration.fields.lookup field with
              | none => simp [classAt, found, targetFound] at valid
              | some target =>
                have child : Entry.positive [field] ∈
                    normalizeChildren classes fuel declaration.fields entries := by
                  exact List.contains_iff_mem.mp
                    (List.all_eq_true.mp allChildren (field, target) (lookup_mem targetFound))
                exact children_sound (fun _ _ _ h => ih h) found distinct valid
                  ⟨.positive [field], child, Or.inr ⟨[field], rfl, by simp⟩⟩
            next =>
              obtain ⟨valid, impossible | cover⟩ := pos_iff.mp known
              · contradiction
              · exact children_sound (fun _ _ _ h => ih h) found distinct valid cover

theorem normalize_pos {classes : ClassTable} (classesWF : classes.WellFormed)
    {ty : ViewType} {path : Path}
    (known : Pos classes (normalize classes ty) path) : Pos classes ty path := by
  exact normalizeEntries_pos classesWF known

theorem classAt_append (classes : ClassTable) (name : ClassName) (initialPath path : Path) :
    classAt classes name (initialPath ++ path) =
      (classAt classes name initialPath).bind (fun target => classAt classes target path) := by
  induction initialPath generalizing name with
  | nil => rfl
  | cons field rest ih =>
    simp only [List.cons_append, classAt]
    cases classes.lookup name with
    | none => rfl
    | some declaration =>
      cases fieldFound : declaration.fields.lookup field with
      | none => simp [fieldFound]
      | some target => simpa [fieldFound] using ih target

theorem selected_covers_general {entries : List Entry} {initialPath path : Path}
    (cover : Covers (entries.filterMap (Entry.dropPrefix initialPath)) path) :
    Covers entries (initialPath ++ path) := by
  obtain ⟨entry, member, h⟩ := cover
  obtain ⟨source, member, selected⟩ := List.mem_filterMap.mp member
  have eq := Entry.dropPrefix_eq_some selected
  subst source
  refine ⟨entry.prepend initialPath, member, ?_⟩
  rcases h with ⟨pre, len⟩ | ⟨p, rfl, pre⟩
  · exact Or.inl ⟨by simpa using pre, by simpa using len⟩
  · exact Or.inr ⟨initialPath ++ p, rfl, by simpa using pre⟩

theorem selected_pos {classes : ClassTable} {ty : ViewType} {initialPath path : Path}
    {target : ClassName}
    (initialPositive : Pos classes ty initialPath)
    (atClass : classAt classes ty.className initialPath = some target)
    (known : Pos classes ⟨target, ty.entries.filterMap (Entry.dropPrefix initialPath)⟩ path) :
    Pos classes ty (initialPath ++ path) := by
  obtain ⟨valid, root | cover⟩ := pos_iff.mp known
  · subst path; simpa using initialPositive
  · refine pos_iff.mpr ⟨?_, Or.inr (selected_covers_general cover)⟩
    simpa [classAt_append, atClass] using valid

theorem selected_neg {ty : ViewType} {initialPath path : Path} {target : ClassName}
    (known : Neg ⟨target, ty.entries.filterMap (Entry.dropPrefix initialPath)⟩ path) :
    Neg ty (initialPath ++ path) := by
  obtain ⟨entry, member, selected⟩ := List.mem_filterMap.mp (List.contains_iff_mem.mp known)
  have eq := Entry.dropPrefix_eq_some selected
  exact List.contains_iff_mem.mpr (by simpa [eq, Entry.prepend] using member)

theorem positive_entry_descendant {classes : ClassTable} {ty : ViewType} {initialPath path : Path}
    (member : Entry.positive initialPath ∈ ty.entries) (pre : initialPath <+: path)
    (valid : (classAt classes ty.className path).isSome = true) : Pos classes ty path := by
  exact pos_iff.mpr ⟨valid, Or.inr ⟨_, member, Or.inr ⟨_, rfl, pre⟩⟩⟩

structure FocusObservations (classes : ClassTable) (source : ViewType) (initialPath : Path)
    (result : ViewType) : Prop where
  positive : Pos classes source initialPath
  className : classAt classes source.className initialPath = some result.className
  positives : ∀ path, Pos classes result path → Pos classes source (initialPath ++ path)
  negatives : ∀ path, Neg result path → Neg source (initialPath ++ path)

theorem focus_observations {classes : ClassTable} (classesWF : classes.WellFormed)
    {ty result : ViewType} {initialPath : Path}
    (normal : Normalized classes ty)
    (focused : focus classes ty initialPath = some result) :
    FocusObservations classes ty initialPath result := by
  unfold focus at focused
  split at focused
  · simp at focused
  · dsimp only at focused
    rw [normal] at focused
    split at focused
    · simp at focused
    next known =>
      have positive : Pos classes ty initialPath := by
        unfold Pos
        simpa using known
      cases found : classAt classes ty.className initialPath with
      | none => simp [found] at focused
      | some target =>
        simp only [found] at focused
        split at focused
        next root =>
          have root := List.isEmpty_iff.mp root
          subst initialPath
          have focused := Option.some.inj focused
          subst result
          exact ⟨positive, rfl, fun _ h => h, fun _ h => h⟩
        next =>
          split at focused
          next whole =>
            have focused := Option.some.inj focused
            subst result
            refine ⟨positive, found, ?_, ?_⟩
            · intro path known
              obtain ⟨entry, member, pre⟩ := List.any_eq_true.mp whole
              cases entry with
              | negative p => contradiction
              | positive p =>
                have pre := List.isPrefixOf_iff_prefix.mp pre
                obtain ⟨tail, eq⟩ := pre
                apply positive_entry_descendant member
                · exact ⟨tail ++ path, (List.append_assoc p tail path).symm.trans (congrArg (· ++ path) eq)⟩
                · simpa [classAt_append, found, ViewType.whole] using known.valid
            · intro path impossible
              simp [Neg, negative, ViewType.whole] at impossible
          next =>
            have focused := Option.some.inj focused
            subst result
            refine ⟨positive, found, ?_, ?_⟩
            · intro path known
              exact selected_pos positive found (normalize_pos classesWF known)
            · intro path known
              exact selected_neg (normalize_neg known)

theorem classAt_prefix_valid {classes : ClassTable} {name : ClassName} {initialPath path : Path}
    (pre : initialPath <+: path) (valid : (classAt classes name path).isSome = true) :
    (classAt classes name initialPath).isSome = true := by
  obtain ⟨rest, rfl⟩ := pre
  rw [classAt_append] at valid
  cases found : classAt classes name initialPath <;> simp_all

theorem Pos.prefix {classes : ClassTable} {ty : ViewType} {initialPath path : Path}
    (known : Pos classes ty path) (pre : initialPath <+: path) :
    Pos classes ty initialPath := by
  obtain ⟨valid, root | ⟨entry, member, covered⟩⟩ := pos_iff.mp known
  · subst path
    have : initialPath = [] := by simpa using pre
    subst initialPath; exact Pos.root _ _
  · refine pos_iff.mpr ⟨classAt_prefix_valid pre valid, ?_⟩
    right
    refine ⟨entry, member, ?_⟩
    rcases covered with ⟨entryPrefix, lt⟩ | ⟨entryPath, rfl, entryPrefix⟩
    · exact Or.inl ⟨pre.trans entryPrefix, Nat.lt_of_le_of_lt pre.length_le lt⟩
    · rcases List.prefix_or_prefix_of_prefix pre entryPrefix with h | h
      · by_cases same : initialPath = entryPath
        · subst initialPath; exact Or.inr ⟨entryPath, rfl, by simp⟩
        · exact Or.inl ⟨h, Nat.lt_of_le_of_ne h.length_le (by
            intro eq; exact same (h.eq_of_length eq))⟩
      · exact Or.inr ⟨entryPath, rfl, h⟩

theorem remainingAfterMove_entries {classes : ClassTable} {name : ClassName} {path : Path}
    {entry : Entry} (member : entry ∈ remainingAfterMove classes name path) :
    ∃ sibling, entry = .positive sibling ∧ ¬path <+: sibling ∧ ¬sibling <+: path := by
  induction path generalizing name entry with
  | nil => simp [remainingAfterMove] at member
  | cons field rest ih =>
    rw [remainingAfterMove] at member
    split at member
    · simp at member
    next declaration found =>
      obtain ⟨⟨other,target⟩, _, member⟩ := List.mem_flatMap.mp member
      dsimp only at member
      split at member
      next same =>
        have same := beq_iff_eq.mp same
        subst other
        obtain ⟨source, sourceMember, eq⟩ := List.mem_map.mp member
        subst entry
        obtain ⟨sibling, rfl, left, right⟩ := ih sourceMember
        exact ⟨field :: sibling, rfl, by simpa using left, by simpa using right⟩
      next different =>
        have different : other ≠ field := by simpa using different
        have eq := List.mem_singleton.mp member
        subst entry
        exact ⟨[other], rfl, by simp [Ne.symm different], by simp [different]⟩

theorem positive_entry_related {classes : ClassTable} {ty : ViewType} {initialPath path : Path}
    (member : Entry.positive initialPath ∈ ty.entries)
    (related : initialPath <+: path ∨ path <+: initialPath)
    (valid : (classAt classes ty.className path).isSome = true) : Pos classes ty path := by
  rcases related with pre | pre
  · exact positive_entry_descendant member pre valid
  · by_cases same : path = initialPath
    · subst path; exact positive_entry_descendant member (by simp) valid
    · exact pos_iff.mpr ⟨valid, Or.inr ⟨_, member,
        Or.inl ⟨pre, Nat.lt_of_le_of_ne pre.length_le (by
          intro eq; exact same (pre.eq_of_length eq))⟩⟩⟩

private def moveRetained (classes : ClassTable) (ty : ViewType) (path : Path) : List Entry :=
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

private theorem covers_avoids {entry : Entry} {target path : Path}
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

private theorem retained_covers {classes : ClassTable} {ty : ViewType} {target path : Path}
    (valid : (classAt classes ty.className path).isSome = true)
    (cover : Covers (moveRetained classes ty target) path) :
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

private theorem retained_negative {classes : ClassTable} {ty : ViewType} {target path : Path}
    (member : Entry.negative path ∈ moveRetained classes ty target) :
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

structure EmptyObservations (classes : ClassTable) (source : ViewType) (target : Path)
    (result : ViewType) : Prop where
  positive : Pos classes source target
  nonempty : target ≠ []
  className : result.className = source.className
  positives : ∀ path, Pos classes result path → Pos classes source path ∧ ¬target <+: path
  negatives : ∀ path, Neg result path → path = target ∨ (Neg source path ∧ ¬target <+: path)

theorem emptyPath_observations {classes : ClassTable} (classesWF : classes.WellFormed)
    {ty result : ViewType} {target : Path} (normal : Normalized classes ty)
    (emptied : emptyPath classes ty target = some result) :
    EmptyObservations classes ty target result := by
  unfold emptyPath at emptied
  split at emptied
  · contradiction
  next allowed =>
    dsimp only at emptied
    rw [normal] at emptied
    split at emptied
    · contradiction
    next known =>
      have focused : Pos classes ty target := by simpa [Pos] using known
      have nonempty : target ≠ [] := by
        intro eq
        simp [eq] at allowed
      have eq := Option.some.inj emptied
      subst result
      refine ⟨focused, nonempty, rfl, ?_, ?_⟩
      · intro path known
        have raw := normalize_pos classesWF known
        obtain ⟨valid, root | ⟨entry, member, covered⟩⟩ := pos_iff.mp raw
        · subst path
          exact ⟨Pos.root _ _, by simpa using nonempty⟩
        · rcases List.mem_append.mp member with member | member
          · exact retained_covers valid ⟨entry, member, covered⟩
          · have eq := List.mem_singleton.mp member
            subst entry
            rcases covered with ⟨pre, lt⟩ | ⟨_, impossible, _⟩
            · exact ⟨focused.prefix pre, fun reverse =>
                Nat.not_lt_of_ge reverse.length_le lt⟩
            · contradiction
      · intro path known
        have raw := normalize_neg known
        rcases List.mem_append.mp (List.contains_iff_mem.mp raw) with member | member
        · exact Or.inr (retained_negative member)
        · exact Or.inl (Entry.negative.inj (List.mem_singleton.mp member))

end Dada.Unique.Typing
