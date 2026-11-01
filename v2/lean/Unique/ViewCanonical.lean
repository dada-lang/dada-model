import Unique.ViewSoundness

namespace Dada.Unique.Typing

def IncomparableEntries (left right : Entry) : Prop :=
  ¬left.path <+: right.path ∧ ¬right.path <+: left.path

theorem entriesDisjoint_iff_pairwise (entries : List Entry) :
    entriesDisjoint entries = true ↔ entries.Pairwise IncomparableEntries := by
  induction entries with
  | nil => simp [entriesDisjoint]
  | cons entry rest ih =>
    simp [entriesDisjoint, List.pairwise_cons, ← ih,
      List.all_eq_true, IncomparableEntries, Bool.eq_false_iff, List.isPrefixOf_iff_prefix]

theorem prefix_cons_iff {field other : FieldName} {left right : Path} :
    field :: left <+: other :: right ↔ field = other ∧ left <+: right := by
  rw [← List.isPrefixOf_iff_prefix]
  simp only [List.isPrefixOf_cons_cons, Bool.and_eq_true, beq_iff_eq,
    List.isPrefixOf_iff_prefix]

theorem selected_disjoint {entries : List Entry} (disjoint : entriesDisjoint entries = true)
    (field : FieldName) : entriesDisjoint (entries.filterMap (Entry.dropPrefix [field])) = true := by
  apply (entriesDisjoint_iff_pairwise _).mpr
  apply List.Pairwise.filterMap (Entry.dropPrefix [field]) _
    ((entriesDisjoint_iff_pairwise _).mp disjoint)
  intro original other incomparable selected found selectedOther foundOther
  have firstEq := Entry.dropPrefix_eq_some found
  have secondEq := Entry.dropPrefix_eq_some foundOther
  simpa [IncomparableEntries, firstEq, secondEq, prefix_cons_iff] using incomparable

theorem prepended_disjoint {entries : List Entry} (disjoint : entriesDisjoint entries = true)
    (field : FieldName) : entriesDisjoint (entries.map (Entry.prepend [field])) = true := by
  apply (entriesDisjoint_iff_pairwise _).mpr
  apply List.Pairwise.map (Entry.prepend [field]) _ ((entriesDisjoint_iff_pairwise _).mp disjoint)
  intro left right incomparable
  simpa [IncomparableEntries, prefix_cons_iff] using incomparable

theorem selected_valid {classes : ClassTable} {name : ClassName} {entries : List Entry}
    (valid : entries.all (Entry.valid classes name) = true)
    (fieldLookup : classAt classes name [field] = some target)
    (noRoot : Entry.negative [] ∉ entries.filterMap (Entry.dropPrefix [field])) :
    (entries.filterMap (Entry.dropPrefix [field])).all (Entry.valid classes target) = true := by
  apply List.all_eq_true.mpr
  intro entry selected
  obtain ⟨original, member, dropped⟩ := List.mem_filterMap.mp selected
  have eq := Entry.dropPrefix_eq_some dropped
  have originalValid := List.all_eq_true.mp valid original member
  have validPath : (classAt classes target entry.path).isSome = true := by
    have pathValid := (Bool.and_eq_true_iff.mp originalValid).1
    rw [eq, Entry.path_prepend, classAt_append, fieldLookup] at pathValid
    exact pathValid
  cases entry with
  | positive path => simpa [Entry.valid, Entry.path] using validPath
  | negative path =>
    have nonempty : path ≠ [] := by
      intro empty
      subst path
      exact noRoot (List.mem_filterMap.mpr ⟨original, member, dropped⟩)
    simp only [Entry.path] at validPath
    simp [Entry.valid, Entry.path, validPath, nonempty]

theorem prepended_valid {classes : ClassTable} {name target : ClassName} {entries : List Entry}
    (valid : entries.all (Entry.valid classes target) = true)
    (fieldLookup : classAt classes name [field] = some target) :
    (entries.map (Entry.prepend [field])).all (Entry.valid classes name) = true := by
  apply List.all_eq_true.mpr
  intro entry member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  have originalValid := List.all_eq_true.mp valid original present
  have validPath : (classAt classes name ([field] ++ original.path)).isSome = true := by
    rw [classAt_append, fieldLookup]
    exact (Bool.and_eq_true_iff.mp originalValid).1
  cases original <;> simpa [Entry.valid, Entry.prepend, Entry.path] using validPath

private theorem lookup_member {K V : Type} [BEq K] [LawfulBEq K]
    {entries : List (K × V)} {key : K} {value : V}
    (found : entries.lookup key = some value) : (key, value) ∈ entries := by
  obtain ⟨before, after, rfl, _⟩ := List.lookup_eq_some_iff.mp found
  simp

private theorem lookup_unique_member {K V : Type} [BEq K] [LawfulBEq K]
    {entries : List (K × V)} {key : K} {value : V}
    (unique : (entries.map Prod.fst).Nodup) (member : (key, value) ∈ entries) :
    entries.lookup key = some value := by
  induction entries with
  | nil => simp at member
  | cons entry rest ih =>
    rcases entry with ⟨head, data⟩
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with same | later
    · cases same; simp
    · have different : key ≠ head := by
        intro same
        exact unique.1 (List.mem_map.mpr ⟨_, later, same⟩)
      rw [List.lookup_cons, show (key == head) = false from beq_eq_false_iff_ne.mpr different]
      exact ih unique.2 later

def normalizedChild (classes : ClassTable) (fuel : Nat) (entries : List Entry)
    (field : FieldName × ClassName) : List Entry :=
  let selected := entries.filterMap (Entry.dropPrefix [field.1])
  if selected.isEmpty then []
  else if selected.contains (.negative []) then [.negative [field.1]]
  else (normalizeEntries classes fuel field.2 selected).map (Entry.prepend [field.1])

theorem normalizedChild_prefix (classes : ClassTable) (fuel : Nat) (entries : List Entry)
    (field : FieldName × ClassName) (entry : Entry)
    (member : entry ∈ normalizedChild classes fuel entries field) :
    ∃ path, entry.path = field.1 :: path := by
  unfold normalizedChild at member
  dsimp only at member
  split at member
  · simp at member
  · split at member
    · simp only [List.mem_singleton] at member
      subst entry
      exact ⟨[], rfl⟩
    · obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
      exact ⟨original.path, Entry.path_prepend _ _⟩

theorem children_disjoint {fields : List (FieldName × ClassName)}
    (unique : (fields.map Prod.fst).Nodup)
    (each : ∀ field ∈ fields,
      entriesDisjoint (normalizedChild classes fuel entries field) = true) :
    entriesDisjoint (fields.flatMap (normalizedChild classes fuel entries)) = true := by
  apply (entriesDisjoint_iff_pairwise _).mpr
  apply List.pairwise_flatMap.mpr
  constructor
  · intro field member
    exact (entriesDisjoint_iff_pairwise _).mp (each field member)
  · have names := List.pairwise_map.mp unique
    apply names.imp
    intro left right different leftEntry leftMember rightEntry rightMember
    obtain ⟨leftPath, leftEq⟩ := normalizedChild_prefix _ _ _ _ _ leftMember
    obtain ⟨rightPath, rightEq⟩ := normalizedChild_prefix _ _ _ _ _ rightMember
    simp only [IncomparableEntries, leftEq, rightEq, prefix_cons_iff]
    exact ⟨fun both => different both.1, fun both => different both.1.symm⟩

theorem normalizeEntries_wellFormed {classes : ClassTable} (classesWF : classes.WellFormed)
    (fuel : Nat) {name : ClassName} {entries : List Entry}
    (declared : (classes.lookup name).isSome = true)
    (valid : entries.all (Entry.valid classes name) = true)
    (disjoint : entriesDisjoint entries = true) :
    (normalizeEntries classes fuel name entries).all (Entry.valid classes name) = true ∧
      entriesDisjoint (normalizeEntries classes fuel name entries) = true := by
  induction fuel generalizing name entries with
  | zero =>
    rw [normalizeEntries]
    split
    · simp [Entry.valid, Entry.path, classAt, entriesDisjoint]
    · split
      · exact ⟨valid, disjoint⟩
      · split
        · simp [Entry.valid, Entry.path, classAt, entriesDisjoint]
        · exact ⟨valid, disjoint⟩
  | succ fuel ih =>
    rw [normalizeEntries]
    split
    · simp [Entry.valid, Entry.path, classAt, entriesDisjoint]
    · split
      · exact ⟨valid, disjoint⟩
      next declaration found =>
        split
        · simp [Entry.valid, Entry.path, classAt, entriesDisjoint]
        · dsimp only
          have declarationMember := lookup_member found
          have fieldsWF := classesWF.2 _ declarationMember
          have each : ∀ field ∈ declaration.fields,
              (normalizedChild classes fuel entries field).all (Entry.valid classes name) = true ∧
              entriesDisjoint (normalizedChild classes fuel entries field) = true := by
            intro field member
            rcases field with ⟨field, target⟩
            have fieldFound := lookup_unique_member fieldsWF.1 member
            have fieldClass : classAt classes name [field] = some target := by
              simp [classAt, found, fieldFound]
            obtain ⟨⟨_, targetDeclaration⟩, targetMember, targetEq⟩ :=
              List.mem_map.mp (fieldsWF.2 _ member)
            simp only at targetEq
            subst targetEq
            have targetFound := lookup_unique_member classesWF.1 targetMember
            unfold normalizedChild
            dsimp only
            split
            · simp [entriesDisjoint]
            · split
              · simp [Entry.valid, Entry.path, fieldClass, entriesDisjoint]
              next noRoot =>
                have child := ih (by simp [targetFound])
                  (selected_valid valid fieldClass
                    (fun root => noRoot (List.contains_iff_mem.mpr root)))
                  (selected_disjoint disjoint field)
                exact ⟨prepended_valid child.1 fieldClass, prepended_disjoint child.2 field⟩
          have childrenWF :
              (declaration.fields.flatMap (normalizedChild classes fuel entries)).all
                (Entry.valid classes name) = true ∧
              entriesDisjoint (declaration.fields.flatMap (normalizedChild classes fuel entries)) = true := by
            constructor
            · apply List.all_eq_true.mpr
              intro entry present
              obtain ⟨field, member, childMember⟩ := List.mem_flatMap.mp present
              exact List.all_eq_true.mp (each field member).1 entry childMember
            · exact children_disjoint fieldsWF.1 (fun field member => (each field member).2)
          split
          · simp [Entry.valid, Entry.path, classAt, entriesDisjoint]
          · exact childrenWF

theorem normalize_wellFormed {classes : ClassTable} (classesWF : classes.WellFormed)
    {ty : ViewType} (wf : ty.WellFormed classes) : (normalize classes ty).WellFormed classes := by
  refine ⟨wf.1, ?_⟩
  exact normalizeEntries_wellFormed classesWF _ wf.1 wf.2.1 wf.2.2

private theorem flatMap_congr_member {A B : Type} {entries : List A} {left right : A → List B}
    (same : ∀ entry ∈ entries, left entry = right entry) : entries.flatMap left = entries.flatMap right := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.flatMap_cons, same entry (by simp)]
    rw [ih (fun member present => same member (List.mem_cons_of_mem _ present))]

theorem normalizeEntries_permutation {classes : ClassTable} (classesWF : classes.WellFormed)
    (fuel : Nat) {name : ClassName} {entries other : List Entry}
    (declared : (classes.lookup name).isSome = true)
    (permutation : entries.Perm other)
    (bounded : ∀ entry ∈ entries, entry.path.length < fuel) :
    normalizeEntries classes fuel name entries = normalizeEntries classes fuel name other := by
  induction fuel generalizing name entries other with
  | zero =>
    have empty : entries = [] := by
      cases entries with
      | nil => rfl
      | cons entry rest => have impossible := bounded entry (by simp); omega
    subst entries
    have otherEmpty : other = [] := List.length_eq_zero_iff.mp (by simpa using permutation.length_eq.symm)
    subst other
    rfl
  | succ fuel ih =>
    rw [normalizeEntries, normalizeEntries]
    rw [← permutation.contains_eq (a := .positive [])]
    split
    · rfl
    · cases found : classes.lookup name with
      | none => simp [found] at declared
      | some declaration =>
        simp only
        rw [← permutation.isEmpty_eq]
        split
        · rfl
        · have declarationMember := lookup_member found
          have fieldsWF := classesWF.2 _ declarationMember
          have childrenEq : declaration.fields.flatMap (normalizedChild classes fuel entries) =
              declaration.fields.flatMap (normalizedChild classes fuel other) := by
            apply flatMap_congr_member
            intro field member
            rcases field with ⟨field,target⟩
            have selectedPerm := permutation.filterMap (Entry.dropPrefix [field])
            unfold normalizedChild
            dsimp only
            rw [← selectedPerm.isEmpty_eq, ← selectedPerm.contains_eq (a := .negative [])]
            split
            · rfl
            · split
              · rfl
              · congr 1
                apply ih
                · obtain ⟨⟨_, targetDeclaration⟩, targetMember, same⟩ := List.mem_map.mp (fieldsWF.2 _ member)
                  simp only at same
                  subst same
                  simp [lookup_unique_member classesWF.1 targetMember]
                · exact selectedPerm
                · intro entry selected
                  obtain ⟨original, present, dropped⟩ := List.mem_filterMap.mp selected
                  have eq := Entry.dropPrefix_eq_some dropped
                  have bound := bounded original present
                  rw [eq, Entry.path_prepend] at bound
                  simpa using bound
          change (let children := declaration.fields.flatMap (normalizedChild classes fuel entries)
                  if !declaration.fields.isEmpty && declaration.fields.all
                    (fun field => children.contains (.positive [field.1])) then [.positive []] else children) =
            (let children := declaration.fields.flatMap (normalizedChild classes fuel other)
             if !declaration.fields.isEmpty && declaration.fields.all
               (fun field => children.contains (.positive [field.1])) then [.positive []] else children)
          rw [childrenEq]

theorem entryDepth_bounds (entries : List Entry) (initial : Nat) :
    initial ≤ entries.foldl (fun depth entry => max depth entry.path.length) initial ∧
      ∀ entry ∈ entries, entry.path.length ≤
        entries.foldl (fun depth entry => max depth entry.path.length) initial := by
  induction entries generalizing initial with
  | nil => simp
  | cons entry rest ih =>
    obtain ⟨start, bounds⟩ := ih (max initial entry.path.length)
    constructor
    · exact Nat.le_trans (Nat.le_max_left _ _) start
    · intro other member
      rcases List.mem_cons.mp member with rfl | later
      · exact Nat.le_trans (Nat.le_max_right _ _) start
      · exact bounds other later

theorem entryDepth_permutation {entries other : List Entry} (permutation : entries.Perm other)
    (initial : Nat) :
    entries.foldl (fun depth entry => max depth entry.path.length) initial =
      other.foldl (fun depth entry => max depth entry.path.length) initial := by
  induction permutation generalizing initial with
  | nil => rfl
  | cons entry _ ih => exact ih _
  | swap left right rest => simp [Nat.max_assoc, Nat.max_left_comm, Nat.max_comm]
  | trans _ _ first second => exact (first initial).trans (second initial)

theorem normalize_permutation {classes : ClassTable} (classesWF : classes.WellFormed)
    {name : ClassName} {entries other : List Entry}
    (declared : (classes.lookup name).isSome = true) (permutation : entries.Perm other) :
    normalize classes ⟨name, entries⟩ = normalize classes ⟨name, other⟩ := by
  unfold normalize
  dsimp only
  rw [← entryDepth_permutation permutation 0]
  congr 1
  apply normalizeEntries_permutation classesWF _ declared permutation
  intro entry member
  exact Nat.lt_succ_of_le ((entryDepth_bounds entries 0).2 entry member)

end Dada.Unique.Typing
