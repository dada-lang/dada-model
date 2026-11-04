import Unique.TypingHeap
import Unique.TypingEffects

namespace Dada.Unique.Typing

-- Allocation adds a fresh, younger object. Every old path still reads the same slot.
theorem readPath_allocate (wf : WellFormedWith layouts state pending)
    (older : object.index < state.nextId) (path : Path) :
    readPath (state.allocate name fields arguments) object path = readPath state object path := by
  induction path generalizing object with
  | nil =>
    have different : object ≠ ObjectId.mk state.nextId := by
      intro equal; cases equal; exact Nat.lt_irrefl _ older
    simp [readPath, State.allocate, List.lookup_cons, beq_eq_false_iff_ne.mpr different]
  | cons field rest ih =>
    have different : object ≠ ObjectId.mk state.nextId := by
      intro equal; cases equal; exact Nat.lt_irrefl _ older
    simp only [readPath, State.allocate, List.lookup_cons, beq_eq_false_iff_ne.mpr different]
    cases found : state.objects.lookup object with
    | none => simp
    | some data =>
      dsimp only [Bind.bind, Option.bind]
      cases slot : data.fields.lookup field with
      | none => simp
      | some value =>
        dsimp only [Bind.bind, Option.bind]
        cases rest with
        | nil => rfl
        | cons next tail =>
          cases value with
          | none => rfl
          | some target =>
            have allocated := WellFormedWith.field_allocated wf (lookup_member found) (lookup_member slot)
            obtain ⟨⟨_, targetData⟩, targetStored, rfl⟩ := List.mem_map.mp allocated
            exact ih (wf.bounds _ targetData targetStored)

theorem Satisfies.allocate (satisfied : Satisfies classes state object ty)
    (wf : WellFormedWith layouts state pending) :
    Satisfies classes (state.allocate name fields arguments) object ty := by
  obtain ⟨rootData, rootMember, rootClass⟩ := satisfied.root
  have bound := wf.bounds _ _ rootMember
  constructor
  · exact ⟨rootData, List.mem_cons_of_mem _ rootMember, rootClass⟩
  · intro path known
    obtain ⟨target, data, read, member, correct⟩ := satisfied.positive path known
    exact ⟨target, data, (readPath_allocate wf bound path).trans read,
      List.mem_cons_of_mem _ member, correct⟩
  · intro path known
    exact (readPath_allocate wf bound path).trans (satisfied.negative path known)

theorem Realizes.perm (realized : Realizes classes environment state pending)
    (permutation : pending.Perm other) : Realizes classes environment state other := by
  refine { realized with
    pendingTypes := ?_, ownership := realized.ownership.perm (permutation.map Prod.fst),
    pendingValues := ?_ }
  · intro object ty member
    exact realized.pendingTypes object ty (permutation.mem_iff.mpr member)
  · intro object ty member
    exact realized.pendingValues object ty (permutation.mem_iff.mpr member)

theorem Realizes.weaken_pending (realized : Realizes classes environment state ((object, ty) :: pending))
    (admissible : Admissible classes other) (subtype : Subtype classes ty other) :
    Realizes classes environment state ((object, other) :: pending) := by
  have original := realized.pendingTypes object ty (by simp)
  refine { realized with pendingTypes := ?_, pendingValues := ?_ }
  · intro root view member
    rcases List.mem_cons.mp member with equal | member
    · cases equal; exact admissible
    · exact realized.pendingTypes root view (List.mem_cons_of_mem _ member)
  · intro root view member
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      exact (realized.pendingValues object ty (by simp)).weaken original.2 admissible.2 subtype
    · exact realized.pendingValues root view (List.mem_cons_of_mem _ member)

-- Constructor arguments are paired with fields in declaration order.
inductive ArgumentsSatisfy (classes : ClassTable) (state : State) : List (FieldName × ClassName) → List ObjectId → Prop where
  | nil : ArgumentsSatisfy classes state [] []
  | cons {entry : FieldName × ClassName} {object : ObjectId}
      {fields : List (FieldName × ClassName)} {objects : List ObjectId} :
      Satisfies classes state object (.whole entry.2) →
      ArgumentsSatisfy classes state fields objects →
      ArgumentsSatisfy classes state (entry :: fields) (object :: objects)

theorem ArgumentsSatisfy.lookup (arguments : ArgumentsSatisfy classes state fields objects)
    (found : fields.lookup field = some targetClass) :
    ∃ object, ((fields.map Prod.fst).zip (objects.map some)).lookup field = some (some object) ∧
      Satisfies classes state object (.whole targetClass) := by
  induction arguments with
  | nil => simp at found
  | @cons entry object fields objects head tail ih =>
    rcases entry with ⟨name, target⟩
    by_cases same : field = name
    · subst name
      simp at found
      cases found
      exact ⟨object, by simp, head⟩
    · have different := beq_eq_false_iff_ne.mpr same
      simp only [List.lookup_cons, different] at found
      obtain ⟨result, lookup, satisfied⟩ := ih found
      exact ⟨result, by simpa [List.lookup_cons, different] using lookup, satisfied⟩

theorem ArgumentsSatisfy.member (arguments : ArgumentsSatisfy classes state fields objects)
    (stored : (field, some object) ∈ (fields.map Prod.fst).zip (objects.map some)) :
    ∃ targetClass, (field, targetClass) ∈ fields ∧
      Satisfies classes state object (.whole targetClass) := by
  induction arguments with
  | nil => simp at stored
  | @cons entry target fields objects head tail ih =>
    rcases entry with ⟨name, targetClass⟩
    rcases List.mem_cons.mp stored with equal | stored
    · cases equal
      exact ⟨targetClass, by simp, head⟩
    · obtain ⟨targetClass, member, satisfied⟩ := ih stored
      exact ⟨targetClass, List.mem_cons_of_mem _ member, satisfied⟩

theorem Satisfies.allocated_whole
    (classesWf : classes.WellFormed) (declared : (name, declaration) ∈ classes)
    (wf : WellFormedWith classes.erase state pending)
    (arguments : ArgumentsSatisfy classes state declaration.fields objects) :
    Satisfies classes
      (state.allocate name (declaration.fields.map Prod.fst) objects)
      ⟨state.nextId⟩ (.whole name) := by
  let allocated := state.allocate name (declaration.fields.map Prod.fst) objects
  have classLookup := lookup_of_member classesWf.1 declared
  constructor
  · exact ⟨⟨name, (declaration.fields.map Prod.fst).zip (objects.map some)⟩, by simp [State.allocate], rfl⟩
  · intro path positive
    rw [Pos, positive_whole] at positive
    cases path with
    | nil =>
      exact ⟨⟨state.nextId⟩, ⟨name, (declaration.fields.map Prod.fst).zip (objects.map some)⟩, by simp [readPath, State.allocate],
        by simp [State.allocate], rfl⟩
    | cons field rest =>
      simp only [classAt, classLookup] at positive
      dsimp only [Bind.bind, Option.bind] at positive
      cases fieldClass : declaration.fields.lookup field with
      | none => simp [fieldClass] at positive
      | some targetClass =>
        obtain ⟨object, fieldLookup, satisfies⟩ := arguments.lookup fieldClass
        have valid : Pos classes (.whole targetClass) rest := by
          simpa [Pos, positive_whole, fieldClass] using positive
        have preservedSat : Satisfies classes allocated object (.whole targetClass) := satisfies.allocate wf
        have preserved := preservedSat.positive rest valid
        obtain ⟨target', data', read', member', correct'⟩ := preserved
        have result : readPath allocated ⟨state.nextId⟩ (field :: rest) = some (some target') := by
          cases rest with
          | nil =>
            have selfRead := readPath_nil allocated object
            rw [selfRead] at read'
            have equal : target' = object := by
              cases found : allocated.objects.lookup object <;> simp [found] at read'
              exact read'.symm
            subst target'
            simpa [allocated, readPath, State.allocate] using fieldLookup
          | cons next tail =>
            simpa [allocated, readPath, State.allocate, fieldLookup] using read'
        exact ⟨target', data', result, member', by
          simpa [ViewType.whole, classAt, classLookup, fieldClass] using correct'⟩
  · intro path negative
    simp [Neg, negative_whole] at negative

theorem ArgumentsSatisfy.of_pending
    (lengths : objects.length = fields.length)
    (satisfied : ∀ object ty, (object, ty) ∈ objects.zip (fields.map fun field => ViewType.whole field.2) →
      Satisfies classes state object ty) : ArgumentsSatisfy classes state fields objects := by
  induction fields generalizing objects with
  | nil =>
    have : objects = [] := List.length_eq_zero_iff.mp lengths
    subst objects
    exact .nil
  | cons field fields ih =>
    cases objects with
    | nil => simp at lengths
    | cons object objects =>
      apply ArgumentsSatisfy.cons (satisfied object (.whole field.2) (by simp))
      apply ih (by simpa using lengths)
      intro object ty member
      exact satisfied object ty (List.mem_cons_of_mem _ member)

theorem FieldsMatchClasses.allocate (matched : FieldsMatchClasses classes state)
    (declared : (name, declaration) ∈ classes)
    (arguments : ArgumentsSatisfy classes state declaration.fields objects) :
    FieldsMatchClasses classes
      (state.allocate name (declaration.fields.map Prod.fst) objects) := by
  intro parent data field target member stored
  rcases List.mem_cons.mp member with same | old
  · cases same
    obtain ⟨targetClass, typedField, satisfied⟩ := arguments.member stored
    obtain ⟨targetData, targetMember, targetName⟩ := satisfied.root
    exact ⟨declaration, targetClass, targetData, declared, typedField,
      List.mem_cons_of_mem _ targetMember, targetName⟩
  · obtain ⟨decl, targetClass, targetData, declared, typedField, allocated, correct⟩ :=
      matched _ _ _ _ old stored
    exact ⟨decl, targetClass, targetData, declared, typedField,
      List.mem_cons_of_mem _ allocated, correct⟩

theorem Realizes.allocate
    (realized : Realizes classes environment state
      (objects.zip (declaration.fields.map fun field => ViewType.whole field.2) ++ pending))
    (declared : (name, declaration) ∈ classes)
    (admissible : Admissible classes (.whole name))
    (lengths : objects.length = declaration.fields.length) :
    Realizes classes environment
      (state.allocate name (declaration.fields.map Prod.fst) objects)
      ((ObjectId.mk state.nextId, .whole name) :: pending) := by
  have argumentViews : ArgumentsSatisfy classes state declaration.fields objects :=
    ArgumentsSatisfy.of_pending lengths (fun object ty member =>
      realized.pendingValues object ty (List.mem_append_left _ member))
  have owners : WellFormedWith classes.erase state (objects ++ pending.map Prod.fst) := by
    have keys : (objects.zip (declaration.fields.map fun field => ViewType.whole field.2)).map Prod.fst = objects :=
      List.map_fst_zip (by simp [lengths])
    simpa only [List.map_append, keys] using realized.ownership
  have erased : (name, Class.mk (declaration.fields.map Prod.fst)) ∈ classes.erase :=
    List.mem_map.mpr ⟨(name, declaration), declared, rfl⟩
  constructor
  · exact realized.classesWellFormed
  · exact realized.environmentWellFormed
  · intro object ty member
    rcases List.mem_cons.mp member with same | old
    · cases same; exact admissible
    · exact realized.pendingTypes object ty (List.mem_append_right _ old)
  · exact owners.allocate realized.classesWellFormed.erase erased (by simpa using lengths)
  · exact realized.fields.allocate declared argumentViews
  · exact realized.variableDomain
  · exact realized.emptyVariables
  · intro destination ty member
    obtain ⟨object, stored, satisfied⟩ := realized.initializedVariables destination ty member
    exact ⟨object, stored, satisfied.allocate realized.ownership⟩
  · intro object ty member
    rcases List.mem_cons.mp member with same | old
    · cases same
      exact Satisfies.allocated_whole realized.classesWellFormed declared realized.ownership argumentViews
    · exact (realized.pendingValues object ty (List.mem_append_right _ old)).allocate realized.ownership

theorem Realizes.next_fresh (realized : Realizes classes environment state pending) :
    ObjectId.mk state.nextId ∉ state.objects.map Prod.fst := by
  intro member
  obtain ⟨⟨object, data⟩, stored, same⟩ := List.mem_map.mp member
  dsimp at same
  subst object
  exact Nat.lt_irrefl _ (realized.ownership.bounds _ _ stored)

end Dada.Unique.Typing
