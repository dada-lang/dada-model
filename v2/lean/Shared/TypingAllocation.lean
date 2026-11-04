import Shared.TypingRealization
import Shared.TypingEffects
import Shared.TypingViewLemmas

namespace Dada.Shared.Typing

-- Allocation adds a fresh object. Existing references cannot target its unused ID.
theorem readPath_allocate (wf : WellFormedWith layouts state pending)
    (older : reference.object.index < state.nextId) (path : Path) :
    readPath (state.allocate name fields arguments) reference path = readPath state reference path := by
  induction path generalizing reference with
  | nil =>
    have different : reference.object ≠ ObjectId.mk state.nextId := by
      intro equal; exact Nat.ne_of_lt older (congrArg ObjectId.index equal)
    simp [readPath, State.allocate, List.lookup_cons, beq_eq_false_iff_ne.mpr different]
  | cons field rest ih =>
    have different : reference.object ≠ ObjectId.mk state.nextId := by
      intro equal; exact Nat.ne_of_lt older (congrArg ObjectId.index equal)
    simp only [readPath, State.allocate, List.lookup_cons, beq_eq_false_iff_ne.mpr different]
    cases found : state.objects.lookup reference.object with
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
            have allocated := (wf.referencesComplete target.object).mp
              (List.mem_append_right _ (List.mem_append_right _
                (List.mem_flatMap.mpr ⟨(_, data), lookup_member found,
                  List.mem_filterMap.mpr ⟨(field, some target), lookup_member slot, rfl⟩⟩)))
            obtain ⟨⟨id, targetData⟩, member, same⟩ := List.mem_map.mp allocated
            dsimp at same
            subst id
            exact ih (reference := enter reference.mode target) (wf.bounds _ _ member)

theorem Satisfies.allocate (satisfied : Satisfies classes state reference ty)
    (wf : WellFormedWith layouts state pending) :
    Satisfies classes (state.allocate name fields arguments) reference ty := by
  obtain ⟨rootData, rootMember, rootClass⟩ := satisfied.root
  have bound := wf.bounds _ _ rootMember
  constructor
  · exact satisfied.mode
  · exact ⟨rootData, List.mem_cons_of_mem _ rootMember, rootClass⟩
  · intro path known
    obtain ⟨target, data, read, member, correct⟩ := satisfied.positive path known
    exact ⟨target, data, (readPath_allocate wf bound path).trans read,
      List.mem_cons_of_mem _ member, correct⟩
  · intro path known
    exact (readPath_allocate wf bound path).trans (satisfied.negative path known)
  · intro path target permission declared read
    rw [readPath_allocate wf bound path] at read
    exact satisfied.modes path target permission declared read

-- Constructor arguments are paired with fields in declaration order.
inductive ArgumentsSatisfy (classes : ClassTable) (state : State) : List (FieldName × FieldType) → List Reference → Prop where
  | nil : ArgumentsSatisfy classes state [] []
  | cons {entry : FieldName × FieldType} {object : Reference}
      {fields : List (FieldName × FieldType)} {objects : List Reference} :
      Satisfies classes state object entry.2.toType →
      ArgumentsSatisfy classes state fields objects →
      ArgumentsSatisfy classes state (entry :: fields) (object :: objects)

theorem ArgumentsSatisfy.reference {reference : Reference} (arguments : ArgumentsSatisfy classes state fields objects)
    (member : reference ∈ objects) :
    ∃ field ∈ fields, Satisfies classes state reference field.2.toType := by
  induction arguments with
  | nil => simp at member
  | @cons entry object fields objects head tail ih =>
    rcases List.mem_cons.mp member with same | rest
    · subst reference; exact ⟨entry, by simp, head⟩
    · obtain ⟨field, found, sat⟩ := ih rest
      exact ⟨field, List.mem_cons_of_mem _ found, sat⟩

theorem ArgumentsSatisfy.lookup (arguments : ArgumentsSatisfy classes state fields objects)
    (found : fields.lookup field = some targetClass) :
    ∃ object, ((fields.map Prod.fst).zip (objects.map some)).lookup field = some (some object) ∧
      Satisfies classes state object targetClass.toType := by
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
      Satisfies classes state object targetClass.toType := by
  induction arguments with
  | nil => simp at stored
  | @cons entry target fields objects head tail ih =>
    rcases entry with ⟨name, targetClass⟩
    rcases List.mem_cons.mp stored with equal | stored
    · cases equal
      exact ⟨targetClass, by simp, head⟩
    · obtain ⟨targetClass, member, satisfied⟩ := ih stored
      exact ⟨targetClass, List.mem_cons_of_mem _ member, satisfied⟩

private theorem allocated_read_cons
    (wf : WellFormedWith classes state pending)
    (root : (reference.object, data) ∈ state.objects)
    (fieldFound : (fields.zip (arguments.map some)).lookup field = some (some reference))
    (rest : Path) :
    readPath (state.allocate name fields arguments) (.owned ⟨state.nextId⟩) (field :: rest) =
      readPath (state.allocate name fields arguments) reference rest := by
  cases rest with
  | nil =>
    rw [readPath_allocate wf (wf.bounds _ _ root)]
    simp [readPath, State.allocate, Reference.owned, fieldFound,
      lookup_of_member wf.objectKeys root]
  | cons next tail => simp [readPath, State.allocate, Reference.owned, fieldFound]

theorem Satisfies.allocated_whole
    (classesWf : classes.WellFormed) (declared : (name, declaration) ∈ classes)
    (wf : WellFormedWith classes.erase state pending)
    (arguments : ArgumentsSatisfy classes state declaration.fields objects) :
    Satisfies classes
      (state.allocate name (declaration.fields.map Prod.fst) objects)
      (.owned ⟨state.nextId⟩) (.whole name) := by
  let allocated := state.allocate name (declaration.fields.map Prod.fst) objects
  have classLookup := lookup_of_member classesWf.1 declared
  constructor
  · rfl
  · exact ⟨⟨name, (declaration.fields.map Prod.fst).zip (objects.map some)⟩,
      by simp [State.allocate, Reference.owned], rfl⟩
  · intro path positive
    change Unique.Typing.Pos classes.nominal (.whole name) path at positive
    rw [Unique.Typing.Pos, Unique.Typing.positive_whole] at positive
    cases path with
    | nil =>
      exact ⟨.owned ⟨state.nextId⟩,
        ⟨name, (declaration.fields.map Prod.fst).zip (objects.map some)⟩,
        by simp [readPath, State.allocate, Reference.owned],
        by simp [State.allocate, Reference.owned], rfl⟩
    | cons field rest =>
      cases fieldClass : declaration.fields.lookup field with
      | none =>
        simp [Unique.Typing.classAt, ClassTable.nominal_lookup, nominal_field_lookup,
          classLookup, fieldClass] at positive
      | some targetClass =>
        obtain ⟨reference, fieldLookup, satisfies⟩ := arguments.lookup fieldClass
        have valid : Pos classes targetClass.toType rest := by
          simpa [Pos, FieldType.toType, ValueType.whole, Unique.Typing.Pos,
            Unique.Typing.positive_whole, Unique.Typing.classAt,
            ClassTable.nominal_lookup, nominal_field_lookup, classLookup, fieldClass] using positive
        have preservedSat : Satisfies classes allocated reference targetClass.toType :=
          satisfies.allocate wf
        obtain ⟨target, data, read, member, correct⟩ := preservedSat.positive rest valid
        obtain ⟨rootData, rootMember, _⟩ := satisfies.root
        refine ⟨target, data, ?_, member, ?_⟩
        · exact (allocated_read_cons wf rootMember fieldLookup rest).trans read
        · simpa [ValueType.whole, Unique.Typing.ViewType.whole, Unique.Typing.classAt,
            ClassTable.nominal_lookup, nominal_field_lookup, classLookup, fieldClass,
            FieldType.toType] using correct
  · intro path negative
    simp [Neg, ValueType.whole, Unique.Typing.Neg, Unique.Typing.negative_whole] at negative
  · intro path target permission declaredPath read
    cases path with
    | nil =>
      have samePermission : permission = .given := (Option.some.inj declaredPath).symm
      have sameTarget : target = .owned ⟨state.nextId⟩ := by
        simpa [readPath, State.allocate, Reference.owned] using read.symm
      subst target permission
      rfl
    | cons field rest =>
      cases fieldClass : declaration.fields.lookup field with
      | none => simp [declaredPermission, classLookup, fieldClass,
          ValueType.whole, Unique.Typing.ViewType.whole] at declaredPath
      | some targetClass =>
        have declaredRest : ∃ inner,
            declaredPermission classes targetClass.className rest = some inner ∧
            permission = targetClass.permission.comp inner := by
          have relation : (declaredPermission classes targetClass.className rest).bind
              (fun inner => some (targetClass.permission.comp inner)) = some permission := by
            simpa [declaredPermission, classLookup, fieldClass, ValueType.whole,
              Unique.Typing.ViewType.whole] using declaredPath
          obtain ⟨inner, found, same⟩ := Option.bind_eq_some_iff.mp relation
          exact ⟨inner, found, (Option.some.inj same).symm⟩
        obtain ⟨inner, declaredRest, rfl⟩ := declaredRest
        obtain ⟨reference, fieldLookup, satisfies⟩ := arguments.lookup fieldClass
        obtain ⟨rootData, rootMember, _⟩ := satisfies.root
        have childRead : readPath allocated reference rest = some (some target) :=
          (allocated_read_cons wf rootMember fieldLookup rest).symm.trans read
        have matched := (satisfies.allocate wf).modes rest target inner declaredRest childRead
        simpa [ValueType.whole, FieldType.toType, Perm.comp_given_left] using matched

theorem ArgumentsSatisfy.of_pending
    (lengths : objects.length = fields.length)
    (satisfied : ∀ object ty, (object, ty) ∈ objects.zip (fields.map fun field => field.2.toType) →
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
      apply ArgumentsSatisfy.cons (satisfied object field.2.toType (by simp))
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
      (objects.zip (declaration.fields.map fun field => field.2.toType) ++ pending))
    (declared : (name, declaration) ∈ classes)
    (admissible : Admissible classes (.whole name (initialPermission declaration.kind)))
    (lengths : objects.length = declaration.fields.length) :
    Realizes classes environment
      (state.allocate name (declaration.fields.map Prod.fst) objects)
      ((⟨declaration.kind.mode, ⟨state.nextId⟩⟩, .whole name (initialPermission declaration.kind)) :: pending) := by
  have argumentViews : ArgumentsSatisfy classes state declaration.fields objects :=
    ArgumentsSatisfy.of_pending lengths (fun object ty member =>
      realized.pendingValues object ty (List.mem_append_left _ member))
  have owners : WellFormedWith classes.erase state (objects ++ pending.map Prod.fst) := by
    have keys : (objects.zip (declaration.fields.map fun field => field.2.toType)).map Prod.fst = objects :=
      List.map_fst_zip (by simp [lengths])
    simpa only [List.map_append, keys] using realized.ownership
  have erased : (name, Class.mk (declaration.fields.map Prod.fst) declaration.kind) ∈ classes.erase :=
    List.mem_map.mpr ⟨(name, declaration), declared, rfl⟩
  constructor
  · exact realized.classesWellFormed
  · exact realized.environmentWellFormed
  · intro object ty member
    rcases List.mem_cons.mp member with same | old
    · cases same; exact admissible
    · exact realized.pendingTypes object ty (List.mem_append_right _ old)
  · have allocated := owners.allocate realized.classesWellFormed.erase erased (by simpa using lengths) realized.next_fresh
    cases declaration.kind with
    | classType => exact allocated
    | structType => exact allocated
    | sharedStruct => exact allocated.share_result
  · exact realized.fields.allocate declared argumentViews
  · exact realized.variableDomain
  · exact realized.emptyVariables
  · intro destination ty member
    obtain ⟨object, stored, satisfied⟩ := realized.initializedVariables destination ty member
    exact ⟨object, stored, satisfied.allocate realized.ownership⟩
  · intro object ty member
    rcases List.mem_cons.mp member with same | old
    · cases same
      have satisfied := Satisfies.allocated_whole realized.classesWellFormed declared realized.ownership argumentViews
      cases declaration.kind with
      | classType => exact satisfied
      | structType => exact satisfied
      | sharedStruct => exact satisfied.share
    · exact (realized.pendingValues object ty (List.mem_append_right _ old)).allocate realized.ownership

end Dada.Shared.Typing
