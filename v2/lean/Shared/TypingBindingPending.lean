import Shared.TypingBindingSoundness

namespace Dada.Shared.Unpacking

private theorem owners_targets (state : State) :
    (Owners state).map Reference.object = References state := by
  simp [Owners, References, List.map_filterMap, List.map_flatMap]

private theorem compatible_symm {first second : Reference} (h : Compatible first second) :
    Compatible second first := by
  rcases h with different | shared
  · exact Or.inl (Ne.symm different)
  · exact Or.inr ⟨shared.2, shared.1⟩

theorem Bind.preserves_pending
    (binding : Bind classes before reference pattern after)
    (wf : WellFormedWith classes before (reference :: pending)) : WellFormedWith classes after pending := by
  cases binding with
  | «variable» fresh =>
    refine ⟨wf.objectKeys, ?_, wf.shapes, wf.bounds, ?_, ?_, ?_⟩
    · simpa [State.bind] using List.nodup_cons.mpr ⟨fresh, wf.variableKeys⟩
    · intro id allocated
      have live := wf.rooted id allocated
      clear allocated
      induction live with
      | pending member =>
        rcases List.mem_cons.mp member with rfl | member
        · exact .variable (List.mem_cons_self ..)
        · exact .pending member
      | «variable» member => exact .variable (List.mem_cons_of_mem _ member)
      | field _ stored field ih => exact .field ih stored field
    · simpa [State.bind, Owners] using (List.perm_middle (a := reference) (l₁ := pending) (l₂ := Owners before)).symm.pairwise wf.ownersCompatible compatible_symm
    · intro id
      have complete := wf.referencesComplete id
      simpa only [State.bind, References, Allocated, List.map_cons, List.filterMap_cons,
        Option.map_some, List.cons_append, List.mem_cons, List.mem_append,
        or_assoc, or_left_comm] using complete
  | @unpack before after variables nextId object className fields pattern bindings declaration
      declared shape uniqueFields uniqueNames fresh transfer =>
    have subset : ∀ entry ∈ before ++ after,
        entry ∈ before ++ (object, ⟨className, fields⟩) :: after := by
      intro entry member
      rcases List.mem_append.mp member with left | right
      · exact List.mem_append_left _ left
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ right)
    have keys : (before.map Prod.fst ++ object :: after.map Prod.fst).Nodup := by
      simpa using wf.objectKeys
    have removedKeys : (before.map Prod.fst ++ after.map Prod.fst).Nodup :=
      List.Nodup.sublist
        ((List.Sublist.refl _).append (List.sublist_cons_self _ _)) keys
    have removedAbsent : object ∉ before.map Prod.fst ++ after.map Prod.fst := by
      have perm := List.perm_middle (a := object) (l₁ := before.map Prod.fst)
        (l₂ := after.map Prod.fst)
      exact (List.nodup_cons.mp (perm.nodup_iff.mp keys)).1
    have owners := unpack_owners transfer before after variables nextId object className
    have refs : (References
        ⟨before ++ (object, ⟨className, fields⟩) :: after, variables, nextId⟩).Perm
        (References ⟨before ++ after, bindings ++ variables, nextId⟩) := by
      simpa only [owners_targets] using owners.map Reference.object
    have compatible : (Reference.owned object :: pending ++ Owners
        ⟨before ++ after, bindings ++ variables, nextId⟩).Pairwise Compatible := by
      exact (List.Perm.cons _ (owners.append_left pending)).pairwise wf.ownersCompatible compatible_symm
    have absentReference : object ∉ pending.map Reference.object ++ References
        ⟨before ++ after, bindings ++ variables, nextId⟩ := by
      rw [← owners_targets, ← List.map_append]
      intro member
      obtain ⟨reference, member, same⟩ := List.mem_map.mp member
      rcases (List.pairwise_cons.mp compatible).1 reference member with different | shared
      · exact different same.symm
      · cases shared.1
    constructor
    · simpa using removedKeys
    · simp only [List.map_append, transfer.keys]
      apply List.nodup_append.mpr
      refine ⟨uniqueNames, wf.variableKeys, ?_⟩
      intro name member other otherMember equality
      subst other
      exact fresh name member otherMember
    · intro id data member
      exact wf.shapes id data (subset _ member)
    · intro id data member
      exact wf.bounds id data (subset _ member)
    · intro id allocated
      have notRemoved : id ≠ object := by
        intro same; subst id
        exact removedAbsent (by simpa [Allocated, List.map_append] using allocated)
      have oldAllocated : Allocated
          ⟨before ++ (object, ⟨className, fields⟩) :: after, variables, nextId⟩ id := by
        obtain ⟨entry, member, same⟩ := List.mem_map.mp allocated
        exact List.mem_map.mpr ⟨entry, subset _ member, same⟩
      exact (unpack_live transfer (by simpa using removedAbsent) (wf.rooted id oldAllocated)).resolve_left notRemoved
    · exact compatible.of_cons
    · intro id
      have complete := wf.referencesComplete id
      simp only [List.map_cons, List.mem_cons,
        Reference.owned, Allocated, List.map_append, List.mem_append] at complete
      change id ∈ pending.map Reference.object ++ References ⟨before ++ after, bindings ++ variables, nextId⟩ ↔
        id ∈ (before ++ after).map Prod.fst
      by_cases same : id = object
      · subst id
        simp [absentReference, List.map_append, removedAbsent]
      · rw [← (refs.append_left (pending.map Reference.object)).mem_iff]
        simpa [same, List.map_append] using complete

end Dada.Shared.Unpacking

namespace Dada.Shared.Typing

theorem Realizes.pending_head_unique (realized : Realizes classes environment state ((.owned object, ty) :: pending)) :
    object ∉ (pending.map Prod.fst).map Reference.object ++ References state := by
  have targets : (Owners state).map Reference.object = References state := by
    simp [Owners, References, List.map_filterMap, List.map_flatMap]
  rw [← targets, ← List.map_append]
  intro member
  obtain ⟨reference, member, same⟩ := List.mem_map.mp member
  have compatible := realized.ownership.ownersCompatible
  rcases (List.pairwise_cons.mp compatible).1 reference member with different | shared
  · exact different same.symm
  · cases shared.1

theorem Realizes.pending_head_not_reference
    (realized : Realizes classes environment state ((.owned object, ty) :: pending)) :
    object ∉ References state := fun h => realized.pending_head_unique (List.mem_append_right _ h)

theorem BindingTyped.exists_bind_pending
    (typed : BindingTyped classes environment pattern ty afterEnvironment)
    (realized : Realizes classes environment state ((reference, ty) :: pending)) :
    ∃ after, Unpacking.Bind classes.erase state reference pattern after := by
  cases typed with
  | «variable» _ _ fresh =>
    exact ⟨_, .variable (fun occupied => fresh ((realized.variableDomain _).mpr occupied))⟩
  | @unpack _ name declaration fields bindings _ _ given sameClass declared
      sameFields uniqueNames fresh _ _ =>
    have satisfied := realized.pendingValues reference ty (by simp)
    have unique : reference.mode = .unique := by rw [satisfied.mode, given]; rfl
    have owned : reference = .owned reference.object := by cases reference; cases unique; rfl
    rw [owned] at realized ⊢
    obtain ⟨data, stored, rootClass⟩ := satisfied.root
    obtain ⟨leading, trailing, objects⟩ := List.mem_iff_append.mp stored
    obtain ⟨untypedDeclaration, untypedDeclared, shape, _⟩ := realized.ownership.shapes _ _ stored
    have erasedDeclared : (name, ⟨declaration.fields.map Prod.fst, declaration.kind⟩) ∈ classes.erase :=
      List.mem_map.mpr ⟨(name, declaration), declared, rfl⟩
    have dataClass : data.className = name := rootClass.trans sameClass
    have declarationEq : untypedDeclaration = ⟨declaration.fields.map Prod.fst, declaration.kind⟩ :=
      member_value_unique realized.classesWellFormed.erase.1
        (dataClass ▸ untypedDeclared) erasedDeclared
    have actualFields : data.fields.map Prod.fst = declaration.fields.map Prod.fst := by
      simpa [declarationEq] using shape
    obtain ⟨runtimeBindings, transferred⟩ :=
      Unpacking.Transfer.exists_of_permutation (sameFields.trans (List.Perm.of_eq actualFields.symm))
    have fieldsUnique := (sameFields.nodup_iff).mpr
      ((realized.classesWellFormed.2 _ declared).1)
    rcases state with ⟨objectsList, variables, nextId⟩
    simp only at objects
    subst objectsList
    rcases data with ⟨dataName, dataFields⟩
    simp only at dataClass
    subst dataName
    exact ⟨_, .unpack erasedDeclared actualFields fieldsUnique uniqueNames
      (fun destination present occupied =>
        fresh destination present ((realized.variableDomain destination).mpr occupied)) transferred⟩

theorem Realizes.bind_variable_pending
    (realized : Realizes classes environment state ((reference, ty) :: pending))
    (fresh : name ∉ environment.map Prod.fst) :
    Realizes classes ((name, some ty) :: environment) (state.bind name reference) pending := by
  have freshState : name ∉ state.variables.map Prod.fst :=
    fun present => fresh ((realized.variableDomain name).mpr present)
  have admissible := realized.pendingTypes reference ty (by simp)
  constructor
  · exact realized.classesWellFormed
  · simpa [Environment.WellFormed, admissible, fresh] using realized.environmentWellFormed
  · intro root view member
    exact realized.pendingTypes root view (List.mem_cons_of_mem _ member)
  · exact Unpacking.Bind.preserves_pending (.variable freshState) realized.ownership
  · exact realized.fields
  · intro variableName
    simp only [List.map_cons, List.mem_cons, State.bind]
    exact or_congr Iff.rfl (realized.variableDomain variableName)
  · intro variableName member
    rcases List.mem_cons.mp member with impossible | old
    · cases impossible
    · exact List.mem_cons_of_mem _ (realized.emptyVariables _ old)
  · intro variableName variableType member
    rcases List.mem_cons.mp member with new | old
    · cases new
      exact ⟨reference, by simp [State.bind],
        (realized.pendingValues reference ty (by simp)).same_objects rfl⟩
    · obtain ⟨target, stored, satisfied⟩ := realized.initializedVariables _ _ old
      exact ⟨target, List.mem_cons_of_mem _ stored, satisfied.same_objects rfl⟩
  · intro root view member
    exact (realized.pendingValues root view (List.mem_cons_of_mem _ member)).same_objects rfl

theorem Realizes.unpack_of_field_matches_pending {fields : List (FieldName × Slot)}
    (realized : Realizes classes environment
      ⟨leading ++ (object, ⟨className, fields⟩) :: trailing, variables, nextId⟩ ((.owned object, ty) :: pending))
    (typed : FieldBindings classes ty pattern bindings)
    (transfer : Unpacking.Transfer pattern fields runtimeBindings)
    (afterWellFormed : (bindings ++ environment).WellFormed classes)
    (operation : Unpacking.Bind classes.erase
      ⟨leading ++ (object, ⟨className, fields⟩) :: trailing, variables, nextId⟩ (.owned object)
      (.unpack className pattern)
      ⟨leading ++ trailing, runtimeBindings ++ variables, nextId⟩)
    (fieldMatches : ∀ field slot description, (field, slot) ∈ fields →
      fieldDescription classes ty field = some description →
      SlotMatches classes
        ⟨leading ++ (object, ⟨className, fields⟩) :: trailing, variables, nextId⟩
        slot description) :
    Realizes classes (bindings ++ environment)
      ⟨leading ++ trailing, runtimeBindings ++ variables, nextId⟩ pending := by
  have noIncoming := realized.pending_head_not_reference
  have objectStored : (object, ⟨className, fields⟩) ∈
      leading ++ (object, ⟨className, fields⟩) :: trailing := by simp
  have subset : ∀ entry ∈ leading ++ trailing,
      entry ∈ leading ++ (object, ⟨className, fields⟩) :: trailing := by
    intro entry present
    rcases List.mem_append.mp present with left | right
    · exact List.mem_append_left _ left
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ right)
  constructor
  · exact realized.classesWellFormed
  · exact afterWellFormed
  · intro root view member
    exact realized.pendingTypes root view (List.mem_cons_of_mem _ member)
  · exact operation.preserves_pending realized.ownership
  · intro parent data field target stored fieldStored
    have oldStored := subset _ stored
    obtain ⟨declaration, targetType, targetData, declared, declaredField, targetStored, correct⟩ :=
      realized.fields parent data field target oldStored fieldStored
    have different : target.object ≠ object := by
      intro same
      apply noIncoming
      have member := field_reference_mem (state := ⟨leading ++ (object, ⟨className, fields⟩) :: trailing, variables, nextId⟩) oldStored fieldStored
      exact same ▸ member
    exact ⟨declaration, targetType, targetData, declared, declaredField,
      member_remove_other _ _ _ _ _ _ different targetStored, correct⟩
  · intro name
    simp only [List.map_append, List.mem_append, typed.keys, transfer.keys]
    exact or_congr Iff.rfl (realized.variableDomain name)
  · intro name member
    rcases List.mem_append.mp member with new | old
    · obtain ⟨field, patternMember, description⟩ := typed.description_member new
      obtain ⟨slot, bound, stored⟩ := transfer.pattern_member patternMember
      have matched := fieldMatches field slot none stored description
      cases slot with
      | none => exact List.mem_append_left _ bound
      | some target => cases matched
    · exact List.mem_append_right _ (realized.emptyVariables name old)
  · intro name child member
    rcases List.mem_append.mp member with new | old
    · obtain ⟨field, patternMember, description⟩ := typed.description_member new
      obtain ⟨slot, bound, stored⟩ := transfer.pattern_member patternMember
      have matched := fieldMatches field slot (some child) stored description
      cases slot with
      | none => cases matched
      | some target =>
        have different : target.object ≠ object := by
          intro same
          apply noIncoming
          have member := field_reference_mem (state := ⟨leading ++ (object, ⟨className, fields⟩) :: trailing, variables, nextId⟩) (data := ⟨className, fields⟩) objectStored stored
          exact same ▸ member
        exact ⟨target, List.mem_append_left _ bound, matched.remove different noIncoming⟩
    · obtain ⟨target, stored, satisfied⟩ := realized.initializedVariables name child old
      have different : target.object ≠ object := by
        intro same
        apply noIncoming
        have member := variable_reference_mem (state := ⟨leading ++ (object, ⟨className, fields⟩) :: trailing, variables, nextId⟩) stored
        exact same ▸ member
      exact ⟨target, List.mem_append_right _ stored, satisfied.remove different noIncoming⟩
  · intro root view member
    have different : root.object ≠ object := by
      intro same
      apply realized.pending_head_unique
      exact List.mem_append_left _ (List.mem_map.mpr ⟨root, List.mem_map.mpr ⟨(root, view), member, rfl⟩, same⟩)
    exact (realized.pendingValues root view (List.mem_cons_of_mem _ member)).remove different noIncoming


theorem BindingTyped.preserves_realization_of_fields_pending
    (typed : BindingTyped classes environment pattern ty afterEnvironment)
    (realized : Realizes classes environment state ((reference, ty) :: pending))
    (operation : Unpacking.Bind classes.erase state reference pattern after)
    (fieldMatches : reference.mode = .unique →
      ∀ data, (reference.object, data) ∈ state.objects →
      ∀ field slot description, (field, slot) ∈ data.fields →
      fieldDescription classes ty field = some description →
      SlotMatches classes state slot description) :
    Realizes classes afterEnvironment after pending := by
  cases typed with
  | «variable» _ _ fresh =>
    cases operation with
    | «variable» _ => exact realized.bind_variable_pending fresh
  | @unpack _ name declaration pattern bindings _ _ _ _ _ _ _ _ fieldTyped afterWf =>
    cases operation with
    | @unpack leading trailing variables nextId object className fields pattern runtimeBindings
        declaration _ _ _ _ _ transfer =>
      apply realized.unpack_of_field_matches_pending fieldTyped transfer afterWf
        (.unpack ‹_› ‹_› ‹_› ‹_› ‹_› transfer)
      exact fieldMatches rfl ⟨name, fields⟩ (by simp [Reference.owned])


theorem BindingTyped.preserves_realization_pending
    (typed : BindingTyped classes environment pattern ty afterEnvironment)
    (realized : Realizes classes environment state ((reference, ty) :: pending))
    (operation : Unpacking.Bind classes.erase state reference pattern after) :
    Realizes classes afterEnvironment after pending := by
  apply typed.preserves_realization_of_fields_pending realized operation
  intro unique data stored field slot description fieldStored described
  have satisfied := realized.pendingValues reference ty (by simp)
  apply satisfied.fieldDescription_of_focus unique realized.ownership stored fieldStored described
  intro child focused
  have normal := typed.wellFormed.2.1.2
  have observations := focus_observations realized.classesWellFormed normal focused
  obtain ⟨target, _, read, _, _⟩ := satisfied.positive [field] observations.positive
  exact ⟨target, read, satisfied.focus realized.classesWellFormed realized.ownership normal focused read⟩


end Dada.Shared.Typing
