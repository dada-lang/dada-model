import Shared.Effects

namespace Dada.Shared

def ClassesWellFormed (classes : Classes) : Prop :=
  (classes.map Prod.fst).Nodup ∧
    ∀ name declaration, (name, declaration) ∈ classes → declaration.fields.Nodup

-- Each list entry represents one owning occurrence, including repeated shared
-- references stored in different slots.
def Owners (state : State) : List Reference :=
  state.variables.filterMap (fun binding => binding.2) ++
    state.objects.flatMap (fun entry => entry.2.fields.filterMap (fun field => field.2))

-- Different occurrences may target the same object only when both are shared.
def Compatible (first second : Reference) : Prop :=
  first.object ≠ second.object ∨ first.mode = .shared ∧ second.mode = .shared

structure WellFormed (classes : Classes) (state : State) : Prop where
  objectKeys : (state.objects.map Prod.fst).Nodup
  variableKeys : (state.variables.map Prod.fst).Nodup
  shapes : ∀ id data, (id, data) ∈ state.objects →
    ∃ declaration, (data.className, declaration) ∈ classes ∧
      data.fields.map Prod.fst = declaration.fields ∧ declaration.fields.Nodup
  bounds : ∀ id data, (id, data) ∈ state.objects → id.index < state.nextId
  older : ∀ id data name reference, (id, data) ∈ state.objects →
    (name, some reference) ∈ data.fields → reference.object.index < id.index
  ownersCompatible : (Owners state).Pairwise Compatible
  referencesComplete : ∀ id, id ∈ References state ↔ Allocated state id

private abbrev slotOwners {K : Type} (slots : List (K × Slot)) : List Reference :=
  slots.filterMap (fun entry => entry.2)

private theorem owners_targets (state : State) : (Owners state).map Reference.object = References state := by
  simp [Owners, References, List.map_filterMap, List.map_flatMap]

private theorem compatible_symm {first second : Reference} (h : Compatible first second) :
    Compatible second first := by
  rcases h with different | shared
  · exact Or.inl (Ne.symm different)
  · exact Or.inr ⟨shared.2, shared.1⟩

private theorem compatible_weaken {first second : Reference} (h : Compatible first second) :
    Compatible (.shared first.object) second := by
  rcases h with different | shared
  · exact Or.inl different
  · exact Or.inr ⟨rfl, shared.2⟩

private theorem pairwise_weaken (h : (reference :: others).Pairwise Compatible) :
    (Reference.shared reference.object :: others).Pairwise Compatible := by
  exact List.pairwise_cons.mpr ⟨fun _ member => compatible_weaken
    ((List.pairwise_cons.mp h).1 _ member), h.of_cons⟩

private theorem shared_compatible_all {owners : List Reference} (h : owners.Pairwise Compatible)
    (member : Reference.shared object ∈ owners) :
    ∀ reference ∈ owners, Compatible (.shared object) reference := by
  induction owners with
  | nil => simp at member
  | cons head tail ih =>
    have parts := List.pairwise_cons.mp h
    rcases List.mem_cons.mp member with same | inside
    · subst head
      intro reference found
      rcases List.mem_cons.mp found with same | rest
      · subst reference
        exact Or.inr ⟨rfl, rfl⟩
      · exact parts.1 _ rest
    · intro reference found
      rcases List.mem_cons.mp found with same | rest
      · subst reference
        exact compatible_symm (parts.1 _ inside)
      · exact ih parts.2 inside _ rest

private theorem pairwise_copy {owners : List Reference} (h : owners.Pairwise Compatible)
    (member : Reference.shared object ∈ owners) :
    (Reference.shared object :: owners).Pairwise Compatible :=
  List.pairwise_cons.mpr ⟨shared_compatible_all h member, h⟩

theorem Take.object_keys (take : Take before place object after) :
    after.objects.map Prod.fst = before.objects.map Prod.fst := by
  cases take <;> simp

theorem Take.variable_keys (take : Take before place object after) :
    after.variables.map Prod.fst = before.variables.map Prod.fst := by
  cases take <;> simp

theorem Take.next_id (take : Take before place object after) :
    after.nextId = before.nextId := by
  cases take <;> rfl

theorem Promote.object_keys (promote : Promote before place object after) :
    after.objects.map Prod.fst = before.objects.map Prod.fst := by
  cases promote <;> simp

theorem Promote.variable_keys (promote : Promote before place object after) :
    after.variables.map Prod.fst = before.variables.map Prod.fst := by
  cases promote <;> simp

theorem Promote.next_id (promote : Promote before place object after) :
    after.nextId = before.nextId := by
  cases promote <;> rfl

theorem Take.owners (take : Take before place object after) :
    (Owners before).Perm (Reference.owned object :: Owners after) := by
  cases take with
  | «variable» objects next leading suffix name object =>
    simp only [Owners, List.filterMap_append, List.filterMap_cons]
    simpa only [List.append_assoc, List.cons_append] using
      (List.perm_middle (a := Reference.owned object)
        (l₁ := slotOwners leading)
        (l₂ := slotOwners suffix ++ objects.flatMap (fun entry => slotOwners entry.2.fields)))
  | field variables next before after parent className leading suffix name object =>
    simp only [Owners, List.flatMap_append, List.flatMap_cons, List.filterMap_append,
      List.filterMap_cons]
    simpa only [List.append_assoc, List.cons_append] using
      (List.perm_middle (a := Reference.owned object)
        (l₁ := slotOwners variables ++ before.flatMap (fun entry => slotOwners entry.2.fields) ++
          slotOwners leading)
        (l₂ := slotOwners suffix ++ after.flatMap (fun entry => slotOwners entry.2.fields)))

theorem Promote.owners (promote : Promote before place object after) :
    ∃ rest, (Owners before).Perm (Reference.owned object :: rest) ∧
      (Owners after).Perm (Reference.shared object :: rest) := by
  cases promote with
  | «variable» objects next leading suffix name object =>
    refine ⟨slotOwners leading ++ slotOwners suffix ++
      objects.flatMap (fun entry => slotOwners entry.2.fields), ?_, ?_⟩ <;>
      simp [Owners, List.append_assoc, slotOwners]
  | field variables next before after parent className leading suffix name object =>
    refine ⟨slotOwners variables ++ before.flatMap (fun entry => slotOwners entry.2.fields) ++
      slotOwners leading ++ slotOwners suffix ++ after.flatMap (fun entry => slotOwners entry.2.fields),
      ?_, ?_⟩ <;>
      simpa [Owners, List.append_assoc, slotOwners] using
        (List.perm_middle
          (l₁ := slotOwners variables ++ before.flatMap (fun entry => slotOwners entry.2.fields) ++
            slotOwners leading)
          (l₂ := slotOwners suffix ++ after.flatMap (fun entry => slotOwners entry.2.fields)))

private theorem stored_owner (stored : Stored state place (some reference)) :
    reference ∈ Owners state := by
  cases place with
  | «variable» name =>
    exact List.mem_append_left _ (List.mem_filterMap.mpr ⟨(name, some reference), stored, rfl⟩)
  | field object name =>
    obtain ⟨data, member, field⟩ := stored
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨(object, data), member,
      List.mem_filterMap.mpr ⟨(name, some reference), field, rfl⟩⟩)

theorem WellFormed.empty (classes : Classes) : WellFormed classes State.empty := by
  constructor <;> simp [State.empty, Owners, References, Allocated]


-- The storage frame records the unchanged identities and layouts. Initialized
-- fields may disappear or weaken to shared ownership, but keep their targets.
private structure StorageFrame (before after : State) : Prop where
  objectKeys : after.objects.map Prod.fst = before.objects.map Prod.fst
  variableKeys : after.variables.map Prod.fst = before.variables.map Prod.fst
  nextId : after.nextId = before.nextId
  data : ∀ id newData, (id, newData) ∈ after.objects →
    ∃ oldData, (id, oldData) ∈ before.objects ∧
      newData.className = oldData.className ∧
      newData.fields.map Prod.fst = oldData.fields.map Prod.fst ∧
      ∀ name reference, (name, some reference) ∈ newData.fields →
        ∃ oldReference, (name, some oldReference) ∈ oldData.fields ∧
          reference.object = oldReference.object

private theorem Take.frame (take : Take before place object after) : StorageFrame before after := by
  refine ⟨take.object_keys, take.variable_keys, take.next_id, ?_⟩
  intro id data member
  obtain ⟨oldData, oldMember, sameClass, sameFields, remaining⟩ := take.object_data id data member
  exact ⟨oldData, oldMember, sameClass, sameFields, fun name reference found =>
    ⟨reference, remaining name reference found, rfl⟩⟩

private theorem Promote.frame (promote : Promote before place object after) : StorageFrame before after :=
  ⟨promote.object_keys, promote.variable_keys, promote.next_id, promote.object_data⟩

private theorem StorageFrame.refl (state : State) : StorageFrame state state := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro id data member
  exact ⟨data, member, rfl, rfl, fun _ reference field => ⟨reference, field, rfl⟩⟩

private theorem Give.frame (give : Give before path reference after) : StorageFrame before after := by
  cases give with
  | move _ take => exact take.frame
  | copy => exact StorageFrame.refl _
  | promote _ promotion => exact promotion.frame

private theorem Give.owners_compatible (give : Give before path reference after)
    (compatible : (Owners before).Pairwise Compatible) :
    (reference :: Owners after).Pairwise Compatible := by
  cases give with
  | move _ take => exact take.owners.pairwise compatible compatible_symm
  | copy _ stored => exact pairwise_copy compatible (stored_owner stored)
  | promote _ promotion =>
    obtain ⟨rest, oldPerm, newPerm⟩ := promotion.owners
    have promoted := pairwise_weaken (oldPerm.pairwise compatible compatible_symm)
    have duplicate := pairwise_copy promoted (List.mem_cons_self ..)
    exact (List.Perm.cons _ newPerm).symm.pairwise duplicate compatible_symm

private theorem Promote.references (promotion : Promote before place object after) :
    References after = References before := by
  cases promotion <;> simp [References, Reference.owned, Reference.shared]

private theorem Give.targets (give : Give before path reference after) (object : ObjectId) :
    object ∈ (reference :: Owners after).map Reference.object ↔ object ∈ References before := by
  cases give with
  | move _ take =>
    simpa [owners_targets] using (take.owners.map Reference.object).mem_iff.symm
  | copy _ stored =>
    have member := List.mem_map_of_mem (f := Reference.object) (stored_owner stored)
    rw [owners_targets] at member
    simp only [List.map_cons, owners_targets, List.mem_cons]
    exact or_iff_right_of_imp (fun same => same ▸ member)
  | promote _ promotion =>
    obtain ⟨rest, oldPerm, _⟩ := promotion.owners
    have present := (oldPerm.map Reference.object).mem_iff.mpr (List.mem_cons_self ..)
    rw [owners_targets] at present
    simp only [List.map_cons, owners_targets, promotion.references, List.mem_cons]
    exact or_iff_right_of_imp (fun same => same ▸ present)

theorem Give.bind_preserves (wf : WellFormed classes before)
    (give : Give before path reference after)
    (fresh : destination ∉ before.variables.map Prod.fst) :
    WellFormed classes (after.bind destination reference) := by
  have frame := give.frame
  constructor
  · simpa [State.bind, frame.objectKeys] using wf.objectKeys
  · simpa [State.bind, frame.variableKeys] using List.nodup_cons.mpr ⟨fresh, wf.variableKeys⟩
  · intro id data member
    obtain ⟨oldData, oldMember, sameClass, sameFields, _⟩ := frame.data id data member
    obtain ⟨declaration, declared, fields, distinct⟩ := wf.shapes id oldData oldMember
    exact ⟨declaration, sameClass ▸ declared, sameFields.trans fields, distinct⟩
  · intro id data member
    obtain ⟨oldData, oldMember, _, _, _⟩ := frame.data id data member
    simpa [State.bind, frame.nextId] using wf.bounds id oldData oldMember
  · intro id data name target member field
    obtain ⟨oldData, oldMember, _, _, remaining⟩ := frame.data id data member
    obtain ⟨oldTarget, oldField, sameTarget⟩ := remaining name target field
    rw [sameTarget]
    exact wf.older id oldData name oldTarget oldMember oldField
  · simpa [State.bind, Owners] using give.owners_compatible wf.ownersCompatible
  · intro id
    have target := give.targets id
    rw [← owners_targets (after.bind destination reference)]
    simpa [Allocated, State.bind, Owners, frame.objectKeys] using
      target.trans (wf.referencesComplete id)

theorem WellFormed.share_result {state : State} {name : VariableId} {reference : Reference}
    (wf : WellFormed classes (state.bind name reference)) :
    WellFormed classes (state.bind name (.shared reference.object)) := by
  constructor
  · exact wf.objectKeys
  · exact wf.variableKeys
  · exact wf.shapes
  · exact wf.bounds
  · exact wf.older
  · have compatible : (reference :: Owners state).Pairwise Compatible := by
      simpa [Owners, State.bind] using wf.ownersCompatible
    simpa [Owners, State.bind] using pairwise_weaken compatible
  · simpa [References, State.bind, Reference.shared, Allocated] using wf.referencesComplete


-- Expression evaluation temporarily holds owners outside the variable and field
-- stores. Pending owners are included until a constructor or let stores them.
structure WellFormedWith (classes : Classes) (state : State) (pending : List Reference) : Prop where
  objectKeys : (state.objects.map Prod.fst).Nodup
  variableKeys : (state.variables.map Prod.fst).Nodup
  shapes : ∀ id data, (id, data) ∈ state.objects →
    ∃ declaration, (data.className, declaration) ∈ classes ∧
      data.fields.map Prod.fst = declaration.fields ∧ declaration.fields.Nodup
  bounds : ∀ id data, (id, data) ∈ state.objects → id.index < state.nextId
  older : ∀ id data name reference, (id, data) ∈ state.objects →
    (name, some reference) ∈ data.fields → reference.object.index < id.index
  ownersCompatible : (pending ++ Owners state).Pairwise Compatible
  referencesComplete : ∀ id, id ∈ (pending.map Reference.object ++ References state) ↔ Allocated state id

theorem WellFormed.with_pending (wf : WellFormed classes state) :
    WellFormedWith classes state [] := by
  exact ⟨wf.objectKeys, wf.variableKeys, wf.shapes, wf.bounds, wf.older,
    by simpa using wf.ownersCompatible, by simpa using wf.referencesComplete⟩

theorem WellFormedWith.no_pending (wf : WellFormedWith classes state []) :
    WellFormed classes state := by
  exact ⟨wf.objectKeys, wf.variableKeys, wf.shapes, wf.bounds, wf.older,
    by simpa using wf.ownersCompatible, by simpa using wf.referencesComplete⟩

theorem WellFormedWith.perm (wf : WellFormedWith classes state pending)
    (permutation : pending.Perm other) : WellFormedWith classes state other := by
  refine ⟨wf.objectKeys, wf.variableKeys, wf.shapes, wf.bounds, wf.older, ?_, ?_⟩
  · exact (permutation.append_right _).pairwise wf.ownersCompatible compatible_symm
  · intro id
    exact ((permutation.map Reference.object).append_right _).mem_iff.symm.trans
      (wf.referencesComplete id)

private theorem Give.pending_compatible (give : Give before path reference after)
    (compatible : (pending ++ Owners before).Pairwise Compatible) :
    (reference :: pending ++ Owners after).Pairwise Compatible := by
  cases give with
  | move _ take =>
    have moved := (take.owners.append_left pending).pairwise compatible compatible_symm
    exact (by simpa only [List.cons_append] using
      (List.perm_middle (a := Reference.owned _) (l₁ := pending)
        (l₂ := Owners after)).pairwise moved compatible_symm)
  | copy _ stored =>
    exact pairwise_copy compatible (List.mem_append_right _ (stored_owner stored))
  | promote _ promotion =>
    obtain ⟨rest, oldPerm, newPerm⟩ := promotion.owners
    have front := (List.perm_middle (a := Reference.owned _) (l₁ := pending) (l₂ := rest)).pairwise
      ((oldPerm.append_left pending).pairwise compatible compatible_symm) compatible_symm
    have promoted := pairwise_weaken front
    have copied := pairwise_copy promoted (List.mem_cons_self ..)
    have rearranged := (List.Perm.cons _
      (List.perm_middle (a := Reference.shared _) (l₁ := pending) (l₂ := rest)).symm).pairwise
        copied compatible_symm
    exact (List.Perm.cons _ (newPerm.symm.append_left pending)).pairwise rearranged compatible_symm

theorem Give.preserves_pending (give : Give before path reference after)
    (wf : WellFormedWith classes before pending) :
    WellFormedWith classes after (reference :: pending) := by
  have frame := give.frame
  refine ⟨?_, ?_, ?_, ?_, ?_, give.pending_compatible wf.ownersCompatible, ?_⟩
  · simpa [frame.objectKeys] using wf.objectKeys
  · simpa [frame.variableKeys] using wf.variableKeys
  · intro id data member
    obtain ⟨oldData, oldMember, sameClass, sameFields, _⟩ := frame.data id data member
    obtain ⟨declaration, declared, fields, distinct⟩ := wf.shapes id oldData oldMember
    exact ⟨declaration, sameClass ▸ declared, sameFields.trans fields, distinct⟩
  · intro id data member
    obtain ⟨oldData, oldMember, _, _, _⟩ := frame.data id data member
    simpa [frame.nextId] using wf.bounds id oldData oldMember
  · intro id data name target member field
    obtain ⟨oldData, oldMember, _, _, remaining⟩ := frame.data id data member
    obtain ⟨oldTarget, oldField, sameTarget⟩ := remaining name target field
    rw [sameTarget]
    exact wf.older id oldData name oldTarget oldMember oldField
  · intro id
    have targets := give.targets id
    simp only [List.map_cons, owners_targets, List.mem_cons] at targets
    simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append]
    rw [or_left_comm, targets]
    simpa [List.mem_append, Allocated, frame.objectKeys] using wf.referencesComplete id

theorem WellFormedWith.share_result
    (wf : WellFormedWith classes state (reference :: pending)) :
    WellFormedWith classes state (.shared reference.object :: pending) := by
  refine ⟨wf.objectKeys, wf.variableKeys, wf.shapes, wf.bounds, wf.older,
    pairwise_weaken wf.ownersCompatible, ?_⟩
  simpa [Reference.shared] using wf.referencesComplete

private theorem zipped_field_names (fields : List FieldName) (references : List Reference)
    (lengths : references.length = fields.length) :
    (fields.zip (references.map some)).map Prod.fst = fields := by
  apply List.map_fst_zip
  simp [lengths]

private theorem zipped_field_owners (fields : List FieldName) (references : List Reference)
    (lengths : references.length = fields.length) :
    slotOwners (fields.zip (references.map some)) = references := by
  have seconds := List.map_snd_zip (l₁ := fields) (l₂ := references.map some)
    (by simp [lengths])
  have filtered := congrArg (List.filterMap id) seconds
  simpa [List.filterMap_map, Function.comp_def, slotOwners] using filtered

private theorem allocation_owners (state : State)
    (lengths : references.length = fields.length) :
    (Owners (state.allocate className fields references)).Perm (references ++ Owners state) := by
  simp only [Owners, State.allocate, List.flatMap_cons]
  rw [show List.filterMap (fun field => field.2) (fields.zip (references.map some)) = references
    from zipped_field_owners fields references lengths]
  simpa only [List.append_assoc] using
    (List.perm_append_comm (l₁ := slotOwners state.variables) (l₂ := references)).append_right
      (state.objects.flatMap (fun entry => slotOwners entry.2.fields))

theorem WellFormedWith.pending_bound (wf : WellFormedWith classes state pending)
    (member : reference ∈ pending) : reference.object.index < state.nextId := by
  have referred := List.mem_append_left (References state)
    (List.mem_map_of_mem (f := Reference.object) member)
  obtain ⟨⟨id, data⟩, allocated, equality⟩ :=
    List.mem_map.mp ((wf.referencesComplete reference.object).mp referred)
  simp only at equality
  subst id
  exact wf.bounds reference.object data allocated

theorem WellFormedWith.allocate (classesWf : ClassesWellFormed classes)
    (wf : WellFormedWith classes state (references ++ pending))
    (declared : (className, declaration) ∈ classes)
    (lengths : references.length = declaration.fields.length)
    (freshObject : ObjectId.mk state.nextId ∉ state.objects.map Prod.fst) :
    WellFormedWith classes (state.allocate className declaration.fields references)
      (Reference.owned ⟨state.nextId⟩ :: pending) := by
  have perm := allocation_owners (className := className) state lengths
  have combined : (pending ++ Owners (state.allocate className declaration.fields references)).Perm
      (references ++ pending ++ Owners state) :=
    (perm.append_left pending).trans (by
      simpa only [List.append_assoc] using
        (List.perm_append_comm (l₁ := pending) (l₂ := references)).append_right (Owners state))
  refine ⟨?_, wf.variableKeys, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [State.allocate] using List.nodup_cons.mpr ⟨freshObject, wf.objectKeys⟩
  · intro id data member
    rcases List.mem_cons.mp member with same | old
    · cases same
      exact ⟨declaration, declared, zipped_field_names _ _ lengths, classesWf.2 _ _ declared⟩
    · exact wf.shapes id data old
  · intro id data member
    rcases List.mem_cons.mp member with same | old
    · cases same
      exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (wf.bounds id data old)
  · intro id data name target member field
    rcases List.mem_cons.mp member with same | old
    · cases same
      have referred : target ∈ slotOwners (declaration.fields.zip (references.map some)) :=
        List.mem_filterMap.mpr ⟨(name, some target), field, rfl⟩
      rw [zipped_field_owners _ _ lengths] at referred
      exact wf.pending_bound (List.mem_append_left _ referred)
    · exact wf.older id data name target old field
  · apply List.pairwise_cons.mpr
    refine ⟨?_, combined.symm.pairwise wf.ownersCompatible compatible_symm⟩
    intro reference member
    apply Or.inl
    intro same
    have referred := List.mem_map_of_mem (f := Reference.object) (combined.mem_iff.mp member)
    simp only [List.map_append, owners_targets] at referred
    have allocated := (wf.referencesComplete reference.object).mp (by simpa only [List.map_append] using referred)
    change ObjectId.mk state.nextId = reference.object at same
    exact freshObject (by simpa only [Allocated, same] using allocated)
  · intro id
    have targets := (combined.map Reference.object).mem_iff (a := id)
    simp only [List.map_append, owners_targets] at targets
    simp only [List.map_cons, List.cons_append, List.mem_cons]
    rw [targets, ← List.map_append, wf.referencesComplete]
    simp [Allocated, State.allocate, Reference.owned]

theorem WellFormedWith.bind (wf : WellFormedWith classes state [reference])
    (fresh : destination ∉ state.variables.map Prod.fst) :
    WellFormed classes (state.bind destination reference) := by
  refine ⟨wf.objectKeys, ?_, wf.shapes, wf.bounds, wf.older, ?_, ?_⟩
  · simpa [State.bind] using List.nodup_cons.mpr ⟨fresh, wf.variableKeys⟩
  · simpa [State.bind, Owners] using wf.ownersCompatible
  · simpa [State.bind, References, Allocated] using wf.referencesComplete

theorem Eval.preserves_wellFormedWith (classesWf : ClassesWellFormed classes)
    (evaluation : Eval classes before expression after reference)
    (wf : WellFormedWith classes before pending) :
    WellFormedWith classes after (reference :: pending) := by
  apply Eval.rec
    (motive_1 := fun before _ after reference _ => ∀ pending,
      WellFormedWith classes before pending → WellFormedWith classes after (reference :: pending))
    (motive_2 := fun before _ after references _ => ∀ pending,
      WellFormedWith classes before pending → WellFormedWith classes after (references ++ pending))
    ?_ ?_ ?_ ?_ ?_ evaluation pending wf
  · intro state evaluated path reference give pending wf
    exact give.preserves_pending wf
  · intro state evaluated path reference give pending wf
    exact (give.preserves_pending wf).share_result
  · intro state evaluated className declaration arguments references declared args lengths fresh ih pending wf
    exact (ih pending wf).allocate classesWf declared lengths fresh
  · intro state pending wf
    exact wf
  · intro before middle after argument arguments reference references first rest ihFirst ihRest pending wf
    have result := ihRest (reference :: pending) (ihFirst pending wf)
    exact result.perm (by
      simpa only [List.cons_append] using
        List.perm_middle (a := reference) (l₁ := references) (l₂ := pending))

theorem Eval.variable_keys (evaluation : Eval classes before value after reference) :
    after.variables.map Prod.fst = before.variables.map Prod.fst := by
  induction evaluation using Eval.rec
    (motive_2 := fun before _ after _ _ =>
      after.variables.map Prod.fst = before.variables.map Prod.fst) with
  | give give => exact give.frame.variableKeys
  | giveShare give => exact give.frame.variableKeys
  | new _ _ _ _ ih => exact ih
  | nil => rfl
  | cons _ _ first rest => exact rest.trans first

theorem EvalArgs.length (evaluation : EvalArgs classes before arguments after references) :
    references.length = arguments.length := by
  induction evaluation using EvalArgs.rec
    (motive_1 := fun _ _ _ _ _ => True) with
  | give => trivial
  | giveShare => trivial
  | new => trivial
  | nil => rfl
  | cons _ _ _ rest => simpa using rest

theorem Step.preserves_wellFormed (classesWf : ClassesWellFormed classes)
    (wf : WellFormed classes before.state) (step : Step classes before after) :
    WellFormed classes after.state := by
  cases step with
  | letValue fresh evaluation =>
    exact (evaluation.preserves_wellFormedWith classesWf wf.with_pending).bind fresh

theorem Steps.preserves_wellFormed (classesWf : ClassesWellFormed classes)
    (wf : WellFormed classes before.state) (steps : Steps classes before after) :
    WellFormed classes after.state := by
  induction steps with
  | refl => exact wf
  | step first _ ih => exact ih (first.preserves_wellFormed classesWf wf)

theorem Steps.from_initial (classesWf : ClassesWellFormed program.classes)
    (steps : Steps program.classes (Configuration.initial program) after) :
    WellFormed program.classes after.state :=
  steps.preserves_wellFormed classesWf (WellFormed.empty _)

end Dada.Shared
