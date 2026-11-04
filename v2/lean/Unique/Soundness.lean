import Unique.Effects

namespace Dada.Unique

-- Class layouts are fixed, and every field name identifies one slot.
def ClassesWellFormed (classes : Classes) : Prop :=
  (classes.map Prod.fst).Nodup ∧
    ∀ name declaration, (name, declaration) ∈ classes → declaration.fields.Nodup

-- These conditions describe arbitrary finite graphs independently of execution.
-- Rootedness records reachability directly; object IDs are allocation identities.
structure WellFormed (classes : Classes) (state : State) : Prop where
  objectKeys : (state.objects.map Prod.fst).Nodup
  variableKeys : (state.variables.map Prod.fst).Nodup
  shapes : ∀ id data, (id, data) ∈ state.objects →
    ∃ declaration, (data.className, declaration) ∈ classes ∧
      data.fields.map Prod.fst = declaration.fields ∧ declaration.fields.Nodup
  bounds : ∀ id data, (id, data) ∈ state.objects → id.index < state.nextId
  rooted : ∀ object, Allocated state object → Live state object
  referencesUnique : (References state).Nodup
  referencesComplete : ∀ id, id ∈ References state ↔ Allocated state id

-- Expression results are temporary owning roots until the surrounding constructor
-- or statement stores them. The empty-root case is the statement invariant.
structure WellFormedWith (classes : Classes) (state : State) (pending : List ObjectId) : Prop where
  objectKeys : (state.objects.map Prod.fst).Nodup
  variableKeys : (state.variables.map Prod.fst).Nodup
  shapes : ∀ id data, (id, data) ∈ state.objects →
    ∃ declaration, (data.className, declaration) ∈ classes ∧
      data.fields.map Prod.fst = declaration.fields ∧ declaration.fields.Nodup
  bounds : ∀ id data, (id, data) ∈ state.objects → id.index < state.nextId
  rooted : ∀ object, Allocated state object → LiveWith state pending object
  referencesUnique : (pending ++ References state).Nodup
  referencesComplete : ∀ id, id ∈ pending ++ References state ↔ Allocated state id

private abbrev slotReferences {K : Type} (slots : List (K × Slot)) : List ObjectId :=
  slots.filterMap (fun entry => entry.2)

-- Taking an owner changes neither object allocation nor slot identities.
theorem Take.object_keys (take : Take before place object after) :
    after.objects.map Prod.fst = before.objects.map Prod.fst := by
  cases take <;> simp

theorem Take.variable_keys (take : Take before place object after) :
    after.variables.map Prod.fst = before.variables.map Prod.fst := by
  cases take <;> simp

theorem Take.next_id (take : Take before place object after) :
    after.nextId = before.nextId := by
  cases take <;> rfl

-- One occurrence leaves the source graph and becomes the expression's result.
theorem Take.references (take : Take before place object after) :
    (References before).Perm (object :: References after) := by
  cases take with
  | «variable» objects next leading suffix name object =>
    simp only [References, List.filterMap_append, List.filterMap_cons]
    simpa only [List.append_assoc, List.cons_append] using
      (List.perm_middle (a := object)
        (l₁ := leading.filterMap (fun binding => binding.2))
        (l₂ := suffix.filterMap (fun binding => binding.2) ++
          objects.flatMap (fun entry => entry.2.fields.filterMap (fun field => field.2))))
  | field variables next before after parent className leading suffix name object =>
    simp only [References, List.flatMap_append, List.flatMap_cons, List.filterMap_append,
      List.filterMap_cons]
    simpa only [List.append_assoc, List.cons_append] using
      (List.perm_middle (a := object)
        (l₁ := variables.filterMap (fun binding => binding.2) ++
          before.flatMap (fun entry => entry.2.fields.filterMap (fun field => field.2)) ++
          leading.filterMap (fun field => field.2))
        (l₂ := suffix.filterMap (fun field => field.2) ++
          after.flatMap (fun entry => entry.2.fields.filterMap (fun field => field.2))))

private theorem zipped_field_names (fields : List FieldName) (objects : List ObjectId)
    (lengths : objects.length = fields.length) :
    (fields.zip (objects.map some)).map Prod.fst = fields := by
  apply List.map_fst_zip
  simp [lengths]

private theorem zipped_field_references (fields : List FieldName) (objects : List ObjectId)
    (lengths : objects.length = fields.length) :
    slotReferences (fields.zip (objects.map some)) = objects := by
  have seconds := List.map_snd_zip (l₁ := fields) (l₂ := objects.map some)
    (by simp [lengths])
  have filtered := congrArg (List.filterMap id) seconds
  simpa [List.filterMap_map, Function.comp_def, slotReferences] using filtered


theorem WellFormed.empty (classes : Classes) : WellFormed classes State.empty := by
  constructor <;> simp [State.empty, References, Allocated]

theorem WellFormed.with_empty (wf : WellFormed classes state) :
    WellFormedWith classes state [] := by
  exact ⟨wf.objectKeys, wf.variableKeys, wf.shapes, wf.bounds, fun object allocated => (wf.rooted object allocated).with_pending,
    by simpa using wf.referencesUnique, by simpa using wf.referencesComplete⟩

theorem WellFormedWith.without_pending (wf : WellFormedWith classes state []) :
    WellFormed classes state := by
  exact ⟨wf.objectKeys, wf.variableKeys, wf.shapes, wf.bounds, fun object allocated => (wf.rooted object allocated).without_pending,
    by simpa using wf.referencesUnique, by simpa using wf.referencesComplete⟩

theorem WellFormedWith.perm (wf : WellFormedWith classes state pending)
    (permutation : pending.Perm other) : WellFormedWith classes state other := by
  have refs := permutation.append_right (References state)
  exact ⟨wf.objectKeys, wf.variableKeys, wf.shapes, wf.bounds, fun object allocated => (wf.rooted object allocated).mono (fun _ h => permutation.mem_iff.mp h),
    refs.nodup_iff.mp wf.referencesUnique,
    fun id => refs.mem_iff.symm.trans (wf.referencesComplete id)⟩

theorem Take.preserves_pending (wf : WellFormedWith classes before pending)
    (take : Take before place object after) :
    WellFormedWith classes after (object :: pending) := by
  have references : (pending ++ References before).Perm
      ((object :: pending) ++ References after) :=
    (take.references.append_left pending).trans List.perm_middle
  constructor
  · simpa [take.object_keys] using wf.objectKeys
  · simpa [take.variable_keys] using wf.variableKeys
  · intro id data member
    obtain ⟨oldData, oldMember, sameClass, sameFields, _⟩ := take.object_data id data member
    obtain ⟨declaration, declared, fields, distinct⟩ := wf.shapes id oldData oldMember
    exact ⟨declaration, sameClass ▸ declared, sameFields.trans fields, distinct⟩
  · intro id data member
    obtain ⟨oldData, oldMember, _, _, _⟩ := take.object_data id data member
    simpa [take.next_id] using wf.bounds id oldData oldMember
  · intro object allocated
    exact take.liveWith (wf.rooted object (by simpa [Allocated, take.object_keys] using allocated))
  · exact references.nodup_iff.mp wf.referencesUnique
  · intro id
    simpa [Allocated, take.object_keys] using
      references.mem_iff.symm.trans (wf.referencesComplete id)

theorem WellFormedWith.bind (wf : WellFormedWith classes state [object])
    (fresh : destination ∉ state.variables.map Prod.fst) :
    WellFormed classes (state.bind destination object) := by
  constructor
  · exact wf.objectKeys
  · simpa [State.bind] using List.nodup_cons.mpr ⟨fresh, wf.variableKeys⟩
  · exact wf.shapes
  · exact wf.bounds
  · intro id allocated
    have live := wf.rooted id allocated
    clear allocated
    induction live with
    | @pending current member =>
      have same : current = object := by simpa using member
      subst_vars
      exact .variable (name := destination) (by simp [State.bind])
    | «variable» member => exact .variable (List.mem_cons_of_mem _ member)
    | field _ member field ih => exact .field ih member field
  · simpa [State.bind, References] using wf.referencesUnique
  · simpa [State.bind, References, Allocated] using wf.referencesComplete

theorem Take.bind_preserves (wf : WellFormed classes before)
    (take : Take before place object after)
    (fresh : destination ∉ before.variables.map Prod.fst) :
    WellFormed classes (after.bind destination object) := by
  apply (take.preserves_pending wf.with_empty).bind
  simpa [take.variable_keys] using fresh

private theorem allocation_references (state : State)
    (lengths : objects.length = fields.length) :
    References (state.allocate className fields objects) =
      slotReferences state.variables ++ objects ++
        state.objects.flatMap (fun entry => slotReferences entry.2.fields) := by
  simp [State.allocate, References, slotReferences, List.append_assoc,
    zipped_field_references fields objects lengths]

theorem WellFormedWith.allocate (classesWf : ClassesWellFormed classes)
    (wf : WellFormedWith classes state (objects ++ pending))
    (declared : (className, declaration) ∈ classes)
    (lengths : objects.length = declaration.fields.length) :
    WellFormedWith classes (state.allocate className declaration.fields objects)
      (ObjectId.mk state.nextId :: pending) := by
  have freshObject : ObjectId.mk state.nextId ∉ state.objects.map Prod.fst := by
    intro member
    obtain ⟨⟨id, data⟩, allocated, same⟩ := List.mem_map.mp member
    simp only at same
    subst id
    exact Nat.lt_irrefl _ (wf.bounds _ _ allocated)
  have freshReference : ObjectId.mk state.nextId ∉ (objects ++ pending) ++ References state := by
    intro member
    exact freshObject ((wf.referencesComplete _).mp member)
  have references : (ObjectId.mk state.nextId :: ((objects ++ pending) ++ References state)).Perm
      ((ObjectId.mk state.nextId :: pending) ++
        References (state.allocate className declaration.fields objects)) := by
    apply List.Perm.cons
    rw [allocation_references state lengths]
    apply List.perm_iff_count.mpr
    intro id
    simp only [List.append_eq, References, slotReferences, List.count_append]
    omega
  constructor
  · simpa [State.allocate] using List.nodup_cons.mpr ⟨freshObject, wf.objectKeys⟩
  · exact wf.variableKeys
  · intro id data member
    rcases List.mem_cons.mp member with same | old
    · cases same
      exact ⟨declaration, declared, zipped_field_names _ _ lengths,
        classesWf.2 _ _ declared⟩
    · exact wf.shapes id data old
  · intro id data member
    rcases List.mem_cons.mp member with same | old
    · cases same
      exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (wf.bounds id data old)
  · intro id allocated
    rcases List.mem_cons.mp allocated with same | oldAllocated
    · subst id
      exact .pending (by simp)
    · have live := wf.rooted id oldAllocated
      clear allocated oldAllocated
      induction live with
      | @pending current member =>
        rcases List.mem_append.mp member with argument | pending
        · have fieldMember : current ∈ slotReferences (declaration.fields.zip (objects.map some)) := by
            rwa [zipped_field_references _ _ lengths]
          obtain ⟨⟨name, slot⟩, field, value⟩ := List.mem_filterMap.mp fieldMember
          dsimp at value
          subst slot
          exact .field (parent := ⟨state.nextId⟩) (data := ⟨className, declaration.fields.zip (objects.map some)⟩) (.pending (by simp)) (by simp [State.allocate]) field
        · exact .pending (List.mem_cons_of_mem _ pending)
      | «variable» member => exact .variable member
      | field _ member field ih => exact .field ih (List.mem_cons_of_mem _ member) field
  · exact references.nodup_iff.mp (List.nodup_cons.mpr ⟨freshReference, wf.referencesUnique⟩)
  · intro id
    rw [← references.mem_iff]
    simp only [List.mem_cons, wf.referencesComplete, Allocated, State.allocate, List.map_cons]

theorem Eval.preserves_pending (classesWf : ClassesWellFormed classes)
    (evaluation : Eval classes before value after object) :
    ∀ pending, WellFormedWith classes before pending →
      WellFormedWith classes after (object :: pending) := by
  induction evaluation using Eval.rec
    (motive_2 := fun before _ after objects _ => ∀ pending,
      WellFormedWith classes before pending →
        WellFormedWith classes after (objects ++ pending)) with
  | give _ take => exact fun _ wf => take.preserves_pending wf
  | new declared _ lengths _ ih =>
    exact fun pending wf => (ih pending wf).allocate classesWf declared lengths
  | nil => assumption
  | cons _ _ first rest =>
    rename_i pending wf
    have result := rest _ (first pending wf)
    exact result.perm List.perm_middle

theorem Eval.variable_keys (evaluation : Eval classes before value after object) :
    after.variables.map Prod.fst = before.variables.map Prod.fst := by
  induction evaluation using Eval.rec
    (motive_2 := fun before _ after _ _ =>
      after.variables.map Prod.fst = before.variables.map Prod.fst) with
  | give _ take => exact take.variable_keys
  | new _ _ _ _ ih => exact ih
  | nil => rfl
  | cons _ _ first rest => exact rest.trans first

theorem EvalArgs.length (evaluation : EvalArgs classes before arguments after objects) :
    objects.length = arguments.length := by
  induction evaluation using EvalArgs.rec
    (motive_1 := fun _ _ _ _ _ => True) with
  | give => trivial
  | new => trivial
  | nil => rfl
  | cons _ _ _ rest => simpa using rest

theorem Step.preserves_wellFormed (classesWf : ClassesWellFormed classes)
    (wf : WellFormed classes before.state) (step : Step classes before after) :
    WellFormed classes after.state := by
  cases step with
  | letValue fresh evaluation =>
    exact (evaluation.preserves_pending classesWf [] wf.with_empty).bind fresh

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

end Dada.Unique
