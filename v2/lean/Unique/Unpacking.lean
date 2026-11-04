import Unique.Soundness

namespace Dada.Unique.Unpacking

-- Patterns consume an expression result; they are not value expressions.
inductive Pattern where
  | variable (name : VariableId)
  | unpack (className : ClassName) (fields : List (FieldName × VariableId))
  deriving DecidableEq, Repr

def Pattern.variables : Pattern → List VariableId
  | .variable name => [name]
  | .unpack _ fields => fields.map Prod.snd

structure Statement where
  pattern : Pattern
  value : Value
  deriving Repr

-- Auxiliary observation for one frame, also used before the final frame-pop step.
structure Configuration where
  state : State
  code : List Statement
  deriving Repr

-- Local code exhaustion, not completion of the framed program machine.
def Configuration.finished (configuration : Configuration) : Prop :=
  configuration.code = []

-- Choose each named field exactly once, in pattern order. Empty slots are
-- transferred too. The empty case requires that no field was left behind.
inductive Transfer : List (FieldName × VariableId) → List (FieldName × Slot) → List (VariableId × Slot) → Prop where
  | nil : Transfer [] [] []
  | cons {field name slot pattern before after bindings} :
      Transfer pattern (before ++ after) bindings →
      Transfer ((field, name) :: pattern) (before ++ (field, slot) :: after)
        ((name, slot) :: bindings)

-- Binding itself neither evaluates an expression nor assumes an invariant.
inductive Bind (classes : Classes) : State → ObjectId → Pattern → State → Prop where
  | variable {state object name} :
      name ∉ state.variables.map Prod.fst →
      Bind classes state object (.variable name) (state.bind name object)
  | unpack {before after variables nextId object className fields pattern bindings declaration} :
      (className, declaration) ∈ classes →
      fields.map Prod.fst = declaration.fields →
      (pattern.map Prod.fst).Nodup →
      (pattern.map Prod.snd).Nodup →
      (∀ name ∈ pattern.map Prod.snd, name ∉ variables.map Prod.fst) →
      Transfer pattern fields bindings →
      Bind classes ⟨before ++ (object, ⟨className, fields⟩) :: after, variables, nextId⟩
        object (.unpack className pattern)
        ⟨before ++ after, bindings ++ variables, nextId⟩

inductive Step (classes : Classes) : Configuration → Configuration → Prop where
  | letValue {before evaluated after pattern value object rest} :
      Eval classes before value evaluated object →
      Bind classes evaluated object pattern after →
      Step classes ⟨before, ⟨pattern, value⟩ :: rest⟩ ⟨after, rest⟩

inductive Steps (classes : Classes) : Configuration → Configuration → Prop where
  | refl (configuration : Configuration) : Steps classes configuration configuration
  | step {before middle after} :
      Step classes before middle → Steps classes middle after → Steps classes before after

def Stuck (classes : Classes) (configuration : Configuration) : Prop :=
  ¬ configuration.finished ∧ ¬ ∃ after, Step classes configuration after

theorem Bind.fresh (binding : Bind classes before object pattern after) :
    ∀ name ∈ pattern.variables, name ∉ before.variables.map Prod.fst := by
  cases binding with
  | «variable» fresh => simpa [Pattern.variables] using fresh
  | unpack _ _ _ _ fresh _ => exact fresh

theorem Transfer.keys (transfer : Transfer pattern fields bindings) :
    bindings.map Prod.fst = pattern.map Prod.snd := by
  induction transfer with
  | nil => rfl
  | cons _ ih => simp [ih]

theorem Transfer.slots (transfer : Transfer pattern fields bindings) :
    (bindings.map Prod.snd).Perm (fields.map Prod.snd) := by
  induction transfer with
  | nil => exact .refl _
  | @cons field name slot pattern before after bindings _ ih =>
    simp only [List.map_append] at ih
    simpa using (List.Perm.cons slot ih).trans
      (List.perm_middle (a := slot) (l₁ := before.map Prod.snd)
        (l₂ := after.map Prod.snd)).symm

theorem Transfer.field_keys (transfer : Transfer pattern fields bindings) :
    (pattern.map Prod.fst).Perm (fields.map Prod.fst) := by
  induction transfer with
  | nil => exact .refl _
  | @cons field name slot pattern before after bindings _ ih =>
    simp only [List.map_append] at ih
    simpa using (List.Perm.cons field ih).trans
      (List.perm_middle (a := field) (l₁ := before.map Prod.fst)
        (l₂ := after.map Prod.fst)).symm

private abbrev slotReferences {K : Type} (slots : List (K × Slot)) : List ObjectId :=
  slots.filterMap (fun entry => entry.2)

theorem Transfer.references (transfer : Transfer pattern fields bindings) :
    (slotReferences bindings).Perm (slotReferences fields) := by
  simpa [slotReferences, List.filterMap_map, Function.comp_def] using
    transfer.slots.filterMap id

-- Relocating the fields changes where their references occur, not which
-- references remain. The consumed container is the separate pending root.
private theorem unpack_references
    (transfer : Transfer pattern fields bindings)
    (before after : List (ObjectId × Object)) (variables : List (VariableId × Slot))
    (nextId : Nat) (object : ObjectId) (className : ClassName) :
    (References ⟨before ++ (object, ⟨className, fields⟩) :: after, variables, nextId⟩).Perm
      (References ⟨before ++ after, bindings ++ variables, nextId⟩) := by
  apply List.perm_iff_count.mpr
  intro id
  have same := transfer.references.count_eq id
  simp only [References, List.filterMap_append, List.flatMap_append, List.flatMap_cons,
    List.count_append] at *
  change List.count id (slotReferences variables) +
      (List.count id (before.flatMap fun e => slotReferences e.2.fields) +
        (List.count id (slotReferences fields) +
          List.count id (after.flatMap fun e => slotReferences e.2.fields))) =
    (List.count id (slotReferences bindings) + List.count id (slotReferences variables)) +
      (List.count id (before.flatMap fun e => slotReferences e.2.fields) +
        List.count id (after.flatMap fun e => slotReferences e.2.fields))
  omega

theorem Bind.preserves_wellFormed
    (binding : Bind classes before object pattern after)
    (wf : WellFormedWith classes before [object]) : WellFormed classes after := by
  cases binding with
  | «variable» fresh => exact wf.bind fresh
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
    have refs := unpack_references transfer before after variables nextId object className
    have uniqueAfter : (object :: References
        ⟨before ++ after, bindings ++ variables, nextId⟩).Nodup := by
      exact (List.Perm.cons object refs).nodup_iff.mp wf.referencesUnique
    have transport : ∀ id,
        LiveWith ⟨before ++ (object, ⟨className, fields⟩) :: after, variables, nextId⟩ [object] id →
        id = object ∨ Live ⟨before ++ after, bindings ++ variables, nextId⟩ id := by
      intro id live
      induction live with
      | pending member => exact Or.inl (by simpa using member)
      | «variable» member => exact Or.inr (.variable (List.mem_append_right _ member))
      | @field parent target data name _ member field ih =>
        simp only [List.mem_append, List.mem_cons] at member
        rcases member with left | same | right
        · have liveParent := ih.resolve_left (by
            intro eq; subst parent
            exact removedAbsent (List.mem_append_left _ (List.mem_map.mpr ⟨_, left, rfl⟩)))
          exact Or.inr (.field liveParent (List.mem_append_left _ left) field)
        · cases same
          have fieldRef : target ∈ slotReferences fields := List.mem_filterMap.mpr ⟨_, field, rfl⟩
          have rootRef := transfer.references.mem_iff.mpr fieldRef
          obtain ⟨⟨localName, slot⟩, atRoot, value⟩ := List.mem_filterMap.mp rootRef
          dsimp at value
          subst slot
          exact Or.inr (.variable (List.mem_append_left _ atRoot))
        · have liveParent := ih.resolve_left (by
            intro eq; subst parent
            exact removedAbsent (List.mem_append_right _ (List.mem_map.mpr ⟨_, right, rfl⟩)))
          exact Or.inr (.field liveParent (List.mem_append_right _ right) field)
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
      have oldAllocated : Allocated ⟨before ++ (object, ⟨className, fields⟩) :: after, variables, nextId⟩ id := by
        obtain ⟨entry, member, same⟩ := List.mem_map.mp allocated
        exact List.mem_map.mpr ⟨entry, subset _ member, same⟩
      exact (transport id (wf.rooted id oldAllocated)).resolve_left (by
        intro eq; subst id
        exact removedAbsent (by simpa [Allocated, List.map_append] using allocated))
    · exact (List.nodup_cons.mp uniqueAfter).2
    · intro id
      have complete := wf.referencesComplete id
      simp only [List.singleton_append, List.mem_cons, Allocated, List.map_append,
        List.map_cons, List.mem_append] at complete
      change id ∈ References ⟨before ++ after, bindings ++ variables, nextId⟩ ↔
        id ∈ (before ++ after).map Prod.fst
      by_cases same : id = object
      · subst id
        have noRef := (List.nodup_cons.mp uniqueAfter).1
        simp [noRef, List.map_append, removedAbsent]
      · rw [← refs.mem_iff]
        simpa [same, List.map_append] using complete

theorem Step.preserves_wellFormed (classesWf : ClassesWellFormed classes)
    (wf : WellFormed classes before.state) (step : Step classes before after) :
    WellFormed classes after.state := by
  cases step with
  | letValue evaluation binding =>
    exact binding.preserves_wellFormed
      (evaluation.preserves_pending classesWf [] wf.with_empty)

theorem Steps.preserves_wellFormed (classesWf : ClassesWellFormed classes)
    (wf : WellFormed classes before.state) (steps : Steps classes before after) :
    WellFormed classes after.state := by
  induction steps with
  | refl => exact wf
  | step first _ ih => exact ih (first.preserves_wellFormed classesWf wf)

def embedStatement (statement : Dada.Unique.Statement) : Statement :=
  ⟨.variable statement.destination, statement.value⟩

def embedConfiguration (configuration : Dada.Unique.Configuration) : Configuration :=
  ⟨configuration.state, configuration.code.map embedStatement⟩

theorem embed_step (step : Dada.Unique.Step classes before after) :
    Step classes (embedConfiguration before) (embedConfiguration after) := by
  cases step with
  | letValue fresh evaluation => exact .letValue evaluation (.variable fresh)

-- There is no new transition available to a program containing only the old
-- variable patterns, even when the successor is not assumed to be embedded.
theorem reflect_step (step : Step classes (embedConfiguration before) after) :
    ∃ next, Dada.Unique.Step classes before next ∧ after = embedConfiguration next := by
  rcases before with ⟨state, code⟩
  cases code with
  | nil => cases step
  | cons statement rest =>
    rcases statement with ⟨destination, value⟩
    cases step with
    | letValue evaluation binding =>
      cases binding with
      | «variable» fresh => exact ⟨_, .letValue fresh evaluation, rfl⟩

theorem embed_steps (steps : Dada.Unique.Steps classes before after) :
    Steps classes (embedConfiguration before) (embedConfiguration after) := by
  induction steps with
  | refl => exact .refl _
  | step first _ ih => exact .step (embed_step first) ih

theorem embed_finished : (embedConfiguration configuration).finished ↔ configuration.finished := by
  simp [embedConfiguration, Configuration.finished, Dada.Unique.Configuration.finished]

theorem Step.code_length (step : Step classes before after) :
    before.code.length = after.code.length + 1 := by
  cases step
  rfl

end Dada.Unique.Unpacking
