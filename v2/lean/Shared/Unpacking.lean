import Shared.Liveness

namespace Dada.Shared.Unpacking

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

structure Configuration where
  state : State
  code : List Statement
  deriving Repr

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
inductive Bind (classes : Classes) : State → Reference → Pattern → State → Prop where
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
        (.owned object) (.unpack className pattern)
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

private abbrev slotOwners {K : Type} (slots : List (K × Slot)) : List Reference :=
  slots.filterMap (fun entry => entry.2)

theorem Transfer.owners (transfer : Transfer pattern fields bindings) :
    (slotOwners bindings).Perm (slotOwners fields) := by
  simpa [slotOwners, List.filterMap_map, Function.comp_def] using
    transfer.slots.filterMap id

private theorem owners_targets (state : State) :
    (Owners state).map Reference.object = References state := by
  simp [Owners, References, List.map_filterMap, List.map_flatMap]

private theorem compatible_symm {first second : Reference} (h : Compatible first second) :
    Compatible second first := by
  rcases h with different | shared
  · exact Or.inl (Ne.symm different)
  · exact Or.inr ⟨shared.2, shared.1⟩

-- Relocating the fields changes where their references occur, not which
-- references remain. The consumed container is the separate pending root.
theorem unpack_owners
    (transfer : Transfer pattern fields bindings)
    (before after : List (ObjectId × Object)) (variables : List (VariableId × Slot))
    (nextId : Nat) (object : ObjectId) (className : ClassName) :
    (Owners ⟨before ++ (object, ⟨className, fields⟩) :: after, variables, nextId⟩).Perm
      (Owners ⟨before ++ after, bindings ++ variables, nextId⟩) := by
  apply List.perm_iff_count.mpr
  intro reference
  have same := transfer.owners.count_eq reference
  simp only [Owners, List.filterMap_append, List.flatMap_append, List.flatMap_cons,
    List.count_append] at *
  change List.count reference (slotOwners variables) +
      (List.count reference (before.flatMap fun e => slotOwners e.2.fields) +
        (List.count reference (slotOwners fields) +
          List.count reference (after.flatMap fun e => slotOwners e.2.fields))) =
    (List.count reference (slotOwners bindings) + List.count reference (slotOwners variables)) +
      (List.count reference (before.flatMap fun e => slotOwners e.2.fields) +
        List.count reference (after.flatMap fun e => slotOwners e.2.fields))
  omega

theorem Bind.preserves_wellFormed
    (binding : Bind classes before reference pattern after)
    (wf : WellFormedWith classes before [reference]) : WellFormed classes after := by
  cases binding with
  | «variable» fresh =>
    refine ⟨wf.objectKeys, ?_, wf.shapes, wf.bounds, wf.older, ?_, ?_⟩
    · simpa [State.bind] using List.nodup_cons.mpr ⟨fresh, wf.variableKeys⟩
    · simpa [State.bind, Owners] using wf.ownersCompatible
    · simpa [State.bind, References, Allocated] using wf.referencesComplete
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
    have compatible : (Reference.owned object :: Owners
        ⟨before ++ after, bindings ++ variables, nextId⟩).Pairwise Compatible := by
      exact (List.Perm.cons _ owners).pairwise wf.ownersCompatible compatible_symm
    have absentReference : object ∉ References
        ⟨before ++ after, bindings ++ variables, nextId⟩ := by
      rw [← owners_targets]
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
    · intro id data name target member field
      exact wf.older id data name target (subset _ member) field
    · exact compatible.of_cons
    · intro id
      have complete := wf.referencesComplete id
      simp only [List.map_cons, List.map_nil, List.singleton_append, List.mem_cons,
        Reference.owned, Allocated, List.map_append, List.mem_append] at complete
      change id ∈ References ⟨before ++ after, bindings ++ variables, nextId⟩ ↔
        id ∈ (before ++ after).map Prod.fst
      by_cases same : id = object
      · subst id
        simp [absentReference, List.map_append, removedAbsent]
      · rw [← refs.mem_iff]
        simpa [same, List.map_append] using complete

theorem Step.preserves_wellFormed (classesWf : ClassesWellFormed classes)
    (wf : WellFormed classes before.state) (step : Step classes before after) :
    WellFormed classes after.state := by
  cases step with
  | letValue evaluation binding =>
    exact binding.preserves_wellFormed
      (evaluation.preserves_wellFormedWith classesWf wf.with_pending)

theorem Steps.preserves_wellFormed (classesWf : ClassesWellFormed classes)
    (wf : WellFormed classes before.state) (steps : Steps classes before after) :
    WellFormed classes after.state := by
  induction steps with
  | refl => exact wf
  | step first _ ih => exact ih (first.preserves_wellFormed classesWf wf)

def embedStatement (statement : Dada.Shared.Statement) : Statement :=
  ⟨.variable statement.destination, statement.value⟩

def embedConfiguration (configuration : Dada.Shared.Configuration) : Configuration :=
  ⟨configuration.state, configuration.code.map embedStatement⟩

theorem embed_step (step : Dada.Shared.Step classes before after) :
    Step classes (embedConfiguration before) (embedConfiguration after) := by
  cases step with
  | letValue fresh evaluation => exact .letValue evaluation (.variable fresh)

-- There is no new transition available to a program containing only the old
-- variable patterns, even when the successor is not assumed to be embedded.
theorem reflect_step (step : Step classes (embedConfiguration before) after) :
    ∃ next, Dada.Shared.Step classes before next ∧ after = embedConfiguration next := by
  rcases before with ⟨state, code⟩
  cases code with
  | nil => cases step
  | cons statement rest =>
    rcases statement with ⟨destination, value⟩
    cases step with
    | letValue evaluation binding =>
      cases binding with
      | «variable» fresh => exact ⟨_, .letValue fresh evaluation, rfl⟩

theorem embed_steps (steps : Dada.Shared.Steps classes before after) :
    Steps classes (embedConfiguration before) (embedConfiguration after) := by
  induction steps with
  | refl => exact .refl _
  | step first _ ih => exact .step (embed_step first) ih

theorem embed_finished : (embedConfiguration configuration).finished ↔ configuration.finished := by
  simp [embedConfiguration, Configuration.finished, Dada.Shared.Configuration.finished]

theorem Step.code_length (step : Step classes before after) :
    before.code.length = after.code.length + 1 := by
  cases step
  rfl


theorem reflect_steps (trace : Steps classes (embedConfiguration before) after) :
    ∃ next, Dada.Shared.Steps classes before next ∧ after = embedConfiguration next := by
  generalize initialEq : embedConfiguration before = initial at trace
  induction trace generalizing before with
  | refl => exact ⟨before, .refl _, initialEq.symm⟩
  | step first _ rest =>
    rw [← initialEq] at first
    obtain ⟨middle, reflected, rfl⟩ := reflect_step first
    obtain ⟨next, remainder, rfl⟩ := rest rfl
    exact ⟨next, .step reflected remainder, rfl⟩

theorem embed_stuck : Stuck classes (embedConfiguration configuration) ↔
    Dada.Shared.Stuck classes configuration := by
  constructor
  · rintro ⟨unfinished, noStep⟩
    refine ⟨fun finished => unfinished (embed_finished.mpr finished), ?_⟩
    rintro ⟨after, step⟩
    exact noStep ⟨embedConfiguration after, embed_step step⟩
  · rintro ⟨unfinished, noStep⟩
    refine ⟨fun finished => unfinished (embed_finished.mp finished), ?_⟩
    rintro ⟨after, step⟩
    obtain ⟨next, reflected, _⟩ := reflect_step step
    exact noStep ⟨next, reflected⟩

-- The unique mode is intrinsic to unpacking, even in a state with no aliases.
theorem Bind.unpack_requires_unique
    (binding : Bind classes before reference (.unpack name fields) after) :
    reference.mode = .unique := by
  cases binding
  rfl

theorem shared_cannot_unpack :
    ¬ Bind classes before (.shared object) (.unpack name fields) after := by
  intro binding
  cases binding.unpack_requires_unique

theorem Steps.live_iff_allocated (classesWf : ClassesWellFormed classes)
    (wf : WellFormed classes before.state) (trace : Steps classes before after) :
    Live after.state object ↔ Allocated after.state object :=
  (trace.preserves_wellFormed classesWf wf).live_iff_allocated

-- Counted executions make termination independent of how expression evaluation
-- is derived: one statement step consumes exactly one statement.
inductive StepsExactly (classes : Classes) : Configuration → Nat → Configuration → Prop where
  | refl (configuration : Configuration) : StepsExactly classes configuration 0 configuration
  | step {before middle after : Configuration} {count : Nat} :
      Step classes before middle → StepsExactly classes middle count after →
      StepsExactly classes before (count + 1) after

theorem StepsExactly.steps (trace : StepsExactly classes before count after) :
    Steps classes before after := by
  induction trace with
  | refl => exact .refl _
  | step first _ rest => exact .step first rest

theorem StepsExactly.length (trace : StepsExactly classes before count after) :
    before.code.length = count + after.code.length := by
  induction trace with
  | refl => simp
  | step first _ rest => have shorter := first.code_length; omega

theorem StepsExactly.trans (first : StepsExactly classes before count middle)
    (second : StepsExactly classes middle later after) :
    StepsExactly classes before (count + later) after := by
  induction first with
  | refl => simpa using second
  | step firstStep _ rest =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (StepsExactly.step firstStep (rest second))

theorem Steps.counted (trace : Steps classes before after) :
    ∃ count, StepsExactly classes before count after := by
  induction trace with
  | refl => exact ⟨0, .refl _⟩
  | step first _ rest =>
    obtain ⟨count, trace⟩ := rest
    exact ⟨count + 1, .step first trace⟩

end Dada.Shared.Unpacking
