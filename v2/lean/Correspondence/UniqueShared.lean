import Unique.Step
import Shared.Step

namespace Dada.Correspondence

def embedId (object : Unique.ObjectId) : Shared.ObjectId := ⟨object.index⟩
def eraseId (object : Shared.ObjectId) : Unique.ObjectId := ⟨object.index⟩

@[simp] theorem erase_embed_id (object : Unique.ObjectId) : eraseId (embedId object) = object := rfl
@[simp] theorem embed_erase_id (object : Shared.ObjectId) : embedId (eraseId object) = object := rfl
@[simp] theorem embed_id_inj {a b : Unique.ObjectId} : embedId a = embedId b ↔ a = b := by
  constructor
  · exact fun h => congrArg eraseId h
  · exact congrArg embedId

def embedReference (object : Unique.ObjectId) : Shared.Reference := .owned (embedId object)
def eraseReference (reference : Shared.Reference) : Unique.ObjectId := eraseId reference.object

@[simp] theorem erase_embed_reference (object : Unique.ObjectId) :
    eraseReference (embedReference object) = object := rfl

def embedSlots {Key : Type} (slots : List (Key × Unique.Slot)) : List (Key × Shared.Slot) :=
  slots.map (fun entry => (entry.1, entry.2.map embedReference))

def eraseSlots {Key : Type} (slots : List (Key × Shared.Slot)) : List (Key × Unique.Slot) :=
  slots.map (fun entry => (entry.1, entry.2.map eraseReference))

def embedObject (object : Unique.Object) : Shared.Object :=
  ⟨object.className, embedSlots object.fields⟩

def eraseObject (object : Shared.Object) : Unique.Object :=
  ⟨object.className, eraseSlots object.fields⟩

def embedState (state : Unique.State) : Shared.State :=
  ⟨state.objects.map (fun entry => (embedId entry.1, embedObject entry.2)),
    embedSlots state.variables, state.nextId⟩

def eraseState (state : Shared.State) : Unique.State :=
  ⟨state.objects.map (fun entry => (eraseId entry.1, eraseObject entry.2)),
    eraseSlots state.variables, state.nextId⟩

def embedPlace : Unique.Place → Shared.Place
  | .variable name => .variable name
  | .field base name => .field (embedPlace base) name

def erasePlace : Shared.Place → Unique.Place
  | .variable name => .variable name
  | .field base name => .field (erasePlace base) name

def embedStorage : Unique.StoragePlace → Shared.StoragePlace
  | .variable name => .variable name
  | .field object name => .field (embedId object) name

def eraseStorage : Shared.StoragePlace → Unique.StoragePlace
  | .variable name => .variable name
  | .field object name => .field (eraseId object) name

def embedValue : Unique.Value → Shared.Value
  | .give source => .give (embedPlace source)
  | .new name arguments => .new name (arguments.map embedValue)

def embedStatement (statement : Unique.Statement) : Shared.Statement :=
  ⟨statement.destination, embedValue statement.value⟩

def embedClasses (classes : Unique.Classes) : Shared.Classes :=
  classes.map (fun entry => (entry.1, ⟨entry.2.fields, .classType⟩))

def embedProgram (program : Unique.Program) : Shared.Program :=
  ⟨embedClasses program.classes, program.body.map embedStatement⟩

def embedConfiguration (configuration : Unique.Configuration) : Shared.Configuration :=
  ⟨embedState configuration.state, configuration.code.map embedStatement⟩

section Proofs

@[simp] theorem erase_embed_slots {Key : Type} (slots : List (Key × Unique.Slot)) :
    eraseSlots (embedSlots slots) = slots := by
  induction slots with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨key, slot⟩
    cases slot <;> simpa [embedSlots, eraseSlots, embedReference, eraseReference, embedId, eraseId, Shared.Reference.owned] using ih

@[simp] theorem erase_embed_state (state : Unique.State) : eraseState (embedState state) = state := by
  cases state
  simp [eraseState, embedState, eraseObject, embedObject, List.map_map, Function.comp_def]

@[simp] theorem erase_embed_place (place : Unique.Place) : erasePlace (embedPlace place) = place := by
  induction place with
  | «variable» => rfl
  | field base name ih => simp [embedPlace, erasePlace, ih]

@[simp] theorem erase_embed_storage (place : Unique.StoragePlace) :
    eraseStorage (embedStorage place) = place := by cases place <;> rfl

def PureSlots {Key : Type} (slots : List (Key × Shared.Slot)) : Prop :=
  ∀ key reference, (key, some reference) ∈ slots → reference.mode = .unique

def Pure (state : Shared.State) : Prop :=
  PureSlots state.variables ∧
    ∀ object data, (object, data) ∈ state.objects → PureSlots data.fields

@[simp] theorem pure_slots_append {Key : Type} (left right : List (Key × Shared.Slot)) :
    PureSlots (left ++ right) ↔ PureSlots left ∧ PureSlots right := by
  simp [PureSlots, List.mem_append, or_imp, forall_and]

@[simp] theorem pure_slots_cons {Key : Type} (key : Key) (slot : Shared.Slot)
    (rest : List (Key × Shared.Slot)) :
    PureSlots ((key, slot) :: rest) ↔
      (∀ reference, slot = some reference → reference.mode = .unique) ∧ PureSlots rest := by
  simp only [PureSlots, List.mem_cons, Prod.mk.injEq]
  constructor
  · intro h
    exact ⟨fun reference equal => h key reference (Or.inl ⟨rfl, equal.symm⟩),
      fun key reference member => h key reference (Or.inr member)⟩
  · rintro ⟨head, tail⟩ key reference (⟨rfl, equal⟩ | member)
    · exact head reference equal.symm
    · exact tail key reference member

theorem embed_slots_pure {Key : Type} (slots : List (Key × Unique.Slot)) :
    PureSlots (embedSlots slots) := by
  intro key reference member
  obtain ⟨⟨oldKey, oldSlot⟩, _, equal⟩ := List.mem_map.mp member
  cases oldSlot <;> simp_all [embedReference, Shared.Reference.owned]
  grind

theorem embed_pure (state : Unique.State) : Pure (embedState state) := by
  constructor
  · exact embed_slots_pure _
  · intro object data member
    obtain ⟨⟨id, old⟩, _, equal⟩ := List.mem_map.mp member
    cases equal
    exact embed_slots_pure _

theorem pure_slots_roundtrip {Key : Type} {slots : List (Key × Shared.Slot)} (pure : PureSlots slots) :
    embedSlots (eraseSlots slots) = slots := by
  induction slots with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨key, slot⟩
    have parts := (pure_slots_cons key slot rest).mp pure
    cases slot with
    | none => simpa [embedSlots, eraseSlots] using ih parts.2
    | some reference =>
      cases reference with
      | reference mode object =>
        have modeEq := parts.1 ⟨mode, object⟩ rfl
        cases modeEq
        simpa [embedSlots, eraseSlots, embedReference, eraseReference, embedId, eraseId, Shared.Reference.owned] using ih parts.2

theorem pure_roundtrip (pure : Pure state) : embedState (eraseState state) = state := by
  cases state with
  | mk objects variables next =>
    simp only [embedState, eraseState, List.map_map, Function.comp_def]
    congr 1
    · conv => rhs; rw [← List.map_id objects]
      apply List.map_congr_left
      intro entry member
      have roundtrip := pure_slots_roundtrip (pure.2 entry.1 entry.2 member)
      rcases entry with ⟨id, ⟨name, fields⟩⟩
      simpa [embedObject, eraseObject] using congrArg (fun fs => (id, Shared.Object.mk name fs)) roundtrip
    · exact pure_slots_roundtrip pure.1

theorem resolve_erase (resolved : Shared.Resolve state path source object mode) :
    Unique.Resolve (eraseState state) (erasePlace path) (eraseStorage source) (eraseId object) := by
  induction resolved with
  | «variable» stored =>
    apply Unique.Resolve.variable
    exact List.mem_map.mpr ⟨(_, _), stored, rfl⟩
  | field base allocated stored ih =>
    apply Unique.Resolve.field ih (data := eraseObject _)
    · exact List.mem_map.mpr ⟨(_, _), allocated, rfl⟩
    · exact List.mem_map.mpr ⟨(_, _), stored, rfl⟩

theorem resolve_pure (pure : Pure state)
    (resolved : Shared.Resolve state path source object mode) : mode = .unique := by
  induction resolved with
  | «variable» stored => exact pure.1 _ _ stored
  | field base allocated stored ih =>
    rw [ih, pure.2 _ _ allocated _ _ stored]
    rfl

theorem take_erase (taken : Shared.Take before source object after) :
    Unique.Take (eraseState before) (eraseStorage source) (eraseId object) (eraseState after) := by
  cases taken with
  | «variable» objects next leading suffix name object =>
    simpa [eraseState, eraseSlots, eraseStorage, eraseReference, Shared.Reference.owned] using
      Unique.Take.variable (objects.map (fun e => (eraseId e.1, eraseObject e.2))) next
        (eraseSlots leading) (eraseSlots suffix) name (eraseId object)
  | field variables next before after parent className leading suffix name object =>
    simpa [eraseState, eraseSlots, eraseObject, eraseStorage, eraseReference, Shared.Reference.owned] using
      Unique.Take.field (eraseSlots variables) next
        (before.map (fun e => (eraseId e.1, eraseObject e.2)))
        (after.map (fun e => (eraseId e.1, eraseObject e.2))) (eraseId parent) className
        (eraseSlots leading) (eraseSlots suffix) name (eraseId object)

theorem take_pure (pure : Pure before) (taken : Shared.Take before source object after) :
    Pure after := by
  cases taken <;> simp_all [Pure, PureSlots, List.mem_append, List.mem_cons,
    Shared.Reference.owned, or_imp, forall_and] <;> grind

theorem resolve_forward (resolved : Unique.Resolve state path source object) :
    Shared.Resolve (embedState state) (embedPlace path) (embedStorage source) (embedId object) .unique := by
  induction resolved with
  | «variable» stored =>
    exact Shared.Resolve.variable (reference := embedReference _) (List.mem_map.mpr ⟨(_, _), stored, rfl⟩)
  | field base allocated stored ih =>
    exact Shared.Resolve.field (reference := embedReference _) ih
      (List.mem_map.mpr ⟨(_, _), allocated, rfl⟩) (List.mem_map.mpr ⟨(_, _), stored, rfl⟩)

theorem take_forward (taken : Unique.Take before source object after) :
    Shared.Take (embedState before) (embedStorage source) (embedId object) (embedState after) := by
  cases taken with
  | «variable» objects next leading suffix name object =>
    simpa [embedState, embedSlots, embedStorage, embedReference] using
      Shared.Take.variable (objects.map (fun e => (embedId e.1, embedObject e.2))) next
        (embedSlots leading) (embedSlots suffix) name (embedId object)
  | field variables next before after parent className leading suffix name object =>
    simpa [embedState, embedSlots, embedObject, embedStorage, embedReference] using
      Shared.Take.field (embedSlots variables) next
        (before.map (fun e => (embedId e.1, embedObject e.2)))
        (after.map (fun e => (embedId e.1, embedObject e.2))) (embedId parent) className
        (embedSlots leading) (embedSlots suffix) name (embedId object)

@[simp] theorem embed_slots_keys {Key : Type} (slots : List (Key × Unique.Slot)) :
    (embedSlots slots).map Prod.fst = slots.map Prod.fst := by
  simp [embedSlots, List.map_map, Function.comp_def]

@[simp] theorem embed_bind (state : Unique.State) (name : Unique.VariableId) (object : Unique.ObjectId) :
    embedState (state.bind name object) = (embedState state).bind name (embedReference object) := by
  rfl

@[simp] theorem erase_bind (state : Shared.State) (name : Shared.VariableId) (reference : Shared.Reference) :
    eraseState (state.bind name reference) = (eraseState state).bind name (eraseReference reference) := by
  rfl

theorem embed_fields (fields : List String) (objects : List Unique.ObjectId) :
    embedSlots (fields.zip (objects.map some)) =
      fields.zip ((objects.map embedReference).map some) := by
  induction fields generalizing objects with
  | nil => simp [embedSlots]
  | cons field fields ih =>
    cases objects with
    | nil => simp [embedSlots]
    | cons object objects => simpa [embedSlots] using ih objects

@[simp] theorem embed_allocate (state : Unique.State) (className : String)
    (fields : List String) (objects : List Unique.ObjectId) :
    embedState (state.allocate className fields objects) =
      (embedState state).allocate className fields (objects.map embedReference) := by
  simp [embedState, Unique.State.allocate, Shared.State.allocate, embedObject, embed_fields, embedId]

@[simp] theorem embed_nextId (state : Unique.State) :
    (embedState state).nextId = state.nextId := rfl

@[simp] theorem embed_object_fresh (state : Unique.State) :
    Shared.ObjectId.mk state.nextId ∉ (embedState state).objects.map Prod.fst ↔
      Unique.ObjectId.mk state.nextId ∉ state.objects.map Prod.fst := by
  have keys : (embedState state).objects.map Prod.fst =
      (state.objects.map Prod.fst).map embedId := by
    simp [embedState, List.map_map, Function.comp_def]
  change embedId ⟨state.nextId⟩ ∉ _ ↔ _
  rw [keys]
  simp only [List.mem_map, embed_id_inj, exists_eq_right]

-- Giving from an embedded graph cannot take either shared-copy case.
theorem give_backward (given : Shared.Give (embedState state) (embedPlace path) reference after) :
    ∃ source object, Unique.Resolve state path source object ∧
      Unique.Take state source object (eraseState after) ∧
      reference = embedReference object ∧ embedState (eraseState after) = after := by
  cases given with
  | move resolved taken =>
    exact ⟨_, _, by simpa using resolve_erase resolved,
      by simpa using take_erase taken, rfl, pure_roundtrip (take_pure (embed_pure _) taken)⟩
  | copy resolved stored => cases resolve_pure (embed_pure _) resolved
  | promote resolved promoted => cases resolve_pure (embed_pure _) resolved

theorem eval_forward (evaluated : Unique.Eval classes before value after object) :
    Shared.Eval (embedClasses classes) (embedState before) (embedValue value)
      (embedState after) (embedReference object) := by
  induction evaluated using Unique.Eval.rec
      (motive_2 := fun before values after objects _ =>
        Shared.EvalArgs (embedClasses classes) (embedState before) (values.map embedValue)
          (embedState after) (objects.map embedReference)) with
  | give resolved taken =>
    simpa only [embedValue, embedReference] using
      Shared.Eval.give (classes := embedClasses classes)
        (Shared.Give.move (resolve_forward resolved) (take_forward taken))
  | @new state evaluated className declaration arguments objects declared args lengths fresh ih =>
    simpa only [embedValue, embed_allocate, embedReference, embedId, embedClasses, embed_nextId, Shared.Kind.mode, Shared.Reference.owned] using
      Shared.Eval.new (declaration := ⟨declaration.fields, .classType⟩)
        (List.mem_map.mpr ⟨(_, _), declared, rfl⟩)
        ih (by simpa using lengths) ((embed_object_fresh evaluated).mpr fresh) (by simp [Shared.StructArguments, Shared.Kind.isStruct])
  | nil state => exact Shared.EvalArgs.nil (embedState state)
  | cons first rest firstIH restIH => exact Shared.EvalArgs.cons firstIH restIH

theorem eval_args_forward (evaluated : Unique.EvalArgs classes before values after objects) :
    Shared.EvalArgs (embedClasses classes) (embedState before) (values.map embedValue)
      (embedState after) (objects.map embedReference) := by
  induction values generalizing before after objects with
  | nil => cases evaluated; exact Shared.EvalArgs.nil _
  | cons argument arguments ih =>
    cases evaluated with
    | cons first rest => exact Shared.EvalArgs.cons (eval_forward first) (ih rest)

-- Reflection starts with an arbitrary Shared result. Pure input syntax and
-- storage force both its value and its resulting storage back into the image.
private theorem eval_backward_aux
    (evaluated : Shared.Eval (embedClasses classes) before value after reference) :
    ∀ original expression, before = embedState original → value = embedValue expression →
      ∃ result object, Unique.Eval classes original expression result object ∧
        after = embedState result ∧ reference = embedReference object := by
  induction evaluated using Shared.Eval.rec
      (motive_2 := fun before values after references _ =>
        ∀ original expressions, before = embedState original → values = expressions.map embedValue →
          ∃ result objects, Unique.EvalArgs classes original expressions result objects ∧
            after = embedState result ∧ references = objects.map embedReference) with
  | give given =>
    intro original expression beforeEq valueEq
    subst beforeEq
    cases expression with
    | give path =>
      simp only [embedValue, Shared.Value.give.injEq] at valueEq
      subst valueEq
      obtain ⟨source, object, resolved, taken, resultEq, roundtrip⟩ := give_backward given
      exact ⟨_, object, Unique.Eval.give resolved taken, roundtrip.symm, resultEq⟩
    | new name arguments => simp [embedValue] at valueEq
  | giveShare given _ =>
    intro original expression beforeEq valueEq
    cases expression <;> simp [embedValue] at valueEq
  | @new state evaluated className declaration arguments references declared args lengths fresh _ ih =>
    intro original expression beforeEq valueEq
    cases expression with
    | give path => simp [embedValue] at valueEq
    | new originalName originalArguments =>
      simp only [embedValue, Shared.Value.new.injEq] at valueEq
      obtain ⟨nameEq, argumentsEq⟩ := valueEq
      subst nameEq
      obtain ⟨result, objects, originalArgs, resultEq, referencesEq⟩ :=
        ih original originalArguments beforeEq argumentsEq
      subst resultEq
      subst referencesEq
      obtain ⟨⟨oldName, oldDeclaration⟩, originalDeclared, same⟩ := List.mem_map.mp declared
      simp only [Prod.mk.injEq] at same
      rcases same with ⟨rfl, rfl⟩
      refine ⟨result.allocate oldName oldDeclaration.fields objects, ⟨result.nextId⟩,
        Unique.Eval.new originalDeclared originalArgs (by simpa using lengths)
          ((embed_object_fresh result).mp fresh), ?_, rfl⟩
      exact (embed_allocate result oldName oldDeclaration.fields objects).symm
  | nil state =>
    rename_i original expressions beforeEq valuesEq
    cases expressions with
    | nil => exact ⟨original, [], Unique.EvalArgs.nil original, beforeEq, rfl⟩
    | cons head tail => simp at valuesEq
  | cons first rest firstIH restIH =>
    rename_i original expressions beforeEq valuesEq
    cases expressions with
    | nil => simp at valuesEq
    | cons expression expressions =>
      simp only [List.map_cons, List.cons.injEq] at valuesEq
      obtain ⟨middle, object, originalFirst, middleEq, objectEq⟩ :=
        firstIH original expression beforeEq valuesEq.1
      obtain ⟨result, objects, originalRest, resultEq, objectsEq⟩ :=
        restIH middle expressions middleEq valuesEq.2
      exact ⟨result, object :: objects, Unique.EvalArgs.cons originalFirst originalRest,
        resultEq, by simp [objectEq, objectsEq]⟩

theorem eval_backward
    (evaluated : Shared.Eval (embedClasses classes) (embedState before)
      (embedValue value) after reference) :
    ∃ result object, Unique.Eval classes before value result object ∧
      after = embedState result ∧ reference = embedReference object :=
  eval_backward_aux evaluated before value rfl rfl

theorem eval_args_backward
    (evaluated : Shared.EvalArgs (embedClasses classes) (embedState before)
      (values.map embedValue) after references) :
    ∃ result objects, Unique.EvalArgs classes before values result objects ∧
      after = embedState result ∧ references = objects.map embedReference := by
  induction values generalizing before after references with
  | nil =>
    cases evaluated
    exact ⟨before, [], Unique.EvalArgs.nil before, rfl, rfl⟩
  | cons argument arguments ih =>
    cases evaluated with
    | cons first rest =>
      obtain ⟨middle, object, originalFirst, middleEq, referenceEq⟩ := eval_backward first
      rw [middleEq] at rest
      obtain ⟨result, objects, originalRest, resultEq, referencesEq⟩ := ih rest
      exact ⟨result, object :: objects, Unique.EvalArgs.cons originalFirst originalRest,
        resultEq, by simp [referenceEq, referencesEq]⟩

theorem eval_correspondence :
    Shared.Eval (embedClasses classes) (embedState before) (embedValue value) after reference ↔
      ∃ result object, Unique.Eval classes before value result object ∧
        after = embedState result ∧ reference = embedReference object := by
  constructor
  · exact eval_backward
  · rintro ⟨result, object, evaluated, rfl, rfl⟩
    exact eval_forward evaluated

theorem eval_args_correspondence :
    Shared.EvalArgs (embedClasses classes) (embedState before) (values.map embedValue) after references ↔
      ∃ result objects, Unique.EvalArgs classes before values result objects ∧
        after = embedState result ∧ references = objects.map embedReference := by
  constructor
  · exact eval_args_backward
  · rintro ⟨result, objects, evaluated, rfl, rfl⟩
    exact eval_args_forward evaluated

theorem step_forward (step : Unique.Step classes before after) :
    Shared.Step (embedClasses classes) (embedConfiguration before) (embedConfiguration after) := by
  cases step with
  | letValue fresh evaluated =>
    simpa only [embedConfiguration, List.map_cons, embedStatement, embed_bind] using
      Shared.Step.letValue (by simpa only [embedState, embed_slots_keys] using fresh)
        (eval_forward evaluated)

-- The quantified successor is arbitrary, not assumed to be an embedding.
theorem step_backward (step : Shared.Step (embedClasses classes) (embedConfiguration before) after) :
    ∃ successor, Unique.Step classes before successor ∧ after = embedConfiguration successor := by
  rcases before with ⟨state, code⟩
  cases code with
  | nil => cases step
  | cons statement rest =>
    rcases statement with ⟨destination, value⟩
    change Shared.Step _ ⟨embedState state,
      ⟨destination, embedValue value⟩ :: rest.map embedStatement⟩ after at step
    cases step with
    | letValue fresh evaluated =>
      obtain ⟨result, object, original, resultEq, referenceEq⟩ := eval_backward evaluated
      subst resultEq
      subst referenceEq
      refine ⟨⟨result.bind destination object, rest⟩,
        Unique.Step.letValue (by simpa only [embedState, embed_slots_keys] using fresh) original, ?_⟩
      simp only [embedConfiguration, embed_bind]

-- The embedding preserves the complete program, including its remaining code.
theorem initial_correspondence (program : Unique.Program) :
    embedConfiguration (Unique.Configuration.initial program) =
      Shared.Configuration.initial (embedProgram program) := by rfl

theorem finished_correspondence (configuration : Unique.Configuration) :
    (embedConfiguration configuration).finished ↔ configuration.finished := by
  simp [Shared.Configuration.finished, Unique.Configuration.finished, embedConfiguration]


theorem stuck_correspondence (classes : Unique.Classes) (configuration : Unique.Configuration) :
    Shared.Stuck (embedClasses classes) (embedConfiguration configuration) ↔
      Unique.Stuck classes configuration := by
  constructor
  · rintro ⟨unfinished, noStep⟩
    refine ⟨fun finished => unfinished ((finished_correspondence _).mpr finished), ?_⟩
    rintro ⟨after, step⟩
    exact noStep ⟨_, step_forward step⟩
  · rintro ⟨unfinished, noStep⟩
    refine ⟨fun finished => unfinished ((finished_correspondence _).mp finished), ?_⟩
    rintro ⟨after, step⟩
    obtain ⟨successor, original, _⟩ := step_backward step
    exact noStep ⟨successor, original⟩

theorem steps_forward (steps : Unique.Steps classes before after) :
    Shared.Steps (embedClasses classes) (embedConfiguration before) (embedConfiguration after) := by
  induction steps with
  | refl => exact Shared.Steps.refl _
  | step first _ ih => exact Shared.Steps.step (step_forward first) ih

theorem steps_backward (steps : Shared.Steps (embedClasses classes) (embedConfiguration before) after) :
    ∃ successor, Unique.Steps classes before successor ∧ after = embedConfiguration successor := by
  generalize startEq : embedConfiguration before = start at steps
  induction steps generalizing before with
  | refl configuration => exact ⟨before, .refl before, startEq.symm⟩
  | step first rest ih =>
    rw [← startEq] at first
    obtain ⟨middle, original, same⟩ := step_backward first
    obtain ⟨last, suffix, final⟩ := ih same.symm
    exact ⟨last, .step original suffix, final⟩

-- One-step bisimulation of the image of the unique language.
theorem step_correspondence :
    Shared.Step (embedClasses classes) (embedConfiguration before) after ↔
      ∃ successor, Unique.Step classes before successor ∧ after = embedConfiguration successor := by
  constructor
  · exact step_backward
  · rintro ⟨successor, original, rfl⟩
    exact step_forward original

theorem steps_correspondence :
    Shared.Steps (embedClasses classes) (embedConfiguration before) after ↔
      ∃ successor, Unique.Steps classes before successor ∧ after = embedConfiguration successor := by
  constructor
  · exact steps_backward
  · rintro ⟨successor, original, rfl⟩
    exact steps_forward original

-- Execution boundaries agree as well as individual transitions.
theorem boundary_correspondence (program : Unique.Program) :
    embedConfiguration (Unique.Configuration.initial program) =
      Shared.Configuration.initial (embedProgram program) ∧
    ∀ configuration : Unique.Configuration,
      ((embedConfiguration configuration).finished ↔ configuration.finished) ∧
      (Shared.Stuck (embedClasses program.classes) (embedConfiguration configuration) ↔
        Unique.Stuck program.classes configuration) :=
  ⟨initial_correspondence program,
    fun configuration => ⟨finished_correspondence configuration,
      stuck_correspondence program.classes configuration⟩⟩

end Proofs

end Dada.Correspondence
