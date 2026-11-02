import Correspondence.UniqueShared
import Unique.Unpacking
import Shared.Unpacking

namespace Dada.Correspondence.Unpacking

def embedPattern : Unique.Unpacking.Pattern → Shared.Unpacking.Pattern
  | .variable name => .variable name
  | .unpack name fields => .unpack name fields

def erasePattern : Shared.Unpacking.Pattern → Unique.Unpacking.Pattern
  | .variable name => .variable name
  | .unpack name fields => .unpack name fields

@[simp] theorem erase_embed_pattern (pattern : Unique.Unpacking.Pattern) :
    erasePattern (embedPattern pattern) = pattern := by cases pattern <;> rfl

def embedStatement (statement : Unique.Unpacking.Statement) : Shared.Unpacking.Statement :=
  ⟨embedPattern statement.pattern, embedValue statement.value⟩

def embedConfiguration (configuration : Unique.Unpacking.Configuration) : Shared.Unpacking.Configuration :=
  ⟨embedState configuration.state, configuration.code.map embedStatement⟩

theorem transfer_forward (transferred : Unique.Unpacking.Transfer pattern fields bindings) :
    Shared.Unpacking.Transfer pattern (embedSlots fields) (embedSlots bindings) := by
  induction transferred with
  | nil => exact .nil
  | @cons field name slot pattern before after bindings rest ih =>
    simpa [embedSlots] using Shared.Unpacking.Transfer.cons
      (before := embedSlots before) (after := embedSlots after) (slot := slot.map embedReference) (by simpa [embedSlots] using ih)

theorem transfer_erase (transferred : Shared.Unpacking.Transfer pattern fields bindings) :
    Unique.Unpacking.Transfer pattern (eraseSlots fields) (eraseSlots bindings) := by
  induction transferred with
  | nil => exact .nil
  | @cons field name slot pattern before after bindings rest ih =>
    simpa [eraseSlots] using Unique.Unpacking.Transfer.cons
      (before := eraseSlots before) (after := eraseSlots after) (slot := slot.map eraseReference) (by simpa [eraseSlots] using ih)

theorem transfer_pure (transferred : Shared.Unpacking.Transfer pattern fields bindings)
    (pure : PureSlots fields) : PureSlots bindings := by
  intro name reference member
  have slotMember : some reference ∈ bindings.map Prod.snd :=
    List.mem_map.mpr ⟨(name, some reference), member, rfl⟩
  have fieldMember := transferred.slots.mem_iff.mp slotMember
  obtain ⟨⟨field, slot⟩, present, same⟩ := List.mem_map.mp fieldMember
  dsimp at same
  subst slot
  exact pure field reference present

theorem bind_forward (binding : Unique.Unpacking.Bind classes before object pattern after) :
    Shared.Unpacking.Bind (embedClasses classes) (embedState before)
      (embedReference object) (embedPattern pattern) (embedState after) := by
  cases binding with
  | «variable» fresh =>
    exact .variable (by simpa [embedState, embed_slots_keys] using fresh)
  | @unpack before after variables nextId object className fields pattern bindings declaration
      declared shape uniqueFields uniqueNames fresh transfer =>
    simpa [embedState, embedObject, embedSlots, embedPattern, embedReference, embedClasses] using
      Shared.Unpacking.Bind.unpack
        (before := before.map fun e => (embedId e.1, embedObject e.2))
        (after := after.map fun e => (embedId e.1, embedObject e.2))
        (variables := embedSlots variables) (nextId := nextId) (object := embedId object)
        (className := className) (fields := embedSlots fields) (pattern := pattern)
        (bindings := embedSlots bindings) (declaration := ⟨declaration.fields⟩)
        (List.mem_map.mpr ⟨(className, declaration), declared, rfl⟩)
        (by simpa using shape) uniqueFields uniqueNames (by simpa using fresh)
        (transfer_forward transfer)

@[simp] theorem erase_slots_keys {Key : Type} (slots : List (Key × Shared.Slot)) :
    (eraseSlots slots).map Prod.fst = slots.map Prod.fst := by
  simp [eraseSlots, List.map_map, Function.comp_def]

theorem bind_erase (binding : Shared.Unpacking.Bind (embedClasses classes) before reference pattern after) :
    Unique.Unpacking.Bind classes (eraseState before)
      (eraseReference reference) (erasePattern pattern) (eraseState after) := by
  cases binding with
  | «variable» fresh =>
    exact .variable (by simpa [eraseState, erase_slots_keys] using fresh)
  | @unpack before after variables nextId object className fields pattern bindings declaration
      declared shape uniqueFields uniqueNames fresh transfer =>
    obtain ⟨⟨originalName, original⟩, originalDeclared, same⟩ := List.mem_map.mp declared
    simp only [Prod.mk.injEq] at same
    rcases same with ⟨rfl, rfl⟩
    simpa [eraseState, eraseObject, eraseSlots, erasePattern, eraseReference,
        Shared.Reference.owned] using
      Unique.Unpacking.Bind.unpack
        (before := before.map fun e => (eraseId e.1, eraseObject e.2))
        (after := after.map fun e => (eraseId e.1, eraseObject e.2))
        (variables := eraseSlots variables) (nextId := nextId) (object := eraseId object)
        (className := originalName) (fields := eraseSlots fields) (pattern := pattern)
        (bindings := eraseSlots bindings) (declaration := original)
        originalDeclared (by simpa using shape) uniqueFields uniqueNames (by simpa using fresh)
        (transfer_erase transfer)

theorem bind_pure (binding : Shared.Unpacking.Bind classes before reference pattern after)
    (pure : Pure before) (unique : reference.mode = .unique) : Pure after := by
  cases binding with
  | «variable» fresh =>
    constructor
    · simpa only [Shared.State.bind, pure_slots_cons] using
        And.intro (fun other (same : some reference = some other) => by cases same; exact unique) pure.1
    · exact pure.2
  | @unpack before after variables nextId object className fields pattern bindings declaration
      declared shape uniqueFields uniqueNames fresh transfer =>
    constructor
    · rw [pure_slots_append]
      exact ⟨transfer_pure transfer (pure.2 object ⟨className, fields⟩ (by simp)), pure.1⟩
    · intro id data member
      apply pure.2 id data
      rcases List.mem_append.mp member with left | right
      · exact List.mem_append_left _ left
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ right)

theorem bind_backward
    (binding : Shared.Unpacking.Bind (embedClasses classes) (embedState before)
      (embedReference object) (embedPattern pattern) after) :
    ∃ result, Unique.Unpacking.Bind classes before object pattern result ∧
      after = embedState result := by
  exact ⟨eraseState after, by simpa using bind_erase binding,
    (pure_roundtrip (bind_pure binding (embed_pure before) rfl)).symm⟩

theorem step_forward (step : Unique.Unpacking.Step classes before after) :
    Shared.Unpacking.Step (embedClasses classes) (embedConfiguration before)
      (embedConfiguration after) := by
  cases step with
  | letValue evaluation binding => exact .letValue (eval_forward evaluation) (bind_forward binding)

theorem step_backward
    (step : Shared.Unpacking.Step (embedClasses classes) (embedConfiguration before) after) :
    ∃ successor, Unique.Unpacking.Step classes before successor ∧ after = embedConfiguration successor := by
  rcases before with ⟨state, code⟩
  cases code with
  | nil => cases step
  | cons statement rest =>
    rcases statement with ⟨pattern, value⟩
    cases step with
    | letValue evaluation binding =>
      obtain ⟨evaluated, object, original, rfl, rfl⟩ := eval_backward evaluation
      obtain ⟨result, bound, rfl⟩ := bind_backward binding
      exact ⟨⟨result, rest⟩, .letValue original bound, rfl⟩

theorem steps_forward (trace : Unique.Unpacking.Steps classes before after) :
    Shared.Unpacking.Steps (embedClasses classes) (embedConfiguration before)
      (embedConfiguration after) := by
  induction trace with
  | refl => exact .refl _
  | step first _ rest => exact .step (step_forward first) rest

theorem steps_backward
    (trace : Shared.Unpacking.Steps (embedClasses classes) (embedConfiguration before) after) :
    ∃ successor, Unique.Unpacking.Steps classes before successor ∧ after = embedConfiguration successor := by
  generalize startEq : embedConfiguration before = start at trace
  induction trace generalizing before with
  | refl => exact ⟨before, .refl _, startEq.symm⟩
  | step first _ rest =>
    rw [← startEq] at first
    obtain ⟨middle, original, same⟩ := step_backward first
    obtain ⟨last, suffix, final⟩ := rest same.symm
    exact ⟨last, .step original suffix, final⟩

theorem step_correspondence :
    Shared.Unpacking.Step (embedClasses classes) (embedConfiguration before) after ↔
      ∃ successor, Unique.Unpacking.Step classes before successor ∧ after = embedConfiguration successor := by
  constructor
  · exact step_backward
  · rintro ⟨successor, original, rfl⟩
    exact step_forward original

theorem steps_correspondence :
    Shared.Unpacking.Steps (embedClasses classes) (embedConfiguration before) after ↔
      ∃ successor, Unique.Unpacking.Steps classes before successor ∧ after = embedConfiguration successor := by
  constructor
  · exact steps_backward
  · rintro ⟨successor, original, rfl⟩
    exact steps_forward original

theorem finished_correspondence (configuration : Unique.Unpacking.Configuration) :
    (embedConfiguration configuration).finished ↔ configuration.finished := by
  simp [Shared.Unpacking.Configuration.finished, Unique.Unpacking.Configuration.finished,
    embedConfiguration]

theorem stuck_correspondence (classes : Unique.Classes) (configuration : Unique.Unpacking.Configuration) :
    Shared.Unpacking.Stuck (embedClasses classes) (embedConfiguration configuration) ↔
      Unique.Unpacking.Stuck classes configuration := by
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

theorem completion_correspondence (configuration : Unique.Unpacking.Configuration) :
    (∃ final, Shared.Unpacking.Steps (embedClasses classes) (embedConfiguration configuration) final ∧
      final.finished) ↔
    (∃ final, Unique.Unpacking.Steps classes configuration final ∧ final.finished) := by
  constructor
  · rintro ⟨final, trace, finished⟩
    obtain ⟨original, originalTrace, rfl⟩ := steps_backward trace
    exact ⟨original, originalTrace, (finished_correspondence original).mp finished⟩
  · rintro ⟨final, trace, finished⟩
    exact ⟨embedConfiguration final, steps_forward trace,
      (finished_correspondence final).mpr finished⟩

end Dada.Correspondence.Unpacking
