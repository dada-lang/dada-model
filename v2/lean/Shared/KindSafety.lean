import Shared.Liveness

namespace Dada.Shared

-- Declaration kinds constrain references without putting ownership modes on objects.
def objectNames (state : State) : List (ObjectId × ClassName) :=
  state.objects.map fun entry => (entry.1, entry.2.className)

def HasKind (classes : Classes) (state : State) (object : ObjectId) (kind : Kind) : Prop :=
  ∃ name declaration, (object, name) ∈ objectNames state ∧
    (name, declaration) ∈ classes ∧ declaration.kind = kind

def ReferenceAllowed (classes : Classes) (state : State) (reference : Reference) : Prop :=
  ∃ kind, HasKind classes state reference.object kind ∧
    (reference.mode = .shared → kind.isStruct = true) ∧
    (kind = .sharedStruct → reference.mode = .shared)

structure KindCorrect (classes : Classes) (state : State) (pending : List Reference) : Prop where
  references : ∀ reference ∈ pending ++ Owners state, ReferenceAllowed classes state reference
  fields : ∀ object data declaration, (object, data) ∈ state.objects →
    (data.className, declaration) ∈ classes → declaration.kind.isStruct = true →
    ∀ name reference, (name, some reference) ∈ data.fields →
      StructReference classes state reference

theorem structReference_iff : StructReference classes state reference ↔
    ∃ kind, HasKind classes state reference.object kind ∧ kind.isStruct = true := by
  simp only [StructReference, HasKind, objectNames, List.mem_map]
  constructor
  · rintro ⟨data, declaration, stored, declared, kind⟩
    exact ⟨declaration.kind, ⟨data.className, declaration,
      ⟨(reference.object, data), stored, rfl⟩, declared, rfl⟩, kind⟩
  · rintro ⟨kind, ⟨name, declaration, ⟨⟨object, data⟩, stored, equal⟩, declared, sameKind⟩, isStruct⟩
    cases equal
    exact ⟨data, declaration, stored, declared, sameKind ▸ isStruct⟩

theorem HasKind.frame (same : objectNames before = objectNames after)
    (has : HasKind classes before object kind) : HasKind classes after object kind := by
  simpa only [HasKind, same] using has

theorem ReferenceAllowed.frame (same : objectNames before = objectNames after)
    (allowed : ReferenceAllowed classes before reference) : ReferenceAllowed classes after reference := by
  obtain ⟨kind, has, shareable, immediate⟩ := allowed
  exact ⟨kind, has.frame same, shareable, immediate⟩

theorem StructReference.frame (same : objectNames before = objectNames after)
    (structRef : StructReference classes before reference) : StructReference classes after reference := by
  obtain ⟨kind, has, isStruct⟩ := structReference_iff.mp structRef
  exact structReference_iff.mpr ⟨kind, has.frame same, isStruct⟩

theorem StructReference.shared_allowed (structRef : StructReference classes state reference) :
    ReferenceAllowed classes state (.shared reference.object) := by
  obtain ⟨kind, has, isStruct⟩ := structReference_iff.mp structRef
  exact ⟨kind, has, fun _ => isStruct, fun _ => rfl⟩

theorem owner_variable (stored : (name, some reference) ∈ state.variables) :
    reference ∈ Owners state := by
  exact List.mem_append_left _ (List.mem_filterMap.mpr ⟨_, stored, rfl⟩)

theorem owner_field (stored : (object, data) ∈ state.objects)
    (field : (name, some reference) ∈ data.fields) : reference ∈ Owners state := by
  exact List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨_, stored, List.mem_filterMap.mpr ⟨_, field, rfl⟩⟩)

theorem Take.names_preserved (taken : Take before place object after) :
    objectNames before = objectNames after := by
  cases taken <;> simp [objectNames]

theorem Promote.names_preserved (promoted : Promote before place object after) :
    objectNames before = objectNames after := by
  cases promoted <;> simp [objectNames]

theorem Take.remaining_owners (taken : Take before place object after) :
    ∀ reference ∈ Owners after, reference ∈ Owners before := by
  cases taken <;> simp only [Owners, List.filterMap_append, List.filterMap_cons,
    List.flatMap_append, List.flatMap_cons, List.mem_append, List.mem_cons, List.mem_filterMap] <;> grind

theorem Promote.remaining_owners (promoted : Promote before place object after) :
    ∀ reference ∈ Owners after, reference ∈ Owners before ∨ reference = .shared object := by
  cases promoted <;> simp only [Owners, List.filterMap_append, List.filterMap_cons,
    List.flatMap_append, List.flatMap_cons, List.mem_append, List.mem_cons, List.mem_filterMap] <;> grind

private theorem lookup_unique {K V : Type} [BEq K] [LawfulBEq K]
    {entries : List (K × V)} {key : K} {first second : V} (keys : (entries.map Prod.fst).Nodup)
    (left : (key, first) ∈ entries) (right : (key, second) ∈ entries) : first = second := by
  induction entries with
  | nil => simp at left
  | cons entry rest ih =>
    rcases List.nodup_cons.mp keys with ⟨fresh, keys⟩
    rcases List.mem_cons.mp left with equal | leftRest
    · cases equal
      rcases List.mem_cons.mp right with equal | right
      · exact (Prod.mk.inj equal).2.symm
      · exact False.elim (fresh (List.mem_map.mpr ⟨_, right, rfl⟩))
    · rcases List.mem_cons.mp right with equal | right
      · cases equal
        exact False.elim (fresh (List.mem_map.mpr ⟨_, leftRest, rfl⟩))
      · exact ih keys leftRest right

theorem HasKind.at_object (has : HasKind classes state object kind)
    (keys : (state.objects.map Prod.fst).Nodup) (stored : (object, data) ∈ state.objects) :
    ∃ declaration, (data.className, declaration) ∈ classes ∧ declaration.kind = kind := by
  obtain ⟨name, declaration, named, declared, kindEq⟩ := has
  obtain ⟨⟨id, old⟩, member, equal⟩ := List.mem_map.mp named
  dsimp only at equal
  have ids := (Prod.mk.inj equal).1
  have names := (Prod.mk.inj equal).2
  subst id
  have same := lookup_unique keys member stored
  subst old
  exact ⟨declaration, names ▸ declared, kindEq⟩

theorem Resolve.allowed (resolved : Resolve state place storage object mode)
    (correct : KindCorrect classes state pending)
    (keys : (state.objects.map Prod.fst).Nodup) :
    ReferenceAllowed classes state ⟨mode, object⟩ := by
  induction resolved with
  | «variable» stored =>
    exact correct.references _ (List.mem_append_right _ (owner_variable stored))
  | @field base source parent permission data name reference route stored field ih =>
    have child := correct.references _ (List.mem_append_right _ (owner_field stored field))
    cases permission with
    | unique => cases reference with
      | reference mode object => cases mode <;> exact child
    | shared =>
      obtain ⟨kind, has, shareable, _⟩ := ih
      obtain ⟨declaration, declared, same⟩ := has.at_object keys stored
      have structChild := correct.fields parent data declaration stored declared
        (same ▸ shareable rfl) name reference field
      exact structChild.shared_allowed

theorem KindCorrect.add_pending (correct : KindCorrect classes state pending)
    (allowed : ReferenceAllowed classes state reference) :
    KindCorrect classes state (reference :: pending) := by
  refine ⟨?_, correct.fields⟩
  intro ref member
  rcases List.mem_cons.mp member with equal | member
  · exact equal ▸ allowed
  · exact correct.references ref member

theorem KindCorrect.take (correct : KindCorrect classes before pending)
    (taken : Take before place object after) : KindCorrect classes after pending := by
  constructor
  · intro ref member
    apply ReferenceAllowed.frame taken.names_preserved
    rcases List.mem_append.mp member with member | member
    · exact correct.references ref (List.mem_append_left _ member)
    · exact correct.references ref (List.mem_append_right _ (taken.remaining_owners ref member))
  · intro id data declaration stored declared isStruct name ref field
    obtain ⟨old, oldStored, same, _, fields⟩ := taken.object_data id data stored
    exact (correct.fields id old declaration oldStored (same ▸ declared) isStruct
      name ref (fields name ref field)).frame taken.names_preserved

theorem KindCorrect.promote (correct : KindCorrect classes before pending)
    (promoted : Promote before place object after)
    (allowed : ReferenceAllowed classes before (.shared object)) :
    KindCorrect classes after pending := by
  constructor
  · intro ref member
    apply ReferenceAllowed.frame promoted.names_preserved
    rcases List.mem_append.mp member with member | member
    · exact correct.references ref (List.mem_append_left _ member)
    · rcases promoted.remaining_owners ref member with old | same
      · exact correct.references ref (List.mem_append_right _ old)
      · exact same ▸ allowed
  · intro id data declaration stored declared isStruct name ref field
    obtain ⟨old, oldStored, same, _, fields⟩ := promoted.object_data id data stored
    obtain ⟨oldRef, oldField, sameObject⟩ := fields name ref field
    have target := correct.fields id old declaration oldStored (same ▸ declared)
      isStruct name oldRef oldField
    have transferred : StructReference classes before ref := by
      simpa only [StructReference, sameObject] using target
    exact transferred.frame promoted.names_preserved

theorem Give.preserves_kinds (given : Give before place reference after)
    (correct : KindCorrect classes before pending)
    (keys : (before.objects.map Prod.fst).Nodup) :
    KindCorrect classes after (reference :: pending) := by
  cases given with
  | move resolved taken =>
    exact (correct.take taken).add_pending ((resolved.allowed correct keys).frame taken.names_preserved)
  | copy resolved _ => exact correct.add_pending (resolved.allowed correct keys)
  | promote resolved promoted =>
    have allowed := resolved.allowed correct keys
    exact (correct.promote promoted allowed).add_pending (allowed.frame promoted.names_preserved)

theorem HasKind.allocate (has : HasKind classes state object kind) :
    HasKind classes (state.allocate name fields arguments) object kind := by
  obtain ⟨target, declaration, member, declared, same⟩ := has
  exact ⟨target, declaration, List.mem_cons_of_mem _ member, declared, same⟩

theorem ReferenceAllowed.allocate (allowed : ReferenceAllowed classes state reference) :
    ReferenceAllowed classes (state.allocate name fields arguments) reference := by
  obtain ⟨kind, has, shareable, immediate⟩ := allowed
  exact ⟨kind, has.allocate, shareable, immediate⟩

theorem StructReference.allocate (structRef : StructReference classes state reference) :
    StructReference classes (state.allocate name fields arguments) reference := by
  obtain ⟨kind, has, isStruct⟩ := structReference_iff.mp structRef
  exact structReference_iff.mpr ⟨kind, has.allocate, isStruct⟩

theorem KindCorrect.allocate {references : List Reference} (correct : KindCorrect classes state (references ++ pending))
    (classesWf : ClassesWellFormed classes) (declared : (name, declaration) ∈ classes)
    (lengths : references.length = declaration.fields.length)
    (structArgs : StructArguments classes state declaration.kind references) :
    KindCorrect classes (state.allocate name declaration.fields references)
      (⟨declaration.kind.mode, ⟨state.nextId⟩⟩ :: pending) := by
  constructor
  · intro ref member
    rcases List.mem_cons.mp member with same | member
    · subst ref
      refine ⟨declaration.kind, ⟨name, declaration, ?_, declared, rfl⟩, ?_, ?_⟩
      · exact List.mem_cons_self
      · cases declaration.kind <;> simp [Kind.mode, Kind.isStruct]
      · cases declaration.kind <;> simp [Kind.mode]
    · apply ReferenceAllowed.allocate
      apply correct.references
      rcases List.mem_append.mp member with pendingMember | owner
      · exact List.mem_append_left _ (List.mem_append_right _ pendingMember)
      · have old := (allocation_owners (className := name) state lengths).mem_iff.mp owner
        rcases List.mem_append.mp old with refMember | oldMember
        · exact List.mem_append_left _ (List.mem_append_left _ refMember)
        · exact List.mem_append_right _ oldMember
  · intro object data actual stored actualDeclared isStruct field ref fieldMember
    rcases List.mem_cons.mp stored with same | old
    · cases same
      have sameDeclaration := lookup_unique classesWf.1 declared actualDeclared
      subst actual
      have refMember : ref ∈ references := by
        obtain ⟨_, member, equal⟩ := List.mem_map.mp (List.of_mem_zip fieldMember).2
        exact Option.some.inj equal ▸ member
      exact (structArgs isStruct ref refMember).allocate
    · exact (correct.fields object data actual old actualDeclared isStruct field ref fieldMember).allocate

theorem KindCorrect.perm (correct : KindCorrect classes state pending)
    (permutation : pending.Perm other) : KindCorrect classes state other := by
  refine ⟨?_, correct.fields⟩
  intro ref member
  exact correct.references ref ((permutation.append_right _).mem_iff.mpr member)

theorem KindCorrect.share_pending (correct : KindCorrect classes state (reference :: pending))
    (structRef : StructReference classes state reference) :
    KindCorrect classes state (.shared reference.object :: pending) := by
  refine ⟨?_, correct.fields⟩
  intro ref member
  rcases List.mem_cons.mp member with same | member
  · exact same ▸ structRef.shared_allowed
  · exact correct.references ref (List.mem_cons_of_mem _ member)

theorem Eval.preserves_kinds (evaluation : Eval classes before value after reference)
    (classesWf : ClassesWellFormed classes) (wf : WellFormedWith classes before pending)
    (correct : KindCorrect classes before pending) : KindCorrect classes after (reference :: pending) := by
  apply Eval.rec
    (motive_1 := fun before _ after reference _ => ∀ pending,
      WellFormedWith classes before pending → KindCorrect classes before pending →
      KindCorrect classes after (reference :: pending))
    (motive_2 := fun before _ after references _ => ∀ pending,
      WellFormedWith classes before pending → KindCorrect classes before pending →
      KindCorrect classes after (references ++ pending))
    ?_ ?_ ?_ ?_ ?_ evaluation pending wf correct
  · intro state evaluated path reference given pending wf correct
    exact given.preserves_kinds correct wf.objectKeys
  · intro state evaluated path reference given structRef pending wf correct
    exact (given.preserves_kinds correct wf.objectKeys).share_pending structRef
  · intro state evaluated name declaration arguments references declared args lengths fresh structArgs ih pending wf correct
    exact (ih pending wf correct).allocate classesWf declared lengths structArgs
  · intro state pending wf correct
    exact correct
  · intro before middle after argument arguments reference references first rest ihFirst ihRest pending wf correct
    have middleWf := first.preserves_wellFormedWith classesWf wf
    have result := ihRest _ middleWf (ihFirst _ wf correct)
    exact result.perm (by simpa only [List.cons_append] using
      (List.perm_middle (a := reference) (l₁ := references) (l₂ := pending)))

theorem KindCorrect.bind (correct : KindCorrect classes state [reference]) :
    KindCorrect classes (state.bind name reference) [] := by
  constructor
  · intro ref member
    exact correct.references ref (by simpa [Owners, State.bind] using member)
  · intro object data declaration stored declared isStruct field ref member
    exact correct.fields object data declaration stored declared isStruct field ref member

theorem KindCorrect.empty (classes : Classes) : KindCorrect classes State.empty [] := by
  constructor
  · simp [Owners, State.empty]
  · simp [State.empty]

theorem Step.preserves_kinds (step : Step classes before after)
    (classesWf : ClassesWellFormed classes) (wf : WellFormed classes before.state)
    (correct : KindCorrect classes before.state []) : KindCorrect classes after.state [] := by
  cases step with
  | letValue _ evaluation => exact (evaluation.preserves_kinds classesWf wf.with_pending correct).bind

theorem Steps.kinds_from_initial (classesWf : ClassesWellFormed program.classes)
    (steps : Steps program.classes (Configuration.initial program) after) :
    KindCorrect program.classes after.state [] := by
  have preserve : ∀ before after, Steps program.classes before after →
      WellFormed program.classes before.state → KindCorrect program.classes before.state [] →
      KindCorrect program.classes after.state [] := by
    intro before after steps
    induction steps with
    | refl => intro _ correct; exact correct
    | step first rest ih =>
      intro wf correct
      exact ih (first.preserves_wellFormed classesWf wf) (first.preserves_kinds classesWf wf correct)
  exact preserve _ _ steps (WellFormed.empty _) (KindCorrect.empty _)

def WellFormedState (classes : Classes) (state : State) : Prop :=
  WellFormed classes state ∧ KindCorrect classes state []

theorem Steps.wellFormed_from_initial (classesWf : ClassesWellFormed program.classes)
    (steps : Steps program.classes (Configuration.initial program) after) :
    WellFormedState program.classes after.state :=
  ⟨steps.from_initial classesWf, steps.kinds_from_initial classesWf⟩

theorem WellFormedState.live_iff_allocated (wf : WellFormedState classes state) :
    Live state object ↔ Allocated state object := wf.1.live_iff_allocated

theorem WellFormedState.path_mode_exclusive (wf : WellFormedState classes state)
    (unique : Resolve state uniquePath uniquePlace object .unique)
    (shared : Resolve state sharedPath sharedPlace object .shared) : False :=
  wf.1.path_mode_exclusive unique shared

end Dada.Shared
