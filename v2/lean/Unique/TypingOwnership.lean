import Unique.TypingHeap

namespace Dada.Unique.Typing

def ownerOccurrences (state : State) : List (StoragePlace × ObjectId) :=
  state.variables.filterMap (fun (name, slot) => slot.map fun object => (.variable name, object)) ++
  state.objects.flatMap (fun (parent, data) => data.fields.filterMap
    (fun (name, slot) => slot.map fun object => (.field parent name, object)))

theorem ownerOccurrences_targets (state : State) :
    (ownerOccurrences state).map Prod.snd = References state := by
  simp [ownerOccurrences, References, List.map_append, List.map_flatMap,
    List.map_filterMap, Function.comp_def, Option.map_map]

theorem stored_ownerOccurrence (stored : Stored state place (some object)) :
    (place, object) ∈ ownerOccurrences state := by
  cases place with
  | «variable» name =>
    exact List.mem_append_left _ (List.mem_filterMap.mpr
      ⟨(name, some object), stored, rfl⟩)
  | field parent name =>
    obtain ⟨data, atObject, atField⟩ := stored
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨(parent, data), atObject,
      List.mem_filterMap.mpr ⟨(name, some object), atField, rfl⟩⟩)

private theorem unique_mapped {α β : Type} {f : α → β} {entries : List α}
    (distinct : (entries.map f).Nodup) {left right : α}
    (leftMem : left ∈ entries) (rightMem : right ∈ entries) (same : f left = f right) :
    left = right := by
  induction entries with
  | nil => simp at leftMem
  | cons head tail ih =>
    obtain ⟨fresh, distinct⟩ := List.nodup_cons.mp distinct
    rcases List.mem_cons.mp leftMem with rfl | leftTail
    · rcases List.mem_cons.mp rightMem with rfl | rightMem
      · rfl
      · exact False.elim (fresh (same ▸ List.mem_map.mpr ⟨right, rightMem, rfl⟩))
    · rcases List.mem_cons.mp rightMem with rfl | rightMem
      · exact False.elim (fresh (same ▸ List.mem_map.mpr ⟨left, leftTail, rfl⟩))
      · exact ih distinct leftTail rightMem

theorem unique_owner (wf : WellFormedWith classes state pending)
    (left : Stored state first (some object)) (right : Stored state second (some object)) :
    first = second := by
  have distinct : ((ownerOccurrences state).map Prod.snd).Nodup := by
    rw [ownerOccurrences_targets]
    exact (List.nodup_append.mp wf.referencesUnique).2.1
  exact congrArg Prod.fst (unique_mapped distinct
    (stored_ownerOccurrence left) (stored_ownerOccurrence right) rfl)

theorem pending_not_stored (wf : WellFormedWith classes state pending)
    (root : object ∈ pending) (stored : Stored state place (some object)) : False := by
  have member : object ∈ References state := by
    rw [← ownerOccurrences_targets]
    exact List.mem_map.mpr ⟨(place, object), stored_ownerOccurrence stored, rfl⟩
  exact (List.nodup_append.mp wf.referencesUnique).2.2 object root object member rfl

inductive RootSite where
  | variable (name : VariableId)
  | pending (object : ObjectId)
  deriving DecidableEq, Repr

inductive RootOwns (state : State) (pending : List ObjectId) : RootSite → ObjectId → Prop where
  | variable : (name, some object) ∈ state.variables → RootOwns state pending (.variable name) object
  | pending : object ∈ pending → RootOwns state pending (.pending object) object

inductive Route (state : State) (pending : List ObjectId) : RootSite → Path → ObjectId → Prop where
  | root : RootOwns state pending site object → Route state pending site [] object
  | field : Route state pending site path parent → (parent, data) ∈ state.objects →
      (name, some object) ∈ data.fields → Route state pending site (path ++ [name]) object

theorem RootOwns.unique {pending : List ObjectId} (wf : WellFormedWith classes state pending)
    (left : RootOwns state pending first object) (right : RootOwns state pending second object) :
    first = second := by
  cases left with
  | «variable» left =>
    cases right with
    | «variable» right =>
      have same := unique_owner wf (show Stored state (.variable _) _ from left)
        (show Stored state (.variable _) _ from right)
      cases same
      rfl
    | pending right => exact False.elim (pending_not_stored wf right (show Stored state (.variable _) _ from left))
  | pending left =>
    cases right with
    | «variable» right => exact False.elim (pending_not_stored wf left (show Stored state (.variable _) _ from right))
    | pending _ => rfl

theorem RootOwns.not_field {pending : List ObjectId} (wf : WellFormedWith classes state pending)
    (root : RootOwns state pending site object)
    (stored : Stored state (.field parent name) (some object)) : False := by
  cases root with
  | «variable» atRoot =>
    have same := unique_owner wf (show Stored state (.variable _) _ from atRoot) stored
    cases same
  | pending atRoot => exact pending_not_stored wf atRoot stored

-- Distinct owning roots and distinct field routes cannot meet. This statement
-- counts pending expression values as roots as well as variables.
theorem Route.unique (wf : WellFormedWith classes state pending)
    (left : Route state pending first firstPath object)
    (right : Route state pending second secondPath object) :
    first = second ∧ firstPath = secondPath := by
  induction left generalizing second secondPath with
  | root atRoot =>
    cases right with
    | root otherRoot => exact ⟨atRoot.unique wf otherRoot, rfl⟩
    | field _ atObject atField => exact False.elim (atRoot.not_field wf ⟨_, atObject, atField⟩)
  | field parentRoute atObject atField ih =>
    cases right with
    | root atRoot => exact False.elim (atRoot.not_field wf ⟨_, atObject, atField⟩)
    | field otherPrefix otherObject otherField =>
      have same := unique_owner wf
        (show Stored state (.field _ _) _ from ⟨_, atObject, atField⟩)
        (show Stored state (.field _ _) _ from ⟨_, otherObject, otherField⟩)
      cases same
      obtain ⟨sites, paths⟩ := ih otherPrefix
      exact ⟨sites, congrArg (fun path => path ++ [_]) paths⟩

theorem Route.follow (route : Route state pending site initial object)
    (read : readPath state object path = some (some target)) :
    Route state pending site (initial ++ path) target := by
  induction path generalizing initial object with
  | nil =>
    cases found : state.objects.lookup object <;> simp [readPath, found] at read
    subst target
    simpa using route
  | cons field rest ih =>
    obtain ⟨data, slot, stored, atField, final | ⟨child, rfl, more⟩⟩ := readPath_cons read
    · rcases final with ⟨rfl, rfl⟩
      exact .field route stored atField
    · simpa [List.append_assoc] using ih (.field route stored atField) more

theorem route_of_resolve (resolved : Resolve state place source object) :
    Route state pending (.variable (splitPlace place).1) (splitPlace place).2 object := by
  induction resolved with
  | «variable» stored => exact .root (.variable stored)
  | field _ stored atField ih => exact .field ih stored atField

theorem resolve_deterministic (wf : WellFormedWith classes state pending)
    (first : Resolve state place firstSource firstObject)
    (second : Resolve state place secondSource secondObject) :
    firstSource = secondSource ∧ firstObject = secondObject := by
  induction first generalizing secondSource secondObject with
  | «variable» first =>
    cases second with
    | «variable» second => exact ⟨rfl, Option.some.inj (member_value_unique wf.variableKeys first second)⟩
  | field _ firstObject firstField ih =>
    cases second with
    | field other otherObject otherField =>
      obtain ⟨rfl, rfl⟩ := ih other
      have sameData := member_value_unique wf.objectKeys firstObject otherObject
      subst_vars
      have same := stored_value_unique wf
        (show Stored state (.field _ _) _ from ⟨_, firstObject, firstField⟩)
        (show Stored state (.field _ _) _ from ⟨_, otherObject, otherField⟩)
      exact ⟨rfl, Option.some.inj same⟩

theorem resolve_readPath (wf : WellFormedWith classes state pending)
    (resolved : Resolve state place source object) :
    ∃ root, ((splitPlace place).1, some root) ∈ state.variables ∧
      readPath state root (splitPlace place).2 = some (some object) := by
  induction resolved with
  | «variable» stored =>
    refine ⟨_, stored, readPath_nil_of_allocated wf ?_⟩
    apply (wf.referencesComplete _).mp
    exact List.mem_append_right _ (List.mem_append_left _
      (List.mem_filterMap.mpr ⟨(_, some _), stored, rfl⟩))
  | field previous stored atField ih =>
    obtain ⟨root, atRoot, read⟩ := ih
    exact ⟨root, atRoot, (readPath_append wf read [_]).trans
      (readPath_singleton_of_stored wf ⟨_, stored, atField⟩)⟩

theorem Route.allocated (wf : WellFormedWith classes state pending)
    (route : Route state pending site path object) : Allocated state object := by
  cases route with
  | root owner =>
    apply (wf.referencesComplete object).mp
    cases owner with
    | «variable» stored =>
      exact List.mem_append_right _ (List.mem_append_left _
        (List.mem_filterMap.mpr ⟨(_, some object), stored, rfl⟩))
    | pending member => exact List.mem_append_left _ member
  | field _ stored atField => exact WellFormedWith.field_allocated wf stored atField

-- A successful observation is unchanged unless the removed owner's route is a
-- prefix of the observed route. The observation may end at an empty slot.
theorem take_readPath_frame (wf : WellFormedWith classes before pending)
    (taken : Take before source removed after)
    (cut : Route before pending cutSite cutPath removed)
    (route : Route before pending site initial object)
    (read : readPath before object path = some slot)
    (separate : ¬ (site = cutSite ∧ cutPath.IsPrefix (initial ++ path))) :
    readPath after object path = some slot := by
  have afterWf := taken.preserves_pending wf
  induction path generalizing initial object with
  | nil =>
    cases found : before.objects.lookup object <;> simp [readPath, found] at read
    subst slot
    apply readPath_nil_of_allocated afterWf
    simpa [Allocated, taken.object_keys] using route.allocated wf
  | cons field rest ih =>
    obtain ⟨data, fieldSlot, stored, atField, final | ⟨child, same, more⟩⟩ := readPath_cons read
    all_goals
      have different : StoragePlace.field object field ≠ source := by
        intro equalSource
        have sameSlot : fieldSlot = some removed := stored_value_unique wf
          (show Stored before (.field object field) fieldSlot from ⟨data, stored, atField⟩)
          (equalSource ▸ taken.stored)
        have crossing : Route before pending site (initial ++ [field]) removed :=
          .field route stored (sameSlot ▸ atField)
        obtain ⟨sameSite, samePath⟩ := crossing.unique wf cut
        apply separate
        refine ⟨sameSite, ?_⟩
        rw [← samePath]
        exact ⟨rest, by simp [List.append_assoc]⟩
      have firstRead := readPath_singleton_of_stored afterWf
        (taken.stored_unchanged different (show Stored before (.field object field) fieldSlot from
          ⟨data, stored, atField⟩))
    · rcases final with ⟨rfl, rfl⟩
      exact firstRead
    · subst fieldSlot
      have remaining := ih (.field route stored atField) more (by
        simpa [List.append_assoc] using separate)
      exact (readPath_append afterWf firstRead rest).trans remaining

theorem route_of_liveWith (live : LiveWith state pending object) :
    ∃ site path, Route state pending site path object := by
  induction live with
  | pending member => exact ⟨_, [], .root (.pending member)⟩
  | «variable» member => exact ⟨_, [], .root (.variable member)⟩
  | field _ member field ih =>
    obtain ⟨site, path, route⟩ := ih
    exact ⟨site, _, .field route member field⟩

theorem readPath_no_cycle (wf : WellFormedWith classes state pending)
    (nonempty : path ≠ []) (read : readPath state object path = some (some object)) : False := by
  obtain ⟨data, member⟩ := readPath_root_allocated read
  obtain ⟨site, rootPath, route⟩ := route_of_liveWith (wf.rooted object (List.mem_map.mpr ⟨_, member, rfl⟩))
  have same := ((route.follow read).unique wf route).2
  have lengths := congrArg List.length same
  have : path.length = 0 := by simp only [List.length_append] at lengths; omega
  exact nonempty (List.length_eq_zero_iff.mp this)

-- An owner's interior cannot lead back to its incoming slot: otherwise two
-- distinct root routes would own the same object.
theorem take_readPath_descendant (wf : WellFormedWith classes before pending)
    (taken : Take before source removed after)
    (cut : Route before pending site cutPath removed)
    (route : Route before pending site initial object)
    (below : cutPath.length ≤ initial.length)
    (read : readPath before object path = some slot) : readPath after object path = some slot := by
  have afterWf := taken.preserves_pending wf
  induction path generalizing initial object with
  | nil =>
    cases found : before.objects.lookup object <;> simp [readPath, found] at read
    subst slot
    apply readPath_nil_of_allocated afterWf
    rw [Allocated, taken.object_keys]
    exact List.mem_map.mpr ⟨_, lookup_member found, rfl⟩
  | cons field rest ih =>
    obtain ⟨data, fieldSlot, stored, atField, final | ⟨child, same, more⟩⟩ := readPath_cons read
    all_goals
      have different : StoragePlace.field object field ≠ source := by
        intro sameSource
        have sourceField : Stored before (.field object field) (some removed) := sameSource ▸ taken.stored
        have sameSlot := stored_value_unique wf
          (show Stored before (.field object field) fieldSlot from ⟨_, stored, atField⟩) sourceField
        have crossing := Route.field route stored (sameSlot ▸ atField)
        have samePath := (crossing.unique wf cut).2
        have lengths := congrArg List.length samePath
        simp only [List.length_append, List.length_singleton] at lengths
        omega
      have firstRead := readPath_singleton_of_stored afterWf
        (taken.stored_unchanged different (show Stored before (.field object field) fieldSlot from
          ⟨data, stored, atField⟩))
    · rcases final with ⟨rfl, rfl⟩
      exact firstRead
    · subst fieldSlot
      exact (readPath_append afterWf firstRead rest).trans
        (ih (.field route stored atField) (by simp only [List.length_append, List.length_singleton]; omega) more)

theorem take_readPath_taken (wf : WellFormedWith classes before pending)
    (taken : Take before source object after)
    (read : readPath before object path = some slot) : readPath after object path = some slot := by
  obtain ⟨data, member⟩ := readPath_root_allocated read
  obtain ⟨site, rootPath, route⟩ := route_of_liveWith (wf.rooted object (List.mem_map.mpr ⟨_, member, rfl⟩))
  exact take_readPath_descendant wf taken route route (Nat.le_refl _) read

theorem take_readPath_cleared (wf : WellFormedWith classes before pending)
    (taken : Take before source removed after) (nonempty : path ≠ [])
    (read : readPath before object path = some (some removed)) :
    readPath after object path = some none := by
  have afterWf := taken.preserves_pending wf
  induction path generalizing object with
  | nil => exact False.elim (nonempty rfl)
  | cons field rest ih =>
    obtain ⟨data, fieldSlot, stored, atField, final | ⟨child, rfl, more⟩⟩ := readPath_cons read
    · rcases final with ⟨rfl, rfl⟩
      have same := unique_owner wf
        (show Stored before (.field object field) (some removed) from ⟨data, stored, atField⟩)
        taken.stored
      exact readPath_singleton_of_stored afterWf (same ▸ taken.cleared)
    · by_cases empty : rest = []
      · subst rest
        cases found : before.objects.lookup child <;> simp [readPath, found] at more
        subst child
        have same := unique_owner wf
          (show Stored before (.field object field) (some removed) from ⟨data, stored, atField⟩)
          taken.stored
        exact readPath_singleton_of_stored afterWf (same ▸ taken.cleared)
      · have different : StoragePlace.field object field ≠ source := by
          intro same
          have equalSlot := stored_value_unique wf
            (show Stored before (.field object field) (some child) from ⟨data, stored, atField⟩)
            (same ▸ taken.stored)
          have equalObject := Option.some.inj equalSlot
          subst child
          exact readPath_no_cycle wf empty more
        have firstRead := readPath_singleton_of_stored afterWf
          (taken.stored_unchanged different
            (show Stored before (.field object field) (some child) from ⟨data, stored, atField⟩))
        exact (readPath_append afterWf firstRead rest).trans (ih empty more)

theorem Satisfies.take_taken (wf : WellFormedWith classes.erase before pending)
    (taken : Take before source object after) (satisfied : Satisfies classes before object ty) :
    Satisfies classes after object ty := by
  constructor
  · obtain ⟨data, stored, same⟩ := satisfied.root
    obtain ⟨newData, newStored, newSame⟩ := taken.old_object_data object data stored
    exact ⟨newData, newStored, newSame.trans same⟩
  · intro path positive
    obtain ⟨target, data, read, stored, correctClass⟩ := satisfied.positive path positive
    obtain ⟨newData, newStored, sameClass⟩ := taken.old_object_data target data stored
    exact ⟨target, newData, take_readPath_taken wf taken read, newStored, sameClass ▸ correctClass⟩
  · intro path negative
    exact take_readPath_taken wf taken (satisfied.negative path negative)

theorem Satisfies.take_frame (wf : WellFormedWith classes.erase before pending)
    (taken : Take before source removed after)
    (cut : Route before pending cutSite cutPath removed)
    (route : Route before pending site initial object)
    (satisfied : Satisfies classes before object ty)
    (separate : ∀ path, Pos classes ty path ∨ Neg ty path →
      ¬ (site = cutSite ∧ cutPath.IsPrefix (initial ++ path))) :
    Satisfies classes after object ty := by
  constructor
  · obtain ⟨data, stored, same⟩ := satisfied.root
    obtain ⟨newData, newStored, newSame⟩ := taken.old_object_data object data stored
    exact ⟨newData, newStored, newSame.trans same⟩
  · intro path positive
    obtain ⟨target, data, read, stored, correctClass⟩ := satisfied.positive path positive
    obtain ⟨newData, newStored, sameClass⟩ := taken.old_object_data target data stored
    exact ⟨target, newData,
      take_readPath_frame wf taken cut route read (separate path (Or.inl positive)),
      newStored, sameClass ▸ correctClass⟩
  · intro path negative
    exact take_readPath_frame wf taken cut route (satisfied.negative path negative)
      (separate path (Or.inr negative))

end Dada.Unique.Typing
