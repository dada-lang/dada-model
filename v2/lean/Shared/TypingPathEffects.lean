import Shared.TypingPaths
import Shared.Typing

namespace Dada.Shared

theorem Take.stored (taken : Take before place object after) :
    Stored before place (some (.owned object)) := by
  cases taken with
  | «variable» => simp [Stored]
  | field variables nextId leading trailing parent className beforeFields afterFields name object =>
    exact ⟨⟨className, beforeFields ++ (name, some (.owned object)) :: afterFields⟩,
      by simp, by simp⟩

theorem Take.cleared (taken : Take before place object after) : Stored after place none := by
  cases taken with
  | «variable» => simp [Stored]
  | field variables nextId leading trailing parent className beforeFields afterFields name object =>
    exact ⟨⟨className, beforeFields ++ (name, none) :: afterFields⟩, by simp, by simp⟩

theorem Take.stored_unchanged (taken : Take before source object after)
    (different : place ≠ source) (stored : Stored before place slot) :
    Stored after place slot := by
  cases taken with
  | «variable» objects nextId leading trailing name object =>
    cases place with
    | «variable» other =>
      simp only [Stored, List.mem_append, List.mem_cons] at stored ⊢
      rcases stored with member | same | member
      · exact Or.inl member
      · cases same
        exact False.elim (different rfl)
      · exact Or.inr (Or.inr member)
    | field parent fieldName => exact stored
  | field variables nextId leading trailing parent className beforeFields afterFields name object =>
    cases place with
    | «variable» other => exact stored
    | field other otherField =>
      obtain ⟨data, atObject, atField⟩ := stored
      simp only [List.mem_append, List.mem_cons] at atObject
      rcases atObject with member | same | member
      · exact ⟨data, List.mem_append_left _ member, atField⟩
      · cases same
        refine ⟨⟨className, beforeFields ++ (name, none) :: afterFields⟩, by simp, ?_⟩
        simp only [List.mem_append, List.mem_cons] at atField ⊢
        rcases atField with member | same | member
        · exact Or.inl member
        · cases same
          exact False.elim (different rfl)
        · exact Or.inr (Or.inr member)
      · exact ⟨data, List.mem_append_right _ (List.mem_cons_of_mem _ member), atField⟩

theorem Take.old_object_data (taken : Take before place object after)
    (id : ObjectId) (data : Object) (stored : (id, data) ∈ before.objects) :
    ∃ newData, (id, newData) ∈ after.objects ∧ newData.className = data.className := by
  cases taken with
  | «variable» => exact ⟨data, stored, rfl⟩
  | field variables nextId leading trailing parent className beforeFields afterFields name object =>
    simp only [List.mem_append, List.mem_cons] at stored
    rcases stored with member | same | member
    · exact ⟨data, List.mem_append_left _ member, rfl⟩
    · cases same
      exact ⟨⟨className, beforeFields ++ (name, none) :: afterFields⟩, by simp, rfl⟩
    · exact ⟨data, List.mem_append_right _ (List.mem_cons_of_mem _ member), rfl⟩

theorem Promote.stored (promoted : Promote before place object after) :
    Stored before place (some (.owned object)) := by
  cases promoted with
  | «variable» => simp [Stored]
  | field variables nextId leading trailing parent className beforeFields afterFields name object =>
    exact ⟨⟨className, beforeFields ++ (name, some (.owned object)) :: afterFields⟩,
      by simp, by simp⟩

theorem Promote.promoted (promoted : Promote before place object after) :
    Stored after place (some (.shared object)) := by
  cases promoted with
  | «variable» => simp [Stored]
  | field variables nextId leading trailing parent className beforeFields afterFields name object =>
    exact ⟨⟨className, beforeFields ++ (name, some (.shared object)) :: afterFields⟩,
      by simp, by simp⟩

theorem Promote.stored_unchanged (promoted : Promote before source object after)
    (different : place ≠ source) (stored : Stored before place slot) :
    Stored after place slot := by
  cases promoted with
  | «variable» objects nextId leading trailing name object =>
    cases place with
    | «variable» other =>
      simp only [Stored, List.mem_append, List.mem_cons] at stored ⊢
      rcases stored with member | same | member
      · exact Or.inl member
      · cases same
        exact False.elim (different rfl)
      · exact Or.inr (Or.inr member)
    | field parent fieldName => exact stored
  | field variables nextId leading trailing parent className beforeFields afterFields name object =>
    cases place with
    | «variable» other => exact stored
    | field other otherField =>
      obtain ⟨data, atObject, atField⟩ := stored
      simp only [List.mem_append, List.mem_cons] at atObject
      rcases atObject with member | same | member
      · exact ⟨data, List.mem_append_left _ member, atField⟩
      · cases same
        refine ⟨⟨className, beforeFields ++ (name, some (.shared object)) :: afterFields⟩,
          by simp, ?_⟩
        simp only [List.mem_append, List.mem_cons] at atField ⊢
        rcases atField with member | same | member
        · exact Or.inl member
        · cases same
          exact False.elim (different rfl)
        · exact Or.inr (Or.inr member)
      · exact ⟨data, List.mem_append_right _ (List.mem_cons_of_mem _ member), atField⟩

theorem Promote.old_object_data (promoted : Promote before place object after)
    (id : ObjectId) (data : Object) (stored : (id, data) ∈ before.objects) :
    ∃ newData, (id, newData) ∈ after.objects ∧ newData.className = data.className := by
  cases promoted with
  | «variable» => exact ⟨data, stored, rfl⟩
  | field variables nextId leading trailing parent className beforeFields afterFields name object =>
    simp only [List.mem_append, List.mem_cons] at stored
    rcases stored with member | same | member
    · exact ⟨data, List.mem_append_left _ member, rfl⟩
    · cases same
      exact ⟨⟨className, beforeFields ++ (name, some (.shared object)) :: afterFields⟩,
        by simp, rfl⟩
    · exact ⟨data, List.mem_append_right _ (List.mem_cons_of_mem _ member), rfl⟩

-- Promotion preserves whether a slot is occupied and the identity it targets.
theorem Promote.stored_back (promoted : Promote before source object after)
    (stored : Stored after place slot) :
    ∃ oldSlot, Stored before place oldSlot ∧
      oldSlot.map Reference.object = slot.map Reference.object := by
  cases promoted with
  | «variable» objects nextId leading trailing name object =>
    cases place with
    | «variable» other =>
      simp only [Stored, List.mem_append, List.mem_cons] at stored
      rcases stored with member | same | member
      · exact ⟨slot, by simp [Stored, member], rfl⟩
      · cases same
        exact ⟨some (.owned object), by simp [Stored], rfl⟩
      · exact ⟨slot, by simp [Stored, member], rfl⟩
    | field parent fieldName => exact ⟨slot, stored, rfl⟩
  | field variables nextId leading trailing parent className beforeFields afterFields name object =>
    cases place with
    | «variable» other => exact ⟨slot, stored, rfl⟩
    | field other otherField =>
      obtain ⟨data, atObject, atField⟩ := stored
      simp only [List.mem_append, List.mem_cons] at atObject
      rcases atObject with member | same | member
      · exact ⟨slot, ⟨data, List.mem_append_left _ member, atField⟩, rfl⟩
      · cases same
        simp only [List.mem_append, List.mem_cons] at atField
        rcases atField with member | same | member
        · exact ⟨slot, ⟨⟨className, beforeFields ++ (name, some (.owned object)) :: afterFields⟩,
            by simp, by simp [member]⟩, rfl⟩
        · cases same
          exact ⟨some (.owned object), ⟨⟨className,
            beforeFields ++ (name, some (.owned object)) :: afterFields⟩,
            by simp, by simp⟩, rfl⟩
        · exact ⟨slot, ⟨⟨className, beforeFields ++ (name, some (.owned object)) :: afterFields⟩,
            by simp, by simp [member]⟩, rfl⟩
      · exact ⟨slot, ⟨data, List.mem_append_right _ (List.mem_cons_of_mem _ member), atField⟩, rfl⟩

end Dada.Shared

namespace Dada.Shared.Typing

def ownerOccurrences (state : State) : List (StoragePlace × Reference) :=
  state.variables.filterMap (fun (name, slot) => slot.map fun reference => (.variable name, reference)) ++
  state.objects.flatMap (fun (parent, data) => data.fields.filterMap
    (fun (name, slot) => slot.map fun reference => (.field parent name, reference)))

theorem ownerOccurrences_references (state : State) :
    (ownerOccurrences state).map Prod.snd = Owners state := by
  simp [ownerOccurrences, Owners, List.map_append, List.map_flatMap,
    List.map_filterMap, Function.comp_def, Option.map_map]

theorem stored_ownerOccurrence (stored : Stored state place (some reference)) :
    (place, reference) ∈ ownerOccurrences state := by
  cases place with
  | «variable» name =>
    exact List.mem_append_left _ (List.mem_filterMap.mpr
      ⟨(name, some reference), stored, rfl⟩)
  | field parent name =>
    obtain ⟨data, atObject, atField⟩ := stored
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨(parent, data), atObject,
      List.mem_filterMap.mpr ⟨(name, some reference), atField, rfl⟩⟩)

theorem stored_owner (stored : Stored state place (some reference)) : reference ∈ Owners state := by
  rw [← ownerOccurrences_references]
  exact List.mem_map.mpr ⟨_, stored_ownerOccurrence stored, rfl⟩

private theorem occurrence_eq_or_compatible {owners : List (StoragePlace × Reference)}
    (pairwise : owners.Pairwise (fun a b => Compatible a.2 b.2))
    (first : a ∈ owners) (second : b ∈ owners) : a = b ∨ Compatible a.2 b.2 := by
  induction owners with
  | nil => simp at first
  | cons head tail ih =>
    rcases List.mem_cons.mp first with firstEq | firstTail
    · subst a
      rcases List.mem_cons.mp second with secondEq | secondTail
      · exact Or.inl secondEq.symm
      · exact Or.inr ((List.pairwise_cons.mp pairwise).1 _ secondTail)
    · rcases List.mem_cons.mp second with secondEq | secondTail
      · subst b
        apply Or.inr
        rcases (List.pairwise_cons.mp pairwise).1 _ firstTail with different | shared
        · exact Or.inl different.symm
        · exact Or.inr ⟨shared.2, shared.1⟩
      · exact ih pairwise.of_cons firstTail secondTail

private theorem reference_eq_or_compatible {owners : List Reference}
    (pairwise : owners.Pairwise Compatible)
    (first : a ∈ owners) (second : b ∈ owners) : a = b ∨ Compatible a b := by
  induction owners with
  | nil => simp at first
  | cons head tail ih =>
    rcases List.mem_cons.mp first with firstEq | firstTail
    · subst a
      rcases List.mem_cons.mp second with secondEq | secondTail
      · exact Or.inl secondEq.symm
      · exact Or.inr ((List.pairwise_cons.mp pairwise).1 _ secondTail)
    · rcases List.mem_cons.mp second with secondEq | secondTail
      · subst b
        apply Or.inr
        rcases (List.pairwise_cons.mp pairwise).1 _ firstTail with different | shared
        · exact Or.inl different.symm
        · exact Or.inr ⟨shared.2, shared.1⟩
      · exact ih pairwise.of_cons firstTail secondTail

theorem unique_owner (wf : WellFormedWith classes state pending)
    (owned : Stored state place (some (.owned object)))
    (stored : Stored state otherPlace (some reference))
    (target : reference.object = object) :
    otherPlace = place ∧ reference = .owned object := by
  have pairwise : (ownerOccurrences state).Pairwise (fun a b => Compatible a.2 b.2) := by
    apply List.pairwise_map.mp
    simpa [ownerOccurrences_references] using
      (List.pairwise_append.mp wf.ownersCompatible).2.1
  rcases occurrence_eq_or_compatible pairwise (stored_ownerOccurrence owned)
      (stored_ownerOccurrence stored) with same | compatible
  · exact ⟨(congrArg Prod.fst same).symm, (congrArg Prod.snd same).symm⟩
  · rcases compatible with different | shared
    · exact False.elim (different target.symm)
    · cases shared.1

theorem pending_stored_compatible (wf : WellFormedWith classes state pending)
    (root : reference ∈ pending) (stored : Stored state place (some other)) :
    Compatible reference other :=
  (List.pairwise_append.mp wf.ownersCompatible).2.2 _ root _ (stored_owner stored)

inductive RootSite where
  | variable (name : VariableId)
  | pending (object : ObjectId)
  deriving DecidableEq, Repr

inductive RootOwns (state : State) (pending : List Reference) : RootSite → Reference → Prop where
  | variable : (name, some reference) ∈ state.variables →
      RootOwns state pending (.variable name) reference
  | pending : reference ∈ pending → RootOwns state pending (.pending reference.object) reference

inductive Route (state : State) (pending : List Reference) :
    RootSite → List FieldName → Reference → Prop where
  | root : RootOwns state pending site reference → Route state pending site [] reference
  | field : Route state pending site path parent → (parent.object, data) ∈ state.objects →
      (name, some reference) ∈ data.fields →
      Route state pending site (path ++ [name]) (enter parent.mode reference)

private theorem reference_owned {reference : Reference} (unique : reference.mode = .unique) :
    reference = .owned reference.object := by
  cases reference with
  | reference mode object => dsimp at unique; subst mode; rfl

theorem RootOwns.unique {pending : List Reference} (wf : WellFormedWith classes state pending)
    (left : RootOwns state pending first (.owned object))
    (right : RootOwns state pending second reference) (target : reference.object = object) :
    first = second ∧ reference = .owned object := by
  cases left with
  | «variable» left =>
    cases right with
    | «variable» right =>
      obtain ⟨same, ref⟩ := unique_owner wf
        (show Stored state (.variable _) _ from left)
        (show Stored state (.variable _) _ from right) target
      cases same
      exact ⟨rfl, ref⟩
    | pending right =>
      rcases pending_stored_compatible wf right (show Stored state (.variable _) _ from left) with
        different | shared
      · exact False.elim (different target)
      · cases shared.2
  | pending left =>
    cases right with
    | «variable» right =>
      rcases pending_stored_compatible wf left (show Stored state (.variable _) _ from right) with
        different | shared
      · exact False.elim (different target.symm)
      · cases shared.1
    | pending right =>
      have same : reference = .owned object := by
        rcases reference_eq_or_compatible
            (List.pairwise_append.mp wf.ownersCompatible).1 left right with same | relation
        · exact same.symm
        · rcases relation with different | shared
          · exact False.elim (different target.symm)
          · cases shared.1
      subst reference
      exact ⟨rfl, rfl⟩

theorem RootOwns.not_unique_field {pending : List Reference} (wf : WellFormedWith classes state pending)
    (root : RootOwns state pending site reference)
    (stored : Stored state (.field parent name) (some (.owned object)))
    (target : reference.object = object) : False := by
  cases root with
  | «variable» atRoot =>
    have same := (unique_owner wf stored (show Stored state (.variable _) _ from atRoot) target).1
    cases same
  | pending atRoot =>
    rcases pending_stored_compatible wf atRoot stored with different | shared
    · exact different target
    · cases shared.2

theorem RootOwns.unique_not_field {pending : List Reference}
    (wf : WellFormedWith classes state pending)
    (root : RootOwns state pending site (.owned object))
    (stored : Stored state (.field parent name) (some reference))
    (target : reference.object = object) : False := by
  cases root with
  | «variable» atRoot =>
    have same := (unique_owner wf (show Stored state (.variable _) _ from atRoot) stored target).1
    cases same
  | pending atRoot =>
    rcases pending_stored_compatible wf atRoot stored with different | shared
    · exact different target.symm
    · cases shared.1

-- A wholly unique route is the only route to its target, even when pending
-- expression values are counted as roots. Shared routes may meet freely.
theorem Route.unique (wf : WellFormedWith classes state pending)
    (left : Route state pending first firstPath reference) (unique : reference.mode = .unique)
    (right : Route state pending second secondPath other)
    (target : other.object = reference.object) :
    first = second ∧ firstPath = secondPath ∧ other = reference := by
  induction left generalizing second secondPath other with
  | @root reference atRoot =>
    have ref : reference = .owned reference.object := reference_owned unique
    cases right with
    | root otherRoot =>
      obtain ⟨sameSite, sameReference⟩ := RootOwns.unique wf (ref ▸ atRoot) otherRoot target
      exact ⟨sameSite, rfl, sameReference.trans ref.symm⟩
    | field _ atObject atField =>
      exact False.elim ((ref ▸ atRoot).unique_not_field wf ⟨_, atObject, atField⟩ target)
  | @field path parent data name reference parentRoute atObject atField ih =>
    have modes : parent.mode = .unique ∧ reference.mode = .unique := by
      cases hm : parent.mode <;> cases hr : reference.mode <;>
        simp_all [enter, Mode.join]
    have ref := reference_owned modes.2
    have owned : Stored state (.field parent.object name) (some (.owned reference.object)) :=
      ⟨_, atObject, ref ▸ atField⟩
    cases right with
    | root atRoot => exact False.elim (atRoot.not_unique_field wf owned target)
    | @field _ otherParent otherData otherName otherReference otherPrefix otherObject otherField =>
      obtain ⟨samePlace, sameRef⟩ := unique_owner wf owned (show Stored state (.field otherParent.object otherName) _ from ⟨_, otherObject, otherField⟩) target
      have sameParent := (StoragePlace.field.inj samePlace).1
      have sameName := (StoragePlace.field.inj samePlace).2
      obtain ⟨sites, paths, parents⟩ := ih modes.1 otherPrefix sameParent
      exact ⟨sites, by rw [paths, sameName], by rw [parents, sameRef, ← ref]⟩

theorem Route.follow (route : Route state pending site initial reference)
    (read : readPath state reference path = some (some target)) :
    Route state pending site (initial ++ path) target := by
  induction path generalizing initial reference with
  | nil =>
    cases found : state.objects.lookup reference.object <;> simp [readPath, found] at read
    subst target
    simpa using route
  | cons field rest ih =>
    obtain ⟨data, slot, stored, atField, final | ⟨child, rfl, more⟩⟩ := readPath_cons read
    · rcases final with ⟨rfl, final⟩
      obtain ⟨child, rfl, rfl⟩ := Option.map_eq_some_iff.mp final
      exact .field route stored atField
    · simpa [List.append_assoc] using ih (.field route stored atField) more

theorem Route.allocated (wf : WellFormedWith classes state pending)
    (route : Route state pending site path reference) : Allocated state reference.object := by
  cases route with
  | root owner =>
    apply (wf.referencesComplete reference.object).mp
    cases owner with
    | «variable» stored =>
      exact List.mem_append_right _ (List.mem_append_left _
        (List.mem_filterMap.mpr ⟨(_, some reference), stored, rfl⟩))
    | pending member => exact List.mem_append_left _ (List.mem_map_of_mem member)
  | @field _ _ _ _ child _ stored atField =>
    exact field_allocated (reference := child) wf stored atField

theorem Route.mode_exclusive (wf : WellFormedWith classes state pending)
    (unique : Route state pending first firstPath (.owned object))
    (shared : Route state pending second secondPath (.shared object)) : False := by
  have same := (unique.unique wf rfl shared rfl).2.2
  have mode := congrArg Reference.mode same
  cases mode

theorem route_of_resolve (resolved : Resolve state place source object permission) :
    Route state pending (.variable (splitPlace place).1) (splitPlace place).2
      ⟨permission, object⟩ := by
  induction resolved with
  | «variable» stored => exact .root (.variable stored)
  | field _ stored atField ih => exact .field ih stored atField

theorem resolve_readPath (wf : WellFormedWith classes state pending)
    (resolved : Resolve state place source object permission) :
    ∃ root, ((splitPlace place).1, some root) ∈ state.variables ∧
      readPath state root (splitPlace place).2 = some (some ⟨permission, object⟩) := by
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

theorem take_readPath_frame (wf : WellFormedWith classes before pending)
    (afterWf : WellFormedWith classes after afterPending)
    (taken : Take before source removed after)
    (cut : Route before pending cutSite cutPath (.owned removed))
    (route : Route before pending site initial reference)
    (read : readPath before reference path = some slot)
    (separate : ¬ (site = cutSite ∧ cutPath.IsPrefix (initial ++ path))) :
    readPath after reference path = some slot := by
  induction path generalizing initial reference with
  | nil =>
    cases found : before.objects.lookup reference.object <;> simp [readPath, found] at read
    subst slot
    apply readPath_nil_of_allocated afterWf
    simpa [Allocated, taken.object_keys] using route.allocated wf
  | cons field rest ih =>
    obtain ⟨data, fieldSlot, stored, atField, final | ⟨child, same, more⟩⟩ := readPath_cons read
    all_goals
      have different : StoragePlace.field reference.object field ≠ source := by
        intro equalSource
        have sameSlot : fieldSlot = some (.owned removed) := stored_value_unique wf
          (show Stored before (.field reference.object field) fieldSlot from ⟨data, stored, atField⟩)
          (equalSource ▸ taken.stored)
        have crossing : Route before pending site (initial ++ [field])
            (enter reference.mode (.owned removed)) :=
          .field route stored (sameSlot ▸ atField)
        obtain ⟨sameSite, samePath, _⟩ := cut.unique wf rfl crossing rfl
        apply separate
        refine ⟨sameSite.symm, ?_⟩
        rw [samePath]
        exact ⟨rest, by simp [List.append_assoc]⟩
      have firstRead := readPath_singleton_of_stored afterWf
        (taken.stored_unchanged different (show Stored before (.field reference.object field) fieldSlot from
          ⟨data, stored, atField⟩))
    · rcases final with ⟨rfl, rfl⟩
      exact firstRead
    · subst fieldSlot
      have remaining := ih (.field route stored atField) more (by
        simpa [List.append_assoc] using separate)
      exact (readPath_append afterWf firstRead rest).trans remaining

theorem take_readPath_below (wf : WellFormedWith classes before pending)
    (afterWf : WellFormedWith classes after afterPending)
    (taken : Take before source removed after)
    (below : reference.object.index ≤ removed.index)
    (read : readPath before reference path = some slot) :
    readPath after reference path = some slot := by
  induction path generalizing reference with
  | nil =>
    cases found : before.objects.lookup reference.object <;> simp [readPath, found] at read
    subst slot
    apply readPath_nil_of_allocated afterWf
    rw [Allocated, taken.object_keys]
    exact List.mem_map.mpr ⟨_, lookup_member found, rfl⟩
  | cons field rest ih =>
    obtain ⟨data, fieldSlot, stored, atField, final | ⟨child, same, more⟩⟩ := readPath_cons read
    all_goals
      have different : StoragePlace.field reference.object field ≠ source := by
        intro sameSource
        have sourceField : Stored before (.field reference.object field) (some (.owned removed)) :=
          sameSource ▸ taken.stored
        obtain ⟨sourceData, sourceStored, sourceAtField⟩ := sourceField
        have older := wf.older _ _ _ _ sourceStored sourceAtField
        change removed.index < reference.object.index at older
        omega
      have firstRead := readPath_singleton_of_stored afterWf
        (taken.stored_unchanged different (show Stored before (.field reference.object field) fieldSlot from
          ⟨data, stored, atField⟩))
    · rcases final with ⟨rfl, rfl⟩
      exact firstRead
    · subst fieldSlot
      have childBelow := Nat.le_trans (Nat.le_of_lt (wf.older _ _ _ child stored atField)) below
      exact (readPath_append afterWf firstRead rest).trans (ih childBelow more)

theorem take_readPath_taken (wf : WellFormedWith classes before pending)
    (afterWf : WellFormedWith classes after afterPending)
    (taken : Take before source reference.object after)
    (read : readPath before reference path = some slot) :
    readPath after reference path = some slot :=
  take_readPath_below wf afterWf taken (Nat.le_refl _) read

theorem take_readPath_back (wf : WellFormedWith classes before pending)
    (taken : Take before source removed after)
    (read : readPath after reference path = some (some target)) :
    readPath before reference path = some (some target) := by
  induction path generalizing reference with
  | nil =>
    obtain ⟨data, stored⟩ := readPath_root_allocated read
    obtain ⟨oldData, oldStored, _, _, _⟩ := taken.object_data _ _ stored
    cases found : after.objects.lookup reference.object <;> simp [readPath, found] at read
    subst target
    simp [readPath, lookup_of_member wf.objectKeys oldStored]
  | cons field rest ih =>
    obtain ⟨data, slot, stored, atField, final | ⟨child, rfl, more⟩⟩ := readPath_cons read
    · rcases final with ⟨rfl, final⟩
      obtain ⟨child, rfl, rfl⟩ := Option.map_eq_some_iff.mp final
      obtain ⟨oldData, oldStored, _, _, kept⟩ := taken.object_data _ _ stored
      exact readPath_singleton_of_stored wf ⟨oldData, oldStored, kept _ _ atField⟩
    · obtain ⟨oldData, oldStored, _, _, kept⟩ := taken.object_data _ _ stored
      have firstRead := readPath_singleton_of_stored (reference := reference) wf
        ⟨oldData, oldStored, kept _ _ atField⟩
      exact (readPath_append wf firstRead rest).trans (ih more)

theorem promote_readPath_frame (wf : WellFormedWith classes before pending)
    (afterWf : WellFormedWith classes after afterPending)
    (promoted : Promote before source object after)
    (cut : Route before pending cutSite cutPath (.shared object))
    (route : Route before pending site initial reference)
    (read : readPath before reference path = some slot) :
    readPath after reference path = some slot := by
  induction path generalizing initial reference with
  | nil =>
    cases found : before.objects.lookup reference.object <;> simp [readPath, found] at read
    subst slot
    apply readPath_nil_of_allocated afterWf
    simpa [Allocated, promoted.object_keys] using route.allocated wf
  | cons field rest ih =>
    obtain ⟨data, fieldSlot, stored, atField, final | ⟨child, same, more⟩⟩ := readPath_cons read
    all_goals
      have firstRead : readPath after reference [field] =
          some (fieldSlot.map (enter reference.mode)) := by
        by_cases sameSource : StoragePlace.field reference.object field = source
        · have sameSlot : fieldSlot = some (.owned object) := stored_value_unique wf
            (show Stored before (.field reference.object field) fieldSlot from ⟨data, stored, atField⟩)
            (sameSource ▸ promoted.stored)
          have crossing : Route before pending site (initial ++ [field])
              (enter reference.mode (.owned object)) :=
            .field route stored (sameSlot ▸ atField)
          have sharedMode : reference.mode = .shared := by
            cases hmode : reference.mode with
            | shared => rfl
            | unique =>
              have uniqueCrossing : Route before pending site (initial ++ [field]) (.owned object) := by
                simpa [hmode] using crossing
              exact False.elim (uniqueCrossing.mode_exclusive wf cut)
          have newRead := readPath_singleton_of_stored (reference := reference) afterWf
            (sameSource ▸ promoted.promoted)
          simpa [sameSlot, sharedMode, Reference.shared, Reference.owned] using newRead
        · exact readPath_singleton_of_stored afterWf
            (promoted.stored_unchanged sameSource
              (show Stored before (.field reference.object field) fieldSlot from ⟨data, stored, atField⟩))
    · rcases final with ⟨rfl, rfl⟩
      exact firstRead
    · subst fieldSlot
      exact (readPath_append afterWf firstRead rest).trans (ih (.field route stored atField) more)

theorem promote_readPath_below (wf : WellFormedWith classes before pending)
    (afterWf : WellFormedWith classes after afterPending)
    (promoted : Promote before source object after)
    (below : reference.object.index ≤ object.index)
    (read : readPath before reference path = some slot) :
    readPath after reference path = some slot := by
  induction path generalizing reference with
  | nil =>
    cases found : before.objects.lookup reference.object <;> simp [readPath, found] at read
    subst slot
    apply readPath_nil_of_allocated afterWf
    rw [Allocated, promoted.object_keys]
    exact List.mem_map.mpr ⟨_, lookup_member found, rfl⟩
  | cons field rest ih =>
    obtain ⟨data, fieldSlot, stored, atField, final | ⟨child, same, more⟩⟩ := readPath_cons read
    all_goals
      have different : StoragePlace.field reference.object field ≠ source := by
        intro sameSource
        have sourceField : Stored before (.field reference.object field) (some (.owned object)) :=
          sameSource ▸ promoted.stored
        obtain ⟨sourceData, sourceStored, sourceAtField⟩ := sourceField
        have older := wf.older _ _ _ _ sourceStored sourceAtField
        change object.index < reference.object.index at older
        omega
      have firstRead := readPath_singleton_of_stored afterWf
        (promoted.stored_unchanged different (show Stored before (.field reference.object field) fieldSlot from
          ⟨data, stored, atField⟩))
    · rcases final with ⟨rfl, rfl⟩
      exact firstRead
    · subst fieldSlot
      have childBelow := Nat.le_trans (Nat.le_of_lt (wf.older _ _ _ child stored atField)) below
      exact (readPath_append afterWf firstRead rest).trans (ih childBelow more)

theorem take_readPath_cleared (wf : WellFormedWith classes before pending)
    (afterWf : WellFormedWith classes after afterPending)
    (taken : Take before source removed after) (nonempty : path ≠ [])
    (read : readPath before reference path = some (some target))
    (targetObject : target.object = removed) : readPath after reference path = some none := by
  induction path generalizing reference with
  | nil => exact False.elim (nonempty rfl)
  | cons field rest ih =>
    obtain ⟨data, fieldSlot, stored, atField, final | ⟨child, rfl, more⟩⟩ := readPath_cons read
    · rcases final with ⟨rfl, final⟩
      obtain ⟨child, rfl, rfl⟩ := Option.map_eq_some_iff.mp final
      have same := (unique_owner wf taken.stored
        (show Stored before (.field reference.object field) (some child) from
          ⟨data, stored, atField⟩) targetObject).1
      exact readPath_singleton_of_stored afterWf (same ▸ taken.cleared)
    · by_cases empty : rest = []
      · subst rest
        cases found : before.objects.lookup child.object <;> simp [readPath, found] at more
        subst target
        have same := (unique_owner wf taken.stored
          (show Stored before (.field reference.object field) (some child) from
            ⟨data, stored, atField⟩) targetObject).1
        exact readPath_singleton_of_stored afterWf (same ▸ taken.cleared)
      · have different : StoragePlace.field reference.object field ≠ source := by
          intro same
          have equalSlot := stored_value_unique wf
            (show Stored before (.field reference.object field) (some child) from ⟨data, stored, atField⟩)
            (same ▸ taken.stored)
          have equalReference := Option.some.inj equalSlot
          have less := readPath_index_strict wf empty more
          simp [equalReference, targetObject, enter, Reference.owned] at less
        have firstRead := readPath_singleton_of_stored (reference := reference) afterWf
          (taken.stored_unchanged different
            (show Stored before (.field reference.object field) (some child) from ⟨data, stored, atField⟩))
        exact (readPath_append afterWf firstRead rest).trans (ih empty more)

theorem promote_readPath_back (wf : WellFormedWith classes before pending)
    (promoted : Promote before source object after)
    (sameObject : first.object = second.object)
    (read : readPath after second path = some slot) :
    ∃ oldSlot, readPath before first path = some oldSlot ∧
      oldSlot.map Reference.object = slot.map Reference.object := by
  induction path generalizing first second slot with
  | nil =>
    obtain ⟨data, stored⟩ := readPath_root_allocated read
    obtain ⟨oldData, oldStored, _, _, _⟩ := promoted.object_data _ _ stored
    cases found : after.objects.lookup second.object <;> simp [readPath, found] at read
    subst slot
    refine ⟨some first, ?_, congrArg some sameObject⟩
    simp [readPath, sameObject, lookup_of_member wf.objectKeys oldStored]
  | cons field rest ih =>
    obtain ⟨data, fieldSlot, stored, atField, final | ⟨child, rfl, more⟩⟩ := readPath_cons read
    · obtain ⟨rfl, rfl⟩ := final
      obtain ⟨oldSlot, oldStored, targets⟩ := promoted.stored_back
        (show Stored after (.field second.object field) fieldSlot from ⟨data, stored, atField⟩)
      refine ⟨oldSlot.map (enter first.mode), ?_, ?_⟩
      · exact readPath_singleton_of_stored wf (sameObject ▸ oldStored)
      · simpa [Option.map_map, Function.comp_def] using targets
    · obtain ⟨oldSlot, oldStored, targets⟩ := promoted.stored_back
        (show Stored after (.field second.object field) (some child) from ⟨data, stored, atField⟩)
      obtain ⟨oldChild, rfl, sameTarget⟩ := Option.map_eq_some_iff.mp targets
      obtain ⟨result, tailRead, resultTargets⟩ := ih
        (first := enter first.mode oldChild) (second := enter second.mode child) sameTarget more
      have firstRead := readPath_singleton_of_stored (reference := first) wf
        (sameObject ▸ oldStored)
      exact ⟨result, (readPath_append wf firstRead rest).trans tailRead, resultTargets⟩

theorem promote_readPath_eq (wf : WellFormedWith classes before pending)
    (afterWf : WellFormedWith classes after afterPending)
    (promoted : Promote before source object after)
    (cut : Route before pending cutSite cutPath (.shared object))
    (route : Route before pending site initial reference) (path : List FieldName) :
    readPath after reference path = readPath before reference path := by
  cases beforeRead : readPath before reference path with
  | some slot => exact promote_readPath_frame wf afterWf promoted cut route beforeRead
  | none =>
    cases afterRead : readPath after reference path with
    | none => rfl
    | some slot =>
      obtain ⟨oldSlot, oldRead, _⟩ := promote_readPath_back wf promoted rfl afterRead
      rw [beforeRead] at oldRead
      contradiction

theorem promote_readPath_below_eq (wf : WellFormedWith classes before pending)
    (afterWf : WellFormedWith classes after afterPending)
    (promoted : Promote before source object after)
    (below : reference.object.index ≤ object.index) (path : List FieldName) :
    readPath after reference path = readPath before reference path := by
  cases beforeRead : readPath before reference path with
  | some slot => exact promote_readPath_below wf afterWf promoted below beforeRead
  | none =>
    cases afterRead : readPath after reference path with
    | none => rfl
    | some slot =>
      obtain ⟨oldSlot, oldRead, _⟩ := promote_readPath_back wf promoted rfl afterRead
      rw [beforeRead] at oldRead
      contradiction

end Dada.Shared.Typing
