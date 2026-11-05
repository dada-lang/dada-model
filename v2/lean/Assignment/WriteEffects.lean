import Assignment.Write
import Shared.TypingPathEffects

namespace Dada.Assignment
open Shared Shared.Typing

theorem Write.stored_unchanged (taken : Write before source reference after)
    (different : place ≠ source) (stored : Stored before place slot) :
    Stored after place slot := by
  cases taken with
  | «variable» objects nextId leading trailing name previous reference =>
    cases place with
    | «variable» other =>
      simp only [Stored, List.mem_append, List.mem_cons] at stored ⊢
      rcases stored with member | same | member
      · exact Or.inl member
      · cases same
        exact False.elim (different rfl)
      · exact Or.inr (Or.inr member)
    | field parent fieldName => exact stored
  | field variables nextId leading trailing parent className beforeFields afterFields name previous reference =>
    cases place with
    | «variable» other => exact stored
    | field other otherField =>
      obtain ⟨data, atObject, atField⟩ := stored
      simp only [List.mem_append, List.mem_cons] at atObject
      rcases atObject with member | same | member
      · exact ⟨data, List.mem_append_left _ member, atField⟩
      · cases same
        refine ⟨⟨className, beforeFields ++ (name, some reference) :: afterFields⟩, by simp, ?_⟩
        simp only [List.mem_append, List.mem_cons] at atField ⊢
        rcases atField with member | same | member
        · exact Or.inl member
        · cases same
          exact False.elim (different rfl)
        · exact Or.inr (Or.inr member)
      · exact ⟨data, List.mem_append_right _ (List.mem_cons_of_mem _ member), atField⟩

theorem Write.stored_back_unchanged (taken : Write before source reference after)
    (different : place ≠ source) (stored : Stored after place slot) :
    Stored before place slot := by
  cases taken with
  | «variable» objects nextId leading trailing name previous reference =>
    cases place with
    | «variable» other =>
      simp only [Stored, List.mem_append, List.mem_cons] at stored ⊢
      rcases stored with member | same | member
      · exact Or.inl member
      · cases same
        exact False.elim (different rfl)
      · exact Or.inr (Or.inr member)
    | field parent fieldName => exact stored
  | field variables nextId leading trailing parent className beforeFields afterFields name previous reference =>
    cases place with
    | «variable» other => exact stored
    | field other otherField =>
      obtain ⟨data, atObject, atField⟩ := stored
      simp only [List.mem_append, List.mem_cons] at atObject
      rcases atObject with member | same | member
      · exact ⟨data, List.mem_append_left _ member, atField⟩
      · cases same
        refine ⟨⟨className, beforeFields ++ (name, previous) :: afterFields⟩, by simp, ?_⟩
        simp only [List.mem_append, List.mem_cons] at atField ⊢
        rcases atField with member | same | member
        · exact Or.inl member
        · cases same
          exact False.elim (different rfl)
        · exact Or.inr (Or.inr member)
      · exact ⟨data, List.mem_append_right _ (List.mem_cons_of_mem _ member), atField⟩

theorem Write.old_object_data (taken : Write before place reference after)
    (id : ObjectId) (data : Object) (stored : (id, data) ∈ before.objects) :
    ∃ newData, (id, newData) ∈ after.objects ∧ newData.className = data.className := by
  cases taken with
  | «variable» => exact ⟨data, stored, rfl⟩
  | field variables nextId leading trailing parent className beforeFields afterFields name previous reference =>
    simp only [List.mem_append, List.mem_cons] at stored
    rcases stored with member | same | member
    · exact ⟨data, List.mem_append_left _ member, rfl⟩
    · cases same
      exact ⟨⟨className, beforeFields ++ (name, some reference) :: afterFields⟩, by simp, rfl⟩
    · exact ⟨data, List.mem_append_right _ (List.mem_cons_of_mem _ member), rfl⟩

theorem Write.variableKeys (written : Write before place reference after) :
    after.variables.map Prod.fst = before.variables.map Prod.fst := by
  cases written <;> simp

theorem Write.installed (written : Write before place reference after) :
    Stored after place (some reference) := by
  cases written with
  | «variable» => simp [Stored]
  | field variables nextId leading trailing parent className beforeFields afterFields name previous reference =>
    exact ⟨⟨className, beforeFields ++ (name, some reference) :: afterFields⟩, by simp, by simp⟩

theorem Write.previous (written : Write before place reference after) :
    ∃ previous, Stored before place previous ∧
      (reference :: Owners before).Perm (previous.toList ++ Owners after) := by
  cases written with
  | «variable» objects nextId leading trailing name previous reference =>
    refine ⟨previous, by simp [Stored], ?_⟩
    apply List.perm_iff_count.mpr
    intro r
    cases previous <;> simp [Owners, List.count_append, List.count_cons, List.filterMap_append] <;> omega
  | field variables nextId leading trailing parent className beforeFields afterFields name previous reference =>
    refine ⟨previous, ⟨⟨className, beforeFields ++ (name, previous) :: afterFields⟩, by simp, by simp⟩, ?_⟩
    apply List.perm_iff_count.mpr
    intro r
    cases previous <;> simp [Owners, List.count_append, List.count_cons, List.filterMap_append, List.flatMap_append] <;> omega

-- A unique route to the parent cannot pass through the field being replaced.
theorem Write.parent_route (wf : WellFormedWith classes before pending)
    (written : Write before (.field parent name) incoming after)
    (cut : Route before pending (.variable root) cutPath (.owned parent))
    (route : Route before pending (.variable root) path reference)
    (short : path.length ≤ cutPath.length) :
    Route after otherPending (.variable root) path reference := by
  induction route with
  | root owner =>
    cases owner with
    | «variable» stored =>
      exact .root (.variable (written.stored_unchanged (place := .variable root) (by simp) stored))
  | @field oldPath parentRef data field child previousRoute obj stored ih =>
    have smaller : oldPath.length ≤ cutPath.length := by simp only [List.length_append, List.length_singleton] at short; omega
    have different : StoragePlace.field parentRef.object field ≠ .field parent name := by
      intro same
      have ids := (StoragePlace.field.inj same).1
      have paths := (cut.unique wf rfl previousRoute ids).2.1
      have lengths := congrArg List.length paths
      simp only [List.length_append, List.length_singleton] at short
      omega
    obtain ⟨newData, newObj, newField⟩ := written.stored_unchanged different ⟨data,obj,stored⟩
    exact .field (ih smaller) newObj newField

-- Only observations that actually cross the changed field can differ.
theorem write_readPath_frame (wf : WellFormedWith classes before pending)
    (afterWf : WellFormedWith classes after afterPending)
    (written : Write before (.field parent name) incoming after)
    (cut : Route before pending cutSite cutPath (.owned parent))
    (route : Route before pending site initial reference)
    (read : readPath before reference path = some slot)
    (separate : ∀ pre post, path = pre ++ name :: post →
      ¬ (site = cutSite ∧ initial ++ pre = cutPath)) :
    readPath after reference path = some slot := by
  induction path generalizing initial reference with
  | nil =>
    cases found : before.objects.lookup reference.object <;> simp [readPath, found] at read
    subst slot
    apply readPath_nil_of_allocated afterWf
    simpa [Allocated, written.objectKeys] using route.allocated wf
  | cons field rest ih =>
    obtain ⟨data, fieldSlot, stored, atField, final | ⟨child, same, more⟩⟩ := readPath_cons read
    all_goals
      have different : StoragePlace.field reference.object field ≠ .field parent name := by
        intro sameSource
        obtain ⟨sameObject, rfl⟩ := StoragePlace.field.inj sameSource
        obtain ⟨sameSite, samePath, _⟩ := cut.unique wf rfl route sameObject
        exact separate [] rest rfl ⟨sameSite.symm, by simpa using samePath.symm⟩
      have firstRead := readPath_singleton_of_stored afterWf
        (written.stored_unchanged different (show Stored before (.field reference.object field) fieldSlot from
          ⟨data, stored, atField⟩))
    · rcases final with ⟨rfl, rfl⟩
      exact firstRead
    · subst fieldSlot
      have remaining := ih (.field route stored atField) more (by
        intro pre post eq same
        apply separate (field :: pre) post (by simp [eq])
        exact ⟨same.1, by simpa [List.append_assoc] using same.2⟩)
      exact (readPath_append afterWf firstRead rest).trans remaining

theorem write_readPath_back_frame (wf : WellFormedWith classes before pending)
    (afterWf : WellFormedWith classes after afterPending)
    (written : Write before (.field parent name) incoming after)
    (cut : Route after afterPending cutSite cutPath (.owned parent))
    (route : Route after afterPending site initial reference)
    (read : readPath after reference path = some slot)
    (separate : ∀ pre post, path = pre ++ name :: post →
      ¬ (site = cutSite ∧ initial ++ pre = cutPath)) :
    readPath before reference path = some slot := by
  induction path generalizing initial reference with
  | nil =>
    cases found : after.objects.lookup reference.object <;> simp [readPath, found] at read
    subst slot
    apply readPath_nil_of_allocated wf
    simpa [Allocated, written.objectKeys] using route.allocated afterWf
  | cons field rest ih =>
    obtain ⟨data, fieldSlot, stored, atField, final | ⟨child, same, more⟩⟩ := readPath_cons read
    all_goals
      have different : StoragePlace.field reference.object field ≠ .field parent name := by
        intro sameSource
        obtain ⟨sameObject, rfl⟩ := StoragePlace.field.inj sameSource
        obtain ⟨sameSite, samePath, _⟩ := cut.unique afterWf rfl route sameObject
        exact separate [] rest rfl ⟨sameSite.symm, by simpa using samePath.symm⟩
      have firstRead := readPath_singleton_of_stored wf
        (written.stored_back_unchanged different (show Stored after (.field reference.object field) fieldSlot from
          ⟨data, stored, atField⟩))
    · rcases final with ⟨rfl, rfl⟩
      exact firstRead
    · subst fieldSlot
      have remaining := ih (.field route stored atField) more (by
        intro pre post eq same
        apply separate (field :: pre) post (by simp [eq])
        exact ⟨same.1, by simpa [List.append_assoc] using same.2⟩)
      exact (readPath_append wf firstRead rest).trans remaining

theorem write_readPath_other (wf : WellFormedWith classes before pending)
    (afterWf : WellFormedWith classes after afterPending)
    (written : Write before (.field parent name) incoming after)
    (cut : Route before pending cutSite cutPath (.owned parent))
    (route : Route before pending site initial reference)
    (different : site ≠ cutSite) (read : readPath before reference path = some slot) :
    readPath after reference path = some slot :=
  write_readPath_frame wf afterWf written cut route read (fun _ _ _ both => different both.1)

theorem write_readPath_descendant (wf : WellFormedWith classes before pending)
    (afterWf : WellFormedWith classes after afterPending)
    (written : Write before (.field parent name) incoming after)
    (cut : Route before pending cutSite cutPath (.owned parent))
    (route : Route before pending site initial reference)
    (longer : cutPath.length < initial.length) (read : readPath before reference path = some slot) :
    readPath after reference path = some slot := by
  apply write_readPath_frame wf afterWf written cut route read
  intro pre post _ both
  have lengths := congrArg List.length both.2
  simp only [List.length_append] at lengths
  omega

theorem readPath_eq_of_success
    (forward : ∀ slot, readPath before reference path = some slot → readPath after reference path = some slot)
    (backward : ∀ slot, readPath after reference path = some slot → readPath before reference path = some slot) :
    readPath after reference path = readPath before reference path := by
  cases b : readPath before reference path with
  | some slot => exact forward slot b
  | none =>
    cases a : readPath after reference path with
    | none => rfl
    | some slot => have impossible := backward slot a; simp [b] at impossible

end Dada.Assignment
