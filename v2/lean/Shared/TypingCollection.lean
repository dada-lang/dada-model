import Shared.TypingBindingPending
import Shared.Frames

noncomputable section
namespace Dada.Shared.Typing

inductive Reachable (objects : List (ObjectId × Object)) (roots : List Reference) : ObjectId → Prop where
  | root {reference} : reference ∈ roots → Reachable objects roots reference.object
  | field {parent data name reference} : Reachable objects roots parent →
      (parent, data) ∈ objects → (name, some reference) ∈ data.fields →
      Reachable objects roots reference.object

def rootReferences (state : State) (pending : PendingValues) : List Reference :=
  pending.map Prod.fst ++ state.variables.filterMap Prod.snd

def collectPending (state : State) (pending : PendingValues) : State := by
  classical
  exact { state with objects := state.objects.filter (fun entry => decide (Reachable state.objects (rootReferences state pending) entry.1)) }

theorem collectPending_member {id : ObjectId} {data : Object} : (id, data) ∈ (collectPending state pending).objects ↔
    (id, data) ∈ state.objects ∧ Reachable state.objects (rootReferences state pending) id := by
  classical
  simp [collectPending]

theorem lookup_filter_keep {K V : Type} [BEq K] [LawfulBEq K]
    (entries : List (K × V)) (keep : K → Bool) (key : K) (kept : keep key = true) :
    (entries.filter (fun entry => keep entry.1)).lookup key = entries.lookup key := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨k,v⟩
    by_cases same : key = k
    · subst k; simp [kept]
    · cases h : keep k <;> simp [h, List.lookup_cons, beq_eq_false_iff_ne.mpr same, ih]

theorem readPath_collectPending (live : Reachable state.objects (rootReferences state pending) reference.object)
    (path : Path) : readPath (collectPending state pending) reference path = readPath state reference path := by
  classical
  have lookup (reference : Reference) (h : Reachable state.objects (rootReferences state pending) reference.object) :
      (collectPending state pending).objects.lookup reference.object = state.objects.lookup reference.object :=
    lookup_filter_keep state.objects (fun id => decide (Reachable state.objects (rootReferences state pending) id)) reference.object (by simpa using h)
  induction path generalizing reference with
  | nil => simp only [readPath_nil, lookup reference live]
  | cons field rest ih =>
    cases rest with
    | nil => simp only [readPath_singleton, lookup reference live]
    | cons next rest =>
      cases found : state.objects.lookup reference.object with
      | none => simp [readPath, lookup reference live, found]
      | some data =>
        cases slot : data.fields.lookup field with
        | none => simp [readPath, lookup reference live, found, slot]
        | some slotValue =>
          cases slotValue with
          | none => simp [readPath, lookup reference live, found, slot]
          | some child =>
            have childLive := Reachable.field live (lookup_member found) (lookup_member slot)
            simpa [readPath, lookup reference live, found, slot] using ih (reference := enter reference.mode child) childLive

theorem readPath_reachable (live : Reachable state.objects roots reference.object)
    (read : readPath state reference path = some (some target)) : Reachable state.objects roots target.object := by
  induction path generalizing reference with
  | nil =>
    cases found : state.objects.lookup reference.object <;> simp [readPath, found] at read
    subst target; exact live
  | cons field rest ih =>
    obtain ⟨data, slot, stored, fieldStored, final | ⟨child, rfl, more⟩⟩ := readPath_cons read
    · obtain ⟨rfl, final⟩ := final
      obtain ⟨child, rfl, rfl⟩ := Option.map_eq_some_iff.mp final
      exact Reachable.field (reference := child) live stored fieldStored
    · exact ih (reference := enter reference.mode child) (Reachable.field (reference := child) live stored fieldStored) more

theorem Satisfies.collect_pending (satisfied : Satisfies classes state reference ty)
    (live : Reachable state.objects (rootReferences state pending) reference.object) :
    Satisfies classes (collectPending state pending) reference ty := by
  constructor
  · exact satisfied.mode
  · obtain ⟨data, member, name⟩ := satisfied.root
    exact ⟨data, collectPending_member.mpr ⟨member, live⟩, name⟩
  · intro path positive
    obtain ⟨target, data, read, member, name⟩ := satisfied.positive path positive
    exact ⟨target, data, (readPath_collectPending live _).trans read,
      collectPending_member.mpr ⟨member, readPath_reachable live read⟩, name⟩
  · intro path negative
    exact (readPath_collectPending live _).trans (satisfied.negative path negative)
  · intro path target permission declared read
    exact satisfied.modes path target permission declared ((readPath_collectPending live _).symm.trans read)

private theorem owners_targets (state : State) :
    (Owners state).map Reference.object = References state := by
  simp [Owners, References, List.map_filterMap, List.map_flatMap]

private theorem flatMap_filter_sublist {A B : Type} (xs : List A) (test : A → Bool) (f : A → List B) :
    ((xs.filter test).flatMap f).Sublist (xs.flatMap f) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih =>
    cases h : test x
    · simp only [List.filter_cons, h, Bool.false_eq_true, ↓reduceIte, List.flatMap_cons]
      exact ih.trans (List.sublist_append_right _ _)
    · simpa only [List.filter_cons, h, ↓reduceIte, List.flatMap_cons] using
        (List.Sublist.refl (f x)).append ih

theorem Realizes.collect_pending (realized : Realizes classes environment state pending)
    (subset : kept.Sublist pending) : Realizes classes environment (collectPending state kept) kept := by
  classical
  let roots := rootReferences state kept
  have oldMember {id data} (h : (id, data) ∈ (collectPending state kept).objects) :
      (id, data) ∈ state.objects := (collectPending_member.mp h).1
  have variableLive {name reference} (h : (name, some reference) ∈ state.variables) :
      Reachable state.objects roots reference.object :=
    .root (List.mem_append_right _ (List.mem_filterMap.mpr ⟨_, h, rfl⟩))
  have pendingLive {reference ty} (h : (reference, ty) ∈ kept) :
      Reachable state.objects roots reference.object :=
    .root (List.mem_append_left _ (List.mem_map.mpr ⟨_, h, rfl⟩))
  have liveAllocated {id} (live : Reachable state.objects roots id) : Allocated state id := by
    apply (realized.ownership.referencesComplete id).mp
    cases live with
    | root member =>
      change _ ∈ kept.map Prod.fst ++ state.variables.filterMap Prod.snd at member
      rcases List.mem_append.mp member with p | v
      · obtain ⟨pair, pairMember, rfl⟩ := List.mem_map.mp p
        exact List.mem_append_left _ (List.mem_map.mpr ⟨pair.1,
          List.mem_map.mpr ⟨pair, subset.subset pairMember, rfl⟩, rfl⟩)
      · obtain ⟨⟨name, slot⟩, slotMember, value⟩ := List.mem_filterMap.mp v
        change slot = some _ at value
        subst slot
        exact List.mem_append_right _ (variable_reference_mem slotMember)
    | field _ stored field => exact List.mem_append_right _ (field_reference_mem stored field)
  have retained {id} (live : Reachable state.objects roots id) :
      Allocated (collectPending state kept) id := by
    obtain ⟨⟨_,data⟩, member, rfl⟩ := List.mem_map.mp (liveAllocated live)
    exact List.mem_map.mpr ⟨(_,data), collectPending_member.mpr ⟨member, live⟩, rfl⟩
  constructor
  · exact realized.classesWellFormed
  · exact realized.environmentWellFormed
  · intro reference ty member; exact realized.pendingTypes _ _ (subset.subset member)
  · constructor
    · exact realized.ownership.objectKeys.sublist (List.filter_sublist.map Prod.fst)
    · exact realized.ownership.variableKeys
    · intro id data member; exact realized.ownership.shapes _ _ (oldMember member)
    · intro id data member; exact realized.ownership.bounds _ _ (oldMember member)
    · intro id data name reference member field; exact realized.ownership.older _ _ _ _ (oldMember member) field
    · apply List.Pairwise.sublist _ realized.ownership.ownersCompatible
      apply List.Sublist.append (subset.map Prod.fst)
      apply List.Sublist.append (List.Sublist.refl _)
      exact flatMap_filter_sublist _ _ _
    · intro id
      constructor
      · intro member
        rw [← owners_targets, ← List.map_append] at member
        obtain ⟨reference, refMember, rfl⟩ := List.mem_map.mp member
        rcases List.mem_append.mp refMember with pendingMember | owner
        · obtain ⟨pair, pairMember, rfl⟩ := List.mem_map.mp pendingMember
          exact retained (pendingLive pairMember)
        · rcases List.mem_append.mp owner with variableMember | field
          · obtain ⟨⟨name, slot⟩, slotMember, value⟩ := List.mem_filterMap.mp variableMember
            change slot = some _ at value
            subst slot
            exact retained (variableLive slotMember)
          · obtain ⟨⟨parent,data⟩, member, fieldMember⟩ := List.mem_flatMap.mp field
            obtain ⟨⟨name, slot⟩, slotMember, value⟩ := List.mem_filterMap.mp fieldMember
            change slot = some _ at value
            subst slot
            have live := (collectPending_member.mp member).2
            exact retained (.field live (oldMember member) slotMember)
      · intro allocated
        obtain ⟨⟨id',data⟩, member, rfl⟩ := List.mem_map.mp allocated
        have live := (collectPending_member.mp member).2
        cases live with
        | root rootMember =>
          change _ ∈ kept.map Prod.fst ++ state.variables.filterMap Prod.snd at rootMember
          rcases List.mem_append.mp rootMember with p | v
          · exact List.mem_append_left _ (List.mem_map.mpr ⟨_, p, rfl⟩)
          · exact List.mem_append_right _ (by
              rw [← owners_targets]
              exact List.mem_map.mpr ⟨_, List.mem_append_left _ v, rfl⟩)
        | @field parent data name reference live stored field =>
          exact List.mem_append_right _ (field_reference_mem
            (collectPending_member.mpr ⟨stored, live⟩) field)
  · intro parent data field target stored fieldStored
    obtain ⟨decl, ty, targetData, declared, described, targetStored, name⟩ :=
      realized.fields _ _ _ _ (oldMember stored) fieldStored
    exact ⟨decl, ty, targetData, declared, described,
      collectPending_member.mpr ⟨targetStored, .field (collectPending_member.mp stored).2 (oldMember stored) fieldStored⟩, name⟩
  · exact realized.variableDomain
  · exact realized.emptyVariables
  · intro name ty member
    obtain ⟨reference, stored, satisfied⟩ := realized.initializedVariables _ _ member
    exact ⟨reference, stored, satisfied.collect_pending (variableLive stored)⟩
  · intro reference ty member
    exact (realized.pendingValues _ _ (subset.subset member)).collect_pending (pendingLive member)

end Dada.Shared.Typing
end
