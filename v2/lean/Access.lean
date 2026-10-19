import PlaceEffects

namespace Dada.Heap

variable {Primitive : Type}

-- Effective access is accumulated along a route. It is not a meet: an inner
-- independently shared owner retains its ownership even through a borrowed route.
inductive AccessPermission where
  | given
  | leased
  | showned
  | shlease
  deriving DecidableEq

def AccessPermission.project (context : AccessPermission) : Reference → Option AccessPermission
  | .owned _ => some context
  | .showned _ => some .showned
  | .shlease _ => some .shlease
  | .leased _ => match context with
    | .given | .leased => some .leased
    | .showned | .shlease => none

theorem AccessPermission.owned_preserves_context (context : AccessPermission) (id : ObjectId) :
    context.project (.owned id) = some context := rfl

theorem AccessPermission.shared_owned_not_given (id : ObjectId) :
    AccessPermission.showned.project (.owned id) ≠ some .given ∧
    AccessPermission.shlease.project (.owned id) ≠ some .given := by
  constructor <;> simp [project]

theorem AccessPermission.shared_rejects_lease (place : Place) :
    AccessPermission.showned.project (.leased place) = none ∧
    AccessPermission.shlease.project (.leased place) = none := by
  constructor <;> rfl

-- A derivation follows finitely many supporting slots. Lease support must itself
-- provide unique access: a chain ending at a shared reference cannot resolve.
-- This describes available route permissions, not borrow activity or invalidation.
inductive ResolveReference (state : State Primitive) : AccessPermission → Reference → ObjectId → AccessPermission → Prop where
  | owned (live : AllocatedObject state object) :
      ResolveReference state context (.owned object) object context
  | showned (live : AllocatedObject state object) :
      ResolveReference state context (.showned object) object .showned
  | shlease (live : AllocatedObject state object) :
      ResolveReference state context (.shlease object) object .shlease
  | leased
      (allowed : context.project (.leased support) = some .leased)
      (stored : readSlot state support = some (.initialized reference))
      (target : ResolveReference state .leased reference object .leased) :
      ResolveReference state context (.leased support) object .leased

inductive ResolvePlace (state : State Primitive) : AccessPermission → Place → ObjectId → AccessPermission → Prop where
  | intro
      (stored : readSlot state place = some (.initialized reference))
      (target : ResolveReference state context reference object permission) :
      ResolvePlace state context place object permission

-- Each prefix is resolved before its next projection. readSlot checks the parent
-- object's shape and the field's existence or element's bounds. The selected
-- final slot is retained alongside its target and the effective access.
inductive ResolvePath (state : State Primitive) : AccessPath → Place → ObjectId → AccessPermission → Prop where
  | variable (target : ResolvePlace state .given (.variable rootVariable) object permission) :
      ResolvePath state (.path rootVariable []) (.variable rootVariable) object permission
  | field
      (prior : ResolvePath state (.path rootVariable projections) prefixPlace parent context)
      (target : ResolvePlace state context (.field parent name) object permission) :
      ResolvePath state (.path rootVariable (projections ++ [.field name]))
        (.field parent name) object permission
  | index
      (prior : ResolvePath state (.path rootVariable projections) prefixPlace parent context)
      (target : ResolvePlace state context (.element parent index) object permission) :
      ResolvePath state (.path rootVariable (projections ++ [.index index]))
        (.element parent index) object permission

-- Releasing a field mutates its containing object, which shared references alias.
-- Destructive access requires unique prefixes, even when the final field is
-- itself an owning showned handle. Destruction through shared views is unspecified.
inductive WritablePath (state : State Primitive) (path : AccessPath) : Prop where
  | intro
      (uniquePrefixes : ∀ {rootVariable projections projection remaining prefixPlace object permission},
        path = .path rootVariable (projections ++ projection :: remaining) →
        ResolvePath state (.path rootVariable projections) prefixPlace object permission →
        permission = .given ∨ permission = .leased) :
      WritablePath state path

theorem WritablePath.variable (state : State Primitive) (rootVariable : VariableId) :
    WritablePath state (.path rootVariable []) := by
  constructor
  intro other projections projection remaining prefixPlace object permission equal _
  have lengths := congrArg List.length (AccessPath.path.inj equal).2
  simp only [List.length_nil, List.length_append, List.length_cons] at lengths
  omega

theorem WritablePath.no_shared_prefix
    (shared : ResolvePath state (.path rootVariable projections) place object .shlease)
    (projection : Projection) (remaining : List Projection) :
    ¬ WritablePath state (.path rootVariable (projections ++ projection :: remaining)) := by
  intro writable
  cases writable with
  | intro uniquePrefixes =>
    rcases uniquePrefixes rfl shared with impossible | impossible <;> cases impossible

theorem WritablePath.no_showned_prefix
    (shared : ResolvePath state (.path rootVariable projections) place object .showned)
    (projection : Projection) (remaining : List Projection) :
    ¬ WritablePath state (.path rootVariable (projections ++ projection :: remaining)) := by
  intro writable
  cases writable with
  | intro uniquePrefixes =>
    rcases uniquePrefixes rfl shared with impossible | impossible <;> cases impossible

theorem ResolveReference.project_eq
    (resolved : ResolveReference state context reference object permission) :
    context.project reference = some permission := by
  cases resolved with
  | owned => rfl
  | showned => rfl
  | shlease => rfl
  | leased allowed _ _ => exact allowed

theorem ResolveReference.live
    (resolved : ResolveReference state context reference object permission) :
    AllocatedObject state object := by
  induction resolved with
  | owned live => exact live
  | showned live => exact live
  | shlease live => exact live
  | leased _ _ _ ih => exact ih

theorem ResolveReference.deterministic
    (left : ResolveReference state context reference object permission)
    (right : ResolveReference state context reference other otherPermission) :
    object = other ∧ permission = otherPermission := by
  induction left generalizing other otherPermission with
  | owned => cases right; exact ⟨rfl, rfl⟩
  | showned => cases right; exact ⟨rfl, rfl⟩
  | shlease => cases right; exact ⟨rfl, rfl⟩
  | leased allowed stored target ih =>
      cases right with
      | leased _ otherStored otherTarget =>
          have same := Option.some.inj (stored.symm.trans otherStored)
          cases same
          exact ⟨(ih otherTarget).1, rfl⟩

theorem ResolvePlace.deterministic
    (left : ResolvePlace state context place object permission)
    (right : ResolvePlace state context place other otherPermission) :
    object = other ∧ permission = otherPermission := by
  cases left with
  | intro stored target =>
    cases right with
    | intro otherStored otherTarget =>
      have same := Option.some.inj (stored.symm.trans otherStored)
      cases same
      exact target.deterministic otherTarget

theorem ResolvePlace.given_reference
    (resolved : ResolvePlace state context place object .given) :
    ReferenceAt state place (.owned object) := by
  cases resolved with
  | intro stored target =>
    cases target with
    | owned _ => exact readSlot_stored.mp stored

-- Effective shared ownership may be inherited through an owned inner edge.
-- It does not by itself say that the selected stored reference is showned.
theorem ResolvePlace.showned_reference
    (resolved : ResolvePlace state context place object .showned) :
    ReferenceAt state place (.showned object) ∨
      (context = .showned ∧ ReferenceAt state place (.owned object)) := by
  cases resolved with
  | intro stored target =>
    cases target with
    | owned _ => exact Or.inr ⟨rfl, readSlot_stored.mp stored⟩
    | showned _ => exact Or.inl (readSlot_stored.mp stored)

theorem ResolvePath.selected
    (resolved : ResolvePath state path place object permission) :
    ∃ context, ResolvePlace state context place object permission := by
  cases resolved with
  | «variable» target => exact ⟨.given, target⟩
  | field _ target => exact ⟨_, target⟩
  | index _ target => exact ⟨_, target⟩

theorem ResolvePath.given_reference
    (resolved : ResolvePath state path place object .given) :
    ReferenceAt state place (.owned object) := by
  obtain ⟨_, target⟩ := resolved.selected
  exact target.given_reference

theorem ResolveReference.no_self_support
    (resolved : ResolveReference state context reference object permission) :
    ∀ place, readSlot state place = some (.initialized (.leased place)) →
      reference ≠ .leased place := by
  induction resolved with
  | owned => intro place _ equal; cases equal
  | showned => intro place _ equal; cases equal
  | shlease => intro place _ equal; cases equal
  | leased allowed stored target ih =>
    intro place self equal
    cases equal
    have same := Option.some.inj (stored.symm.trans self)
    cases same
    exact ih _ self rfl

theorem ResolvePlace.missing
    (missing : readSlot state place = none) :
    ¬ ResolvePlace state context place object permission := by
  intro resolved
  cases resolved with
  | intro stored _ => simp [missing] at stored

private def auditObject : ObjectId := ⟨0⟩
private def auditChild : ObjectId := ⟨1⟩
private def auditVariable : VariableId := ⟨0⟩

private def auditState (inner : Reference) : State Nat :=
  .state
    ⟨[(auditObject, .aggregate ⟨[("f", .initialized inner)], by simp⟩),
      (auditChild, .primitive 22)], by simp [auditObject, auditChild]⟩
    ⟨[(auditVariable, .initialized (.shlease auditObject)),
      (⟨1⟩, .initialized (.owned auditObject))], by decide⟩

-- ANCHOR: shared_route_owned_field
example : ResolvePath (auditState (.owned auditChild))
    (.path auditVariable [.field "f"]) (.field auditObject "f") auditChild .shlease := by
  apply ResolvePath.field (projections := [])
  · apply ResolvePath.variable
    apply ResolvePlace.intro (by rfl)
    apply ResolveReference.shlease
    simp [AllocatedObject, auditState]
  · apply ResolvePlace.intro (by rfl)
    apply ResolveReference.owned
    simp [AllocatedObject, auditState]
-- ANCHOR_END: shared_route_owned_field

-- ANCHOR: shared_route_showned_field
example : ResolvePath (auditState (.showned auditChild))
    (.path auditVariable [.field "f"]) (.field auditObject "f") auditChild .showned := by
  apply ResolvePath.field (projections := [])
  · apply ResolvePath.variable
    apply ResolvePlace.intro (by rfl)
    apply ResolveReference.shlease
    simp [AllocatedObject, auditState]
  · apply ResolvePlace.intro (by rfl)
    apply ResolveReference.showned
    simp [AllocatedObject, auditState]
-- ANCHOR_END: shared_route_showned_field

-- ANCHOR: shared_route_rejects_lease
example (state : State Nat) (place : Place) (object : ObjectId) (permission : AccessPermission) :
    ¬ ResolveReference state .shlease (.leased place) object permission := by
  intro resolved
  have allowed := resolved.project_eq
  simp [AccessPermission.project] at allowed
-- ANCHOR_END: shared_route_rejects_lease

-- ANCHOR: missing_lease_support
example (state : State Nat) (place : Place) (object : ObjectId)
    (context permission : AccessPermission) (missing : readSlot state place = none) :
    ¬ ResolveReference state context (.leased place) object permission := by
  intro resolved
  cases resolved with
  | leased _ stored _ => simp [missing] at stored
-- ANCHOR_END: missing_lease_support

-- ANCHOR: cyclic_lease_support
example (state : State Nat) (place : Place) (object : ObjectId)
    (context permission : AccessPermission)
    (self : readSlot state place = some (.initialized (.leased place))) :
    ¬ ResolveReference state context (.leased place) object permission := by
  intro resolved
  exact resolved.no_self_support place self rfl
-- ANCHOR_END: cyclic_lease_support

end Dada.Heap
