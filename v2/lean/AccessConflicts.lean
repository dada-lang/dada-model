import Heap

namespace Dada.Heap

-- A basic live-lien table over syntactic access paths. A caller
-- supplies liens derived from types of variables live after the operation.
-- This does not compute liveness, resolve aliases, check initialization, or
-- implement runtime invalidation. Field-local dependent-type restrictions and
-- guard-sensitive dead-link cancellation remain outside this table.

deriving instance DecidableEq for Projection

def AccessPath.IsPrefix : AccessPath → AccessPath → Prop
  | .path x projections, .path y other =>
      x = y ∧ projections.IsPrefix other

-- Paths overlap precisely when one is a prefix of the other.
-- Different roots are syntactically disjoint; this is not a heap alias proof.
def AccessPath.Disjoint (left right : AccessPath) : Prop :=
  ¬ left.IsPrefix right ∧ ¬ right.IsPrefix left

theorem AccessPath.prefix_refl (path : AccessPath) : path.IsPrefix path := by
  cases path
  exact ⟨rfl, List.prefix_refl _⟩

theorem AccessPath.not_disjoint_self (path : AccessPath) : ¬ path.Disjoint path := by
  intro disjoint
  exact disjoint.1 path.prefix_refl

theorem AccessPath.disjoint_symm {left right : AccessPath} (disjoint : left.Disjoint right) :
    right.Disjoint left := ⟨disjoint.2, disjoint.1⟩

theorem AccessPath.distinct_variables_disjoint
    (different : x ≠ y) (left right : List Projection) :
    (AccessPath.path x left).Disjoint (.path y right) := by
  simp [Disjoint, IsPrefix, different, Ne.symm different]

theorem AccessPath.distinct_fields_disjoint
    (different : first ≠ second) (root : VariableId)
    (common left right : List Projection) :
    (AccessPath.path root (common ++ .field first :: left)).Disjoint
      (.path root (common ++ .field second :: right)) := by
  simp [Disjoint, IsPrefix, different, Ne.symm different]

theorem AccessPath.distinct_indices_disjoint
    (different : first ≠ second) (root : VariableId)
    (common left right : List Projection) :
    (AccessPath.path root (common ++ .index first :: left)).Disjoint
      (.path root (common ++ .index second :: right)) := by
  simp [Disjoint, IsPrefix, different, Ne.symm different]

inductive AccessKind where
  | give
  | share
  | lease
  | drop
  deriving DecidableEq

inductive Lien where
  | shared (support : AccessPath)
  | unique (support : AccessPath)

def Lien.permits (lien : Lien) (kind : AccessKind) (accessed : AccessPath) : Prop :=
  match lien, kind with
  | .shared support, .give | .unique support, .give =>
      accessed.Disjoint support ∨ accessed.IsPrefix support
  | .shared _, .share => True
  | .unique support, .share
  | .shared support, .lease | .unique support, .lease
  | .shared support, .drop | .unique support, .drop =>
      accessed.Disjoint support

-- This predicate checks every supplied live-after lien; it neither creates nor
-- invalidates references and is deliberately independent of PathStep.
def LiveLiensPermit (liens : List Lien) (kind : AccessKind) (accessed : AccessPath) : Prop :=
  ∀ lien ∈ liens, lien.permits kind accessed

variable {accessed support : AccessPath} {liens remaining original : List Lien}
variable {kind : AccessKind}

theorem Lien.prefix_give_permitted (isPrefix : accessed.IsPrefix support) :
    (Lien.shared support).permits .give accessed ∧
      (Lien.unique support).permits .give accessed :=
  ⟨Or.inr isPrefix, Or.inr isPrefix⟩

theorem Lien.shared_share_permitted (support accessed : AccessPath) :
    (Lien.shared support).permits .share accessed := True.intro

theorem Lien.disjoint_permitted (disjoint : accessed.Disjoint support)
    (kind : AccessKind) :
    (Lien.shared support).permits kind accessed ∧
      (Lien.unique support).permits kind accessed := by
  cases kind with
  | give => exact ⟨Or.inl disjoint, Or.inl disjoint⟩
  | share => exact ⟨True.intro, disjoint⟩
  | lease => exact ⟨disjoint, disjoint⟩
  | drop => exact ⟨disjoint, disjoint⟩

theorem Lien.unique_conflict (conflict : ¬ accessed.Disjoint support) :
    ¬ (Lien.unique support).permits .share accessed ∧
    ¬ (Lien.unique support).permits .lease accessed ∧
    ¬ (Lien.unique support).permits .drop accessed :=
  ⟨conflict, conflict, conflict⟩

theorem live_unique_blocks_conflicts
    (live : Lien.unique support ∈ liens) (conflict : ¬ accessed.Disjoint support) :
    ¬ LiveLiensPermit liens .share accessed ∧
    ¬ LiveLiensPermit liens .lease accessed ∧
    ¬ LiveLiensPermit liens .drop accessed := by
  exact ⟨fun permitted => conflict (permitted _ live),
    fun permitted => conflict (permitted _ live),
    fun permitted => conflict (permitted _ live)⟩

theorem fewer_live_liens_permit
    (subset : ∀ lien ∈ remaining, lien ∈ original)
    (permitted : LiveLiensPermit original kind accessed) :
    LiveLiensPermit remaining kind accessed := by
  intro lien live
  exact permitted lien (subset lien live)

-- ANCHOR: give_prefix_of_live_borrows
example :
    let root : AccessPath := .path ⟨0⟩ []
    let field : AccessPath := .path ⟨0⟩ [.field "item"]
    LiveLiensPermit [.unique field, .shared field] .give root := by
  simp [LiveLiensPermit, Lien.permits, AccessPath.IsPrefix]
-- ANCHOR_END: give_prefix_of_live_borrows

-- ANCHOR: live_unique_conflict
example :
    let path : AccessPath := .path ⟨0⟩ [.field "item"]
    ¬ LiveLiensPermit [.unique path] .share path ∧
    ¬ LiveLiensPermit [.unique path] .lease path ∧
    ¬ LiveLiensPermit [.unique path] .drop path := by
  exact live_unique_blocks_conflicts (by simp) (AccessPath.not_disjoint_self _)
-- ANCHOR_END: live_unique_conflict

-- ANCHOR: disjoint_siblings_permit
example (kind : AccessKind) :
    let left : AccessPath := .path ⟨0⟩ [.field "left"]
    let right : AccessPath := .path ⟨0⟩ [.field "right"]
    LiveLiensPermit [.unique right, .shared right] kind left := by
  intro left right lien live
  have disjoint : left.Disjoint right :=
    AccessPath.distinct_fields_disjoint (by decide) ⟨0⟩ [] [] []
  simp only [List.mem_cons, List.not_mem_nil, or_false] at live
  rcases live with rfl | rfl
  · exact (Lien.disjoint_permitted disjoint kind).2
  · exact (Lien.disjoint_permitted disjoint kind).1
-- ANCHOR_END: disjoint_siblings_permit

-- ANCHOR: shared_lien_allows_only_shared_overlap
example :
    let path : AccessPath := .path ⟨0⟩ []
    LiveLiensPermit [.shared path] .share path ∧
    ¬ LiveLiensPermit [.shared path] .lease path ∧
    ¬ LiveLiensPermit [.shared path] .drop path := by
  simp [LiveLiensPermit, Lien.permits, AccessPath.Disjoint, AccessPath.IsPrefix]
-- ANCHOR_END: shared_lien_allows_only_shared_overlap

end Dada.Heap
