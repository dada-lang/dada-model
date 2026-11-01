import Shared.Examples
import Unique.Examples
import Unique.Soundness
import Correspondence.UniqueShared
import PathExamples
import WellFormed

-- These independent probes characterize adversarial boundary cases. They do not
-- add to the repository formalization or to its saved correspondence evidence.
namespace Dada.Adversarial

example : Shared.Capture [("s", some (.shared 0))] ["s", "s"]
    [.shared 0, .shared 0] [("s", some (.shared 0))] :=
  .shared [] [] "s" 0 (.shared [] [] "s" 0 (.nil _))

-- The raw relation intentionally accepts malformed class tables, and such
-- tables can be nondeterministic. Published preservation excludes these tables.
def ambiguousClasses : Unique.Classes := [("C", ⟨["left"]⟩), ("C", ⟨["right"]⟩)]
def initialToken : Unique.State := ⟨[(0, ⟨"Token", []⟩)], [("t", some 0)], 1⟩
def withField (field : String) : Unique.State :=
  initialToken.create [("t", none)] "c" "C" [field] [0]

example : ¬ Unique.ClassesWellFormed ambiguousClasses := by
  simp [Unique.ClassesWellFormed, ambiguousClasses]

example : Unique.Step ambiguousClasses
    ⟨initialToken, [⟨"c", .new "C" ["t"]⟩]⟩ ⟨withField "left", []⟩ := by
  apply Unique.Step.new (declaration := ⟨["left"]⟩) (objects := [0])
    (remaining := [("t", none)])
  · simp [initialToken]
  · simp [ambiguousClasses]
  · exact .cons [] [] "t" 0 (.nil _)
  · rfl

example : Unique.Step ambiguousClasses
    ⟨initialToken, [⟨"c", .new "C" ["t"]⟩]⟩ ⟨withField "right", []⟩ := by
  apply Unique.Step.new (declaration := ⟨["right"]⟩) (objects := [0])
    (remaining := [("t", none)])
  · simp [initialToken]
  · simp [ambiguousClasses]
  · exact .cons [] [] "t" 0 (.nil _)
  · rfl

example : withField "left" ≠ withField "right" := by decide

end Dada.Adversarial

namespace Dada.Heap.Adversarial

-- Two borrows of the same owner are separate roots, not ancestor/descendant.
def siblingRoots : LeaseStore :=
  .store { entries := [(⟨1⟩, .entry (.root ⟨10⟩) true),
                       (⟨0⟩, .entry (.root ⟨10⟩) true)]
           uniqueKeys := by decide } 2

def siblingState : State Nat :=
  .state borrowStart.objects
    { entries := [(⟨2⟩, .initialized (.borrow .shared ⟨1⟩ ⟨10⟩)),
                  (⟨1⟩, .initialized (.borrow .unique ⟨0⟩ ⟨10⟩)),
                  (⟨0⟩, .initialized (.owned ⟨10⟩))]
      uniqueKeys := by decide }
    siblingRoots

example : MachineStep borrowRootState (.borrow ⟨0⟩ .shared ⟨2⟩) siblingState := by
  apply MachineStep.borrow
  refine BorrowReference.borrow (reference := .owned ⟨10⟩) (id := ⟨1⟩)
    (leases := siblingRoots) ?_ ?_ ?_ ?_ ?_ ?_
  · simp [ReferenceAt, Stored, borrowRootState]
  · exact ResolveReference.owner .unique
      (by simp [AllocatedObject, borrowRootState, borrowStart])
  · intro impossible
    cases impossible
  · exact .allocate borrowRootStore borrowRootStore_wellFormed (.root ⟨10⟩) trivial
  · simp [Stored, borrowRootState]
  · rfl

theorem no_sibling_parents (child parent : LeaseId) :
    ¬ LeaseParent siblingRoots child parent := by
  intro h
  cases h with
  | parent stored member =>
    simp [siblingRoots] at stored
    rcases stored with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [LeaseNode.parents] at member

theorem no_sibling_ancestors (child parent : LeaseId) :
    ¬ LeaseAncestor siblingRoots child parent := by
  intro h
  induction h with
  | parent edge => exact no_sibling_parents _ _ edge
  | trans _ _ impossible _ => exact impossible

noncomputable def siblingAfterWrite : State Nat :=
  .state siblingState.objects siblingState.variables (invalidateLease siblingRoots ⟨0⟩)

example : MachineStep siblingState (.invalidateForWrite ⟨1⟩) siblingAfterWrite := by
  refine .invalidateForWrite (reference := .borrow .unique ⟨0⟩ ⟨10⟩) ?_ ?_ ?_
  · simp [ReferenceAt, Stored, siblingState]
  · exact ResolveReference.borrow .unique
      (by simp [AllocatedObject, siblingState, borrowStart])
      ⟨.entry (.root ⟨10⟩) true, by simp [siblingState, siblingRoots], rfl⟩
  · exact .borrowed _ _ _
      ⟨.entry (.root ⟨10⟩) true, by simp [siblingState, siblingRoots], rfl⟩

example : ResolveReference siblingAfterWrite (.borrow .shared ⟨1⟩ ⟨10⟩) ⟨10⟩ .shared := by
  apply ResolveReference.borrow
  · simp [AllocatedObject, siblingAfterWrite, siblingState, borrowStart]
  · apply LeaseStore.not_revoked_usable
    · exact ⟨.entry (.root ⟨10⟩) true, by simp [siblingRoots], rfl⟩
    · exact no_sibling_ancestors _ _

end Dada.Heap.Adversarial
