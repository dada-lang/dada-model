import Destructors.Checks

namespace Dada.Destructors.Checks
open Shared Shared.Typing

-- These are operational checks, in addition to the static give-effect checks.
def uniquePoint : Configuration := .running
  ⟨[(0,⟨"Point",[]⟩)],[("p",some (.owned 0))],1⟩
  ⟨[.dropStruct (.variable "p")],none⟩

def copiedPoint : Configuration := .running
  ⟨[(0,⟨"SharedPoint",[]⟩)],[("s",some (.shared 0))],1⟩
  ⟨[.dropStruct (.variable "s")],none⟩

-- ANCHOR: struct_runtime
example :
    Step classes.erase declarations uniquePoint
      (.running ⟨[],[("p",none)],1⟩ ⟨[],none⟩) ∧
    Step classes.erase declarations copiedPoint
      (.running ⟨[(0,⟨"SharedPoint",[]⟩)],[("s",some (.shared 0))],1⟩ ⟨[],none⟩) := by
  constructor
  · let raw : Configuration := .running ⟨[(0,⟨"Point",[]⟩)],[("p",none)],1⟩ ⟨[],none⟩
    have noLive (id : ObjectId) : ¬ Live raw.rootState id := by
      intro live
      obtain ⟨name,reference,member⟩ := live_has_root live
      simp [raw,Configuration.rootState,Configuration.running] at member
    have collected : raw.collect = .running ⟨[],[("p",none)],1⟩ ⟨[],none⟩ := by
      simp only [Configuration.collect,State.collect]
      simp only [noLive,decide_false]
      rfl
    rw [← collected]
    apply Step.collect
    apply RawStep.dropStruct (reference := .owned 0)
    · exact .give (.move (source := .variable "p")
        (.variable (reference := .owned 0) (by simp))
        (.variable [(0,⟨"Point",[]⟩)] 1 [] [] "p" 0))
    · exact ⟨⟨"Point",[]⟩,⟨[],.structType⟩,by simp [Reference.owned],by decide,rfl⟩
  · let after : Configuration := .running
      ⟨[(0,⟨"SharedPoint",[]⟩)],[("s",some (.shared 0))],1⟩ ⟨[],none⟩
    have collected : after.collect = after := by
      apply Configuration.collect_eq_self
      intro id data member
      have eq : (id,data) = (0,⟨"SharedPoint",[]⟩) := List.mem_singleton.mp member
      cases eq
      exact .variable (name := "s") (reference := .shared 0) (by simp [after,Configuration.rootState,Configuration.running])
    change Step classes.erase declarations copiedPoint after
    rw [← collected]
    apply Step.collect
    apply RawStep.dropStruct (reference := .shared 0)
    · exact .give (.copy (source := .variable "s")
        (.variable (reference := .shared 0) (by simp)) (by simp [Stored]))
    · exact ⟨⟨"SharedPoint",[]⟩,⟨[],.sharedStruct⟩,by simp [Reference.shared],by decide,rfl⟩
-- ANCHOR_END: struct_runtime

-- ANCHOR: class_exit_rejected
example : ¬ StoreFinished classes.erase
    ⟨[(0,⟨"Resource",[]⟩)],[("self",some (.owned 0))],1⟩ := by
  intro finished
  have impossible := finished "self" (.owned 0) (by simp)
  simp [StructReference,classes,ClassTable.erase,Reference.owned,Kind.isStruct] at impossible
-- ANCHOR_END: class_exit_rejected

-- ANCHOR: struct_destructor_rejected
example :
    ¬ Signature.WellFormed classes (.destructor "Point") ⟨[receiver "Point" .given],none⟩ ∧
    ¬ Signature.WellFormed classes (.destructor "SharedPoint") ⟨[receiver "SharedPoint" .shared],none⟩ := by
  constructor
  all_goals
    intro h
    obtain ⟨_,_,_,_,decl,member,kind⟩ := h
    simp [classes] at member
    subst decl
    cases kind
-- ANCHOR_END: struct_destructor_rejected

end Dada.Destructors.Checks
