import Assignment.StoreViews
import Assignment.WriteEffects

namespace Dada.Assignment
open Shared Shared.Typing

theorem fieldsMatchClasses_write_variable
    (fields : FieldsMatchClasses classes before)
    (written : Write before (.variable name) incoming after) :
    FieldsMatchClasses classes after := by
  cases written
  exact fields

theorem fieldsMatchClasses_write_field
    {classes : ClassTable} {before after : State} {pending : List Reference}
    {parent : ObjectId} {name : FieldName} {incoming : Reference}
    {parentType incomingType : ValueType} {declaration : TypedClass} {fieldType : FieldType}
    (wf : WellFormedWith classes.erase before pending)
    (fields : FieldsMatchClasses classes before)
    (written : Write before (.field parent name) incoming after)
    (parentSatisfied : Satisfies classes before (.owned parent) parentType)
    (incomingSatisfied : Satisfies classes before incoming incomingType)
    (declared : classes.lookup parentType.base = some declaration)
    (fieldDeclared : declaration.fields.lookup name = some fieldType)
    (sameType : storageType incomingType = fieldType) :
    FieldsMatchClasses classes after := by
  have transfer : ∀ object data field child, (object, data) ∈ before.objects →
      (field, some child) ∈ data.fields →
      ∃ decl type childData,
        (data.className, decl) ∈ classes ∧ (field, type) ∈ decl.fields ∧
        (child.object, childData) ∈ after.objects ∧ childData.className = type.className := by
    intro object data field child stored fieldStored
    obtain ⟨decl, type, childData, declMember, fieldMember, childMember, same⟩ :=
      fields object data field child stored fieldStored
    obtain ⟨newData, newMember, newClass⟩ := written.old_object_data _ _ childMember
    exact ⟨decl, type, newData, declMember, fieldMember, newMember, newClass.trans same⟩
  obtain ⟨parentData, parentStored, parentNamed⟩ := parentSatisfied.root
  obtain ⟨incomingData, incomingStored, incomingNamed⟩ := incomingSatisfied.root
  obtain ⟨newIncomingData, newIncomingStored, sameIncoming⟩ :=
    written.old_object_data _ _ incomingStored
  have correctIncoming : newIncomingData.className = fieldType.className := by
    have sameClass := congrArg FieldType.className sameType
    exact sameIncoming.trans (incomingNamed.trans sameClass)
  cases written with
  | field variables nextId leading trailing parent className beforeFields afterFields name previous incoming =>
    have actualParent : (parent, (⟨className, beforeFields ++ (name, previous) :: afterFields⟩ : Object)) ∈
        (leading ++ (parent, ⟨className, beforeFields ++ (name, previous) :: afterFields⟩) :: trailing) := by simp
    have parentEq := member_value_unique wf.objectKeys parentStored actualParent
    have sameParent : className = parentType.base := by simpa only [parentEq, ValueType.base] using parentNamed
    have declaredMember : (className, declaration) ∈ classes := sameParent ▸ lookup_member declared
    intro object data field child stored fieldStored
    simp only [List.mem_append, List.mem_cons] at stored
    rcases stored with earlier | same | later
    · exact transfer object data field child (List.mem_append_left _ earlier) fieldStored
    · cases same
      simp only [List.mem_append, List.mem_cons] at fieldStored
      rcases fieldStored with earlier | same | later
      · exact transfer parent ⟨className, beforeFields ++ (name, previous) :: afterFields⟩ field child actualParent (List.mem_append_left _ earlier)
      · cases same
        exact ⟨declaration, fieldType, newIncomingData, declaredMember, lookup_member fieldDeclared,
          newIncomingStored, correctIncoming⟩
      · exact transfer parent ⟨className, beforeFields ++ (name, previous) :: afterFields⟩ field child actualParent (List.mem_append_right _ (List.mem_cons_of_mem _ later))
    · exact transfer object data field child (List.mem_append_right _ (List.mem_cons_of_mem _ later)) fieldStored

end Dada.Assignment
