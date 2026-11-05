import Assignment.StoreProgress

namespace Dada.Assignment
open Shared Shared.Typing

-- The displaced struct needs a type while it is a temporary GC root. Its
-- nominal identity and permission suffice; none of its fields remain visible.
private def garbageType (field : FieldType) (declaration : TypedClass) : ValueType :=
  ⟨field.permission,
    if declaration.fields.isEmpty then .whole field.className else ⟨field.className, []⟩⟩

private theorem garbageType_permission (field : FieldType) (declaration : TypedClass) :
    (garbageType field declaration).permission = field.permission := rfl

private theorem garbageType_base (field : FieldType) (declaration : TypedClass) :
    (garbageType field declaration).base = field.className := by
  unfold garbageType ValueType.base
  split <;> rfl

private theorem garbageType_admissible
    (declared : classes.lookup field.className = some declaration)
    (kind : KindValid classes field.toType) :
    Admissible classes (garbageType field declaration) := by
  have nominalDeclared := ClassTable.nominal_lookup classes field.className
  rw [declared] at nominalDeclared
  simp only [Option.map_some] at nominalDeclared
  constructor
  · constructor
    · unfold garbageType
      split <;> simp [Unique.Typing.ViewType.WellFormed,
        Unique.Typing.ViewType.whole, Unique.Typing.Entry.valid,
        Unique.Typing.Entry.path, Unique.Typing.classAt,
        Unique.Typing.entriesDisjoint, nominalDeclared]
    · unfold KindValid
      rw [garbageType_base, garbageType_permission]
      exact kind
  · unfold Normalized Unique.Typing.Normalized garbageType
    split
    · exact Unique.Typing.normalize_whole _ _
    next nonempty =>
      cases fieldsEq : declaration.fields with
      | nil => simp [fieldsEq] at nonempty
      | cons first rest =>
        have flatEmpty (values : List (FieldName × ClassName)) :
            values.flatMap (fun _ => ([] : List Entry)) = [] :=
          List.flatMap_eq_nil_iff.mpr (by simp)
        simp [Unique.Typing.normalize, Unique.Typing.normalizeEntries,
          nominalDeclared, flatEmpty, fieldsEq]

private theorem garbageType_positive
    (declared : classes.lookup field.className = some declaration)
    (positive : Pos classes (garbageType field declaration) path) : path = [] := by
  unfold Pos Unique.Typing.Pos Unique.Typing.positive garbageType at positive
  split at positive
  next empty =>
    have empty := List.isEmpty_iff.mp empty
    cases path with
    | nil => rfl
    | cons name rest =>
      simp [Unique.Typing.ViewType.whole, Unique.Typing.classAt,
        ClassTable.nominal_lookup, declared, empty] at positive
  next =>
    simpa using (Bool.and_eq_true_iff.mp positive).2

private theorem garbageType_negative
    (negative : Shared.Typing.Neg (garbageType field declaration) path) : False := by
  unfold Shared.Typing.Neg Unique.Typing.Neg Unique.Typing.negative garbageType at negative
  split at negative <;> simp [Unique.Typing.ViewType.whole] at negative

theorem field_garbage_type
    (realized : Realizes classes environment state pending)
    (satisfied : Satisfies classes state (.owned parent) parentTy)
    (dataStored : (parent, data) ∈ state.objects)
    (fieldStored : (name, some previous) ∈ data.fields)
    (declared : classes.lookup parentTy.base = some declaration)
    (fieldDeclared : declaration.fields.lookup name = some fieldType)
    (replaceable : Replaceable classes.erase state (some previous)) :
    ∃ previousTy, Admissible classes previousTy ∧ StructType classes previousTy ∧
      Satisfies classes state previous previousTy := by
  obtain ⟨rootData, rootStored, rootClass⟩ := satisfied.root
  have sameData : rootData = data :=
    member_value_unique realized.ownership.objectKeys rootStored dataStored
  subst rootData
  change data.className = parentTy.base at rootClass
  obtain ⟨actualDeclaration, actualField, childData, actualDeclared, actualFieldDeclared,
    childStored, childClass⟩ := realized.fields _ _ _ _ dataStored fieldStored
  have sameDeclaration : actualDeclaration = declaration :=
    member_value_unique realized.classesWellFormed.1
      (rootClass ▸ actualDeclared) (lookup_member declared)
  subst actualDeclaration
  have sameField : actualField = fieldType :=
    member_value_unique (realized.classesWellFormed.2 _ (lookup_member declared)).1
      actualFieldDeclared (lookup_member fieldDeclared)
  subst actualField
  have fieldWellFormed := (realized.classesWellFormed.2 _ (lookup_member declared)).2
    _ (lookup_member fieldDeclared)
  obtain ⟨⟨childName, childDeclaration⟩, childDeclared, childNameEq⟩ :=
    List.mem_map.mp fieldWellFormed.1
  dsimp at childNameEq
  subst childName
  have childLookup := lookup_of_member realized.classesWellFormed.1 childDeclared
  have childType := garbageType_admissible childLookup fieldWellFormed.2.1
  have parentGiven : parentTy.permission = .given := by
    have mode := satisfied.mode
    cases permEq : parentTy.permission <;> simp_all [Perm.toMode, Reference.owned]
  have read : readPath state (.owned parent) [name] = some (some previous) := by
    have dataLookup := lookup_of_member realized.ownership.objectKeys dataStored
    obtain ⟨_, _, shape, fieldsDistinct⟩ := realized.ownership.shapes _ _ dataStored
    have fieldLookup := lookup_of_member (shape ▸ fieldsDistinct) fieldStored
    simp [readPath, dataLookup, fieldLookup, Reference.owned]
  have fieldPermission : declaredPermission classes parentTy.base [name] =
      some fieldType.permission := by
    simp [declaredPermission, declared, fieldDeclared, Perm.comp_given_right]
  have childMode : previous.mode = fieldType.permission.toMode := by
    simpa [parentGiven, Perm.comp_given_left] using
      satisfied.modes [name] previous fieldType.permission fieldPermission read
  refine ⟨garbageType fieldType childDeclaration, childType, ?_, ?_⟩
  · obtain ⟨structData, structDeclaration, structStored, structDeclared, structKind⟩ := replaceable
    have sameStructData : structData = childData :=
      member_value_unique realized.ownership.objectKeys structStored childStored
    subst structData
    have erasedDeclared : (childData.className,
        ⟨childDeclaration.fields.map Prod.fst, childDeclaration.kind⟩) ∈ classes.erase :=
      List.mem_map.mpr ⟨(fieldType.className, childDeclaration), childDeclared,
        by simp [childClass]⟩
    have sameStructDeclaration : structDeclaration =
        ⟨childDeclaration.fields.map Prod.fst, childDeclaration.kind⟩ :=
      member_value_unique realized.classesWellFormed.erase.1 structDeclared erasedDeclared
    unfold StructType
    rw [garbageType_base, childLookup]
    simpa [sameStructDeclaration] using structKind
  · constructor
    · exact childMode
    · refine ⟨childData, childStored, ?_⟩
      change childData.className = (garbageType fieldType childDeclaration).base
      rw [garbageType_base]
      exact childClass
    · intro path positive
      have empty := garbageType_positive childLookup positive
      subst path
      refine ⟨previous, childData, ?_, childStored, ?_⟩
      · simp [readPath, lookup_of_member realized.ownership.objectKeys childStored]
      · change some (garbageType fieldType childDeclaration).base = some childData.className
        rw [garbageType_base, childClass]
    · intro path negative
      exact False.elim (garbageType_negative negative)
    · intro path target permission permissionDeclared tailRead
      have completeDeclared : declaredPermission classes parentTy.base ([name] ++ path) =
          some (fieldType.permission.comp permission) := by
        change declaredPermission classes (garbageType fieldType childDeclaration).base path =
          some permission at permissionDeclared
        rw [garbageType_base] at permissionDeclared
        simp [declaredPermission, declared, fieldDeclared, permissionDeclared]
      have completeRead := (readPath_append realized.ownership read path).trans tailRead
      simpa [parentGiven, Perm.comp_given_left, garbageType_permission] using
        satisfied.modes ([name] ++ path) target _ completeDeclared completeRead

end Dada.Assignment
