import Shared.TypingViews
import Unique.ViewSoundness

namespace Dada.Shared.Typing

private theorem lookup_map_value {Key Value Result : Type} [BEq Key]
    (entries : List (Key × Value)) (key : Key) (f : Value → Result) :
    (entries.map (fun entry => (entry.1, f entry.2))).lookup key =
      (entries.lookup key).map f := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨entryKey, entryValue⟩
    by_cases same : key == entryKey
    · simp [List.lookup_cons, same]
    · simpa [List.lookup_cons, same] using ih

theorem ClassTable.nominal_lookup (classes : ClassTable) (name : ClassName) :
    classes.nominal.lookup name = (classes.lookup name).map (fun declaration =>
      (⟨declaration.fields.map (fun entry => (entry.1, entry.2.className))⟩ :
        Unique.Typing.TypedClass)) := by
  simpa [ClassTable.nominal] using lookup_map_value classes name
    (fun declaration => (⟨declaration.fields.map (fun entry => (entry.1, entry.2.className))⟩ :
      Unique.Typing.TypedClass))

theorem nominal_field_lookup (fields : List (FieldName × FieldType)) (name : FieldName) :
    (fields.map (fun entry => (entry.1, entry.2.className))).lookup name =
      (fields.lookup name).map FieldType.className :=
  lookup_map_value fields name _

theorem declaredPermission_valid (classes : ClassTable) (name : ClassName) (path : Path) :
    (declaredPermission classes name path).isSome =
      (Unique.Typing.classAt classes.nominal name path).isSome := by
  induction path generalizing name with
  | nil => rfl
  | cons field rest ih =>
    cases classFound : classes.lookup name with
    | none => simp [declaredPermission, Unique.Typing.classAt, ClassTable.nominal_lookup, classFound]
    | some declaration =>
      cases fieldFound : declaration.fields.lookup field with
      | none => simp [declaredPermission, Unique.Typing.classAt, ClassTable.nominal_lookup,
          nominal_field_lookup, classFound, fieldFound]
      | some fieldType =>
        have restValid := ih fieldType.className
        cases declared : declaredPermission classes fieldType.className rest <;>
          simpa [declaredPermission, Unique.Typing.classAt, ClassTable.nominal_lookup,
            nominal_field_lookup, classFound, fieldFound, declared] using restValid

theorem declaredPermission_append {classes : ClassTable} {name target : ClassName}
    {initialPath : Path} (atClass : Unique.Typing.classAt classes.nominal name initialPath = some target)
    (suffix : Path) :
    declaredPermission classes name (initialPath ++ suffix) = do
      let first ← declaredPermission classes name initialPath
      let second ← declaredPermission classes target suffix
      return first.comp second := by
  induction initialPath generalizing name with
  | nil =>
    have same : name = target := Option.some.inj atClass
    subst name
    simp [declaredPermission, Perm.comp_given_left]
  | cons field rest ih =>
    cases classFound : classes.lookup name with
    | none => simp [Unique.Typing.classAt, ClassTable.nominal_lookup, classFound] at atClass
    | some declaration =>
      cases fieldFound : declaration.fields.lookup field with
      | none => simp [Unique.Typing.classAt, ClassTable.nominal_lookup,
          nominal_field_lookup, classFound, fieldFound] at atClass
      | some fieldType =>
        have tailClass : Unique.Typing.classAt classes.nominal fieldType.className rest =
            some target := by
          simpa [Unique.Typing.classAt, ClassTable.nominal_lookup, nominal_field_lookup,
            classFound, fieldFound] using atClass
        simp only [List.cons_append, declaredPermission, classFound, fieldFound,
          Bind.bind, Option.bind]
        rw [ih tailClass]
        cases declaredPermission classes fieldType.className rest <;>
          cases declaredPermission classes target suffix <;> simp [Perm.comp_assoc]

theorem focus_observations {classes : ClassTable} (wf : classes.WellFormed)
    (normal : Normalized classes ty) (focused : focus classes ty path = some result) :
    Unique.Typing.FocusObservations classes.nominal ty.nominal path result.nominal := by
  obtain ⟨nominal, permission, nominalFocus, _, resultEq⟩ := focus_eq_some_iff.mp focused
  subst result
  exact Unique.Typing.focus_observations wf.nominal normal nominalFocus

theorem focus_permission (focused : focus classes ty path = some result) :
    ∃ permission, declaredPermission classes ty.base path = some permission ∧
      result.permission = ty.permission.comp permission := by
  obtain ⟨nominal, permission, _, declared, resultEq⟩ := focus_eq_some_iff.mp focused
  exact ⟨permission, declared, congrArg ValueType.permission resultEq⟩

theorem focus_nominal (focused : focus classes ty path = some result) :
    Unique.Typing.focus classes.nominal ty.nominal path = some result.nominal := by
  obtain ⟨nominal, permission, nominalFocus, _, resultEq⟩ := focus_eq_some_iff.mp focused
  subst result
  exact nominalFocus

theorem focus_given (focused : focus classes ty path = some result)
    (given : result.permission = .given) : ty.permission = .given := by
  obtain ⟨permission, _, same⟩ := focus_permission focused
  exact (Perm.comp_eq_given_iff _ _).mp (same.symm.trans given) |>.1

theorem emptyPath_permission (emptied : emptyPath classes ty path = some result) :
    result.permission = ty.permission := by
  obtain ⟨nominal, _, same⟩ := Option.map_eq_some_iff.mp emptied
  exact (congrArg ValueType.permission same).symm

theorem emptyPath_nominal (emptied : emptyPath classes ty path = some result) :
    Unique.Typing.emptyPath classes.nominal ty.nominal path = some result.nominal := by
  obtain ⟨nominal, nominalEmpty, same⟩ := Option.map_eq_some_iff.mp emptied
  cases same
  exact nominalEmpty

end Dada.Shared.Typing
