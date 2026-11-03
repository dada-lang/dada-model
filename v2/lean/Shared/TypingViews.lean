import Unique.Views
import Shared.State

namespace Dada.Shared.Typing

inductive Perm where
  | given
  | shared
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def Perm.comp : Perm → Perm → Perm
  | .given, .given => .given
  | _, _ => .shared

def Perm.toMode : Perm → Mode
  | .given => .unique
  | .shared => .shared

abbrev Path := Unique.Typing.Path
abbrev Entry := Unique.Typing.Entry
abbrev Nominal := Unique.Typing.ViewType

-- The static judgments use normalized outer permissions. RawType below retains
-- the surface grammar with arbitrarily nested permission applications.
structure ValueType where
  permission : Perm
  nominal : Nominal
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def ValueType.whole (name : ClassName) (permission : Perm := .given) : ValueType :=
  ⟨permission, .whole name⟩

def ValueType.shared (ty : ValueType) : ValueType :=
  { ty with permission := .shared }

def ValueType.perm (ty : ValueType) : Perm := ty.permission

def ValueType.base (ty : ValueType) : ClassName := ty.nominal.className

structure FieldType where
  permission : Perm
  className : ClassName
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def FieldType.toType (field : FieldType) : ValueType :=
  .whole field.className field.permission

structure TypedClass where
  fields : List (FieldName × FieldType)
  kind : Kind := .structType
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

abbrev ClassTable := List (ClassName × TypedClass)

def ClassTable.nominal (classes : ClassTable) : Unique.Typing.ClassTable :=
  classes.map fun (name, declaration) =>
    (name, ⟨declaration.fields.map fun (field, ty) => (field, ty.className)⟩)

def ClassTable.erase (classes : ClassTable) : Classes :=
  classes.map fun (name, declaration) => (name, ⟨declaration.fields.map Prod.fst, declaration.kind⟩)

def StructType (classes : ClassTable) (ty : ValueType) : Prop :=
  (classes.lookup ty.base).any (fun declaration => declaration.kind.isStruct) = true

instance (classes : ClassTable) (ty : ValueType) : Decidable (StructType classes ty) :=
  inferInstanceAs (Decidable (_ = true))

def initialPermission : Kind → Perm
  | .sharedStruct => .shared
  | _ => .given

def kindAllows (kind : Kind) (permission : Perm) : Bool :=
  match kind with
  | .classType => permission == .given
  | .structType => true
  | .sharedStruct => permission == .shared

def KindValid (classes : ClassTable) (ty : ValueType) : Prop :=
  (classes.lookup ty.base).any (fun declaration => kindAllows declaration.kind ty.permission) = true

instance (classes : ClassTable) (ty : ValueType) : Decidable (KindValid classes ty) :=
  inferInstanceAs (Decidable (_ = true))

def ClassTable.WellFormed (classes : ClassTable) : Prop :=
  (classes.map Prod.fst).Nodup ∧
    ∀ entry ∈ classes, (entry.2.fields.map Prod.fst).Nodup ∧
      ∀ field ∈ entry.2.fields, field.2.className ∈ classes.map Prod.fst ∧
        KindValid classes field.2.toType ∧
        (entry.2.kind.isStruct = true → StructType classes field.2.toType)

instance (classes : ClassTable) : Decidable classes.WellFormed := by
  unfold ClassTable.WellFormed
  infer_instance

inductive RawType where
  | nominal (view : Nominal)
  | apply (permission : Perm) (inner : RawType)
  deriving DecidableEq, Repr

def normalize (classes : ClassTable) (ty : ValueType) : ValueType :=
  { ty with nominal := Unique.Typing.normalize classes.nominal ty.nominal }

def RawType.normalize (classes : ClassTable) : RawType → ValueType
  | .nominal view =>
      ⟨initialPermission ((classes.lookup view.className).map TypedClass.kind |>.getD .classType),
        Unique.Typing.normalize classes.nominal view⟩
  | .apply permission inner =>
      let result := inner.normalize classes
      { result with permission := permission.comp result.permission }

def ValueType.WellFormed (ty : ValueType) (classes : ClassTable) : Prop :=
  ty.nominal.WellFormed classes.nominal ∧ KindValid classes ty

def Normalized (classes : ClassTable) (ty : ValueType) : Prop :=
  Unique.Typing.Normalized classes.nominal ty.nominal

def Admissible (classes : ClassTable) (ty : ValueType) : Prop :=
  ty.WellFormed classes ∧ Normalized classes ty

instance (ty : ValueType) (classes : ClassTable) : Decidable (ty.WellFormed classes) := by
  unfold ValueType.WellFormed
  infer_instance

instance (classes : ClassTable) (ty : ValueType) : Decidable (Normalized classes ty) :=
  inferInstanceAs (Decidable (Unique.Typing.Normalized classes.nominal ty.nominal))

instance (classes : ClassTable) (ty : ValueType) : Decidable (Admissible classes ty) := by
  unfold Admissible
  infer_instance

theorem StructType.declaration (structTy : StructType classes ty) :
    ∃ declaration, classes.lookup ty.base = some declaration ∧ declaration.kind.isStruct = true := by
  unfold StructType at structTy
  cases found : classes.lookup ty.base with
  | none => simp [found] at structTy
  | some declaration => exact ⟨declaration, rfl, by simpa [found] using structTy⟩

theorem Admissible.share (admissible : Admissible classes ty)
    (structTy : StructType classes ty) : Admissible classes ty.shared := by
  obtain ⟨declaration, found, kind⟩ := structTy.declaration
  refine ⟨⟨admissible.1.1, ?_⟩, admissible.2⟩
  unfold KindValid
  change (classes.lookup ty.base).any _ = true
  rw [found]
  cases kindEq : declaration.kind <;> simp_all [kindAllows, Kind.isStruct, ValueType.shared]

def Pos (classes : ClassTable) (ty : ValueType) (path : Path) : Prop :=
  Unique.Typing.Pos classes.nominal ty.nominal path

def Neg (ty : ValueType) (path : Path) : Prop :=
  Unique.Typing.Neg ty.nominal path

def declaredPermission (classes : ClassTable) (name : ClassName) : Path → Option Perm
  | [] => some .given
  | field :: rest => do
      let declaration ← classes.lookup name
      let target ← declaration.fields.lookup field
      let permission ← declaredPermission classes target.className rest
      return target.permission.comp permission

def focus (classes : ClassTable) (ty : ValueType) (path : Path) : Option ValueType := do
  let nominal ← Unique.Typing.focus classes.nominal ty.nominal path
  let permission ← declaredPermission classes ty.base path
  return ⟨ty.permission.comp permission, nominal⟩

def emptyPath (classes : ClassTable) (ty : ValueType) (path : Path) : Option ValueType :=
  (Unique.Typing.emptyPath classes.nominal ty.nominal path).map fun remaining =>
    ⟨ty.permission, remaining⟩

def Subtype (classes : ClassTable) (source target : ValueType) : Prop :=
  source.permission = target.permission ∧
    Unique.Typing.Subtype classes.nominal source.nominal target.nominal

theorem Perm.comp_given_left (permission : Perm) : Perm.given.comp permission = permission := by
  cases permission <;> rfl

theorem Perm.comp_given_right (permission : Perm) : permission.comp .given = permission := by
  cases permission <;> rfl

theorem Perm.comp_shared_left (permission : Perm) : Perm.shared.comp permission = .shared := by
  cases permission <;> rfl

theorem Perm.comp_shared_right (permission : Perm) : permission.comp .shared = .shared := by
  cases permission <;> rfl

theorem Perm.comp_assoc (a b c : Perm) : (a.comp b).comp c = a.comp (b.comp c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem Perm.comp_eq_given_iff (a b : Perm) : a.comp b = .given ↔ a = .given ∧ b = .given := by
  cases a <;> cases b <;> simp [comp]

theorem Perm.toMode_comp (a b : Perm) : (a.comp b).toMode = a.toMode.join b.toMode := by
  cases a <;> cases b <;> rfl

theorem Perm.toMode_injective : Function.Injective Perm.toMode := by
  intro a b equality
  cases a <;> cases b <;> simp_all [toMode]

theorem ClassTable.nominal_keys (classes : ClassTable) :
    classes.nominal.map Prod.fst = classes.map Prod.fst := by
  simp [nominal, List.map_map, Function.comp_def]

theorem ClassTable.erase_keys (classes : ClassTable) :
    classes.erase.map Prod.fst = classes.map Prod.fst := by
  simp [erase, List.map_map, Function.comp_def]

theorem ClassTable.WellFormed.nominal {classes : ClassTable} (wf : classes.WellFormed) :
    classes.nominal.WellFormed := by
  refine ⟨?_, ?_⟩
  · simpa [ClassTable.nominal_keys] using wf.1
  · intro entry member
    obtain ⟨⟨name, declaration⟩, found, rfl⟩ := List.mem_map.mp member
    have fields := (wf.2 _ found).1
    have targets := (wf.2 _ found).2
    constructor
    · simpa [List.map_map, Function.comp_def] using fields
    · intro field member
      change field ∈ declaration.fields.map (fun field => (field.1, field.2.className)) at member
      obtain ⟨⟨fieldName, ty⟩, fieldMember, rfl⟩ := List.mem_map.mp member
      simpa only [ClassTable.nominal_keys] using (targets (fieldName, ty) fieldMember).1

theorem focus_eq_some_iff : focus classes ty path = some result ↔
    ∃ nominal permission,
      Unique.Typing.focus classes.nominal ty.nominal path = some nominal ∧
      declaredPermission classes ty.base path = some permission ∧
      result = ⟨ty.permission.comp permission, nominal⟩ := by
  simp [focus, Option.bind_eq_some_iff]
  constructor <;> rintro ⟨nominal, found, permission, declared, equality⟩ <;>
    exact ⟨nominal, found, permission, declared, equality.symm⟩

theorem focus_root (wf : ty.WellFormed classes) :
    focus classes ty [] = some (normalize classes ty) := by
  simp [focus, Unique.Typing.focus_root wf.1, declaredPermission, normalize,
    Perm.comp_given_right]

theorem emptyPath_root (classes : ClassTable) (ty : ValueType) :
    emptyPath classes ty [] = none := by
  simp [emptyPath, Unique.Typing.emptyPath_root]

theorem Subtype.refl (classes : ClassTable) (ty : ValueType) : Subtype classes ty ty :=
  ⟨rfl, Unique.Typing.Subtype.refl _ _⟩

theorem Subtype.trans (first : Subtype classes source middle)
    (second : Subtype classes middle target) : Subtype classes source target :=
  ⟨first.1.trans second.1, Unique.Typing.Subtype.trans first.2 second.2⟩

end Dada.Shared.Typing
