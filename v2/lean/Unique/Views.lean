import Unique.Syntax

namespace Dada.Unique.Typing

structure TypedClass where
  fields : List (FieldName × ClassName)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

abbrev ClassTable := List (ClassName × TypedClass)

def ClassTable.erase (classes : ClassTable) : Classes :=
  classes.map fun (name, declaration) => (name, ⟨declaration.fields.map Prod.fst⟩)

def ClassTable.WellFormed (classes : ClassTable) : Prop :=
  (classes.map Prod.fst).Nodup ∧
    ∀ entry ∈ classes, (entry.2.fields.map Prod.fst).Nodup ∧
      ∀ field ∈ entry.2.fields, field.2 ∈ classes.map Prod.fst

instance (classes : ClassTable) : Decidable classes.WellFormed := by
  unfold ClassTable.WellFormed
  infer_instance

abbrev Path := List FieldName

def classAt (classes : ClassTable) (base : ClassName) : Path → Option ClassName
  | [] => some base
  | field :: rest => do
      let declaration ← classes.lookup base
      let target ← declaration.fields.lookup field
      classAt classes target rest

inductive Entry where
  | positive (path : Path)
  | negative (path : Path)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def Entry.path : Entry → Path
  | .positive path | .negative path => path

def Entry.prepend (initialPath : Path) : Entry → Entry
  | .positive path => .positive (initialPath ++ path)
  | .negative path => .negative (initialPath ++ path)

def Entry.dropPrefix (initialPath : Path) (entry : Entry) : Option Entry :=
  if initialPath.isPrefixOf entry.path then
    some (match entry with
      | .positive path => .positive (path.drop initialPath.length)
      | .negative path => .negative (path.drop initialPath.length))
  else none

structure ViewType where
  className : ClassName
  entries : List Entry
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def ViewType.whole (name : ClassName) : ViewType :=
  ⟨name, [.positive []]⟩

def Entry.valid (classes : ClassTable) (base : ClassName) (entry : Entry) : Bool :=
  (classAt classes base entry.path).isSome &&
    match entry with
    | .positive _ => true
    | .negative path => !path.isEmpty

def entriesDisjoint : List Entry → Bool
  | [] => true
  | entry :: rest =>
    rest.all (fun other =>
      !entry.path.isPrefixOf other.path && !other.path.isPrefixOf entry.path) &&
    entriesDisjoint rest

def ViewType.WellFormed (ty : ViewType) (classes : ClassTable) : Prop :=
  (classes.lookup ty.className).isSome = true ∧
    ty.entries.all (Entry.valid classes ty.className) = true ∧
    entriesDisjoint ty.entries = true

instance (ty : ViewType) (classes : ClassTable) : Decidable (ty.WellFormed classes) := by
  unfold ViewType.WellFormed
  infer_instance

def positive (classes : ClassTable) (ty : ViewType) (path : Path) : Bool :=
  (classAt classes ty.className path).isSome &&
    (path.isEmpty || ty.entries.any (fun entry =>
      (path.length < entry.path.length && path.isPrefixOf entry.path) ||
      match entry with
      | .positive initialPath => initialPath.isPrefixOf path
      | .negative _ => false))

def negative (ty : ViewType) (path : Path) : Bool :=
  ty.entries.contains (.negative path)

def Pos (classes : ClassTable) (ty : ViewType) (path : Path) : Prop :=
  positive classes ty path = true

def Neg (ty : ViewType) (path : Path) : Prop :=
  negative ty path = true

instance (classes : ClassTable) (ty : ViewType) (path : Path) :
    Decidable (Pos classes ty path) := inferInstanceAs (Decidable (positive classes ty path = true))

instance (ty : ViewType) (path : Path) :
    Decidable (Neg ty path) := inferInstanceAs (Decidable (negative ty path = true))

def Full (classes : ClassTable) (ty : ViewType) : Prop :=
  ∀ path, Pos classes ty path →
    ∀ name declaration, classAt classes ty.className path = some name →
      classes.lookup name = some declaration →
      ∀ field ∈ declaration.fields,
        Pos classes ty (path ++ [field.1]) ∨ Neg ty (path ++ [field.1])

-- A recursive call is made only for a field with an entry beneath it. An absent
-- field therefore remains unknown, including when its declared class is empty.
-- The depth bound comes from the finite input paths, not from class unfolding.
def normalizeEntries (classes : ClassTable) : Nat → ClassName → List Entry → List Entry
  | fuel, name, entries =>
    if entries.contains (.positive []) then [.positive []]
    else match classes.lookup name with
    | none => entries
    | some declaration =>
      if declaration.fields.isEmpty && entries.isEmpty then [.positive []]
      else match fuel with
      | 0 => entries
      | fuel + 1 =>
        let children := declaration.fields.flatMap fun (field, target) =>
          let selected := entries.filterMap (Entry.dropPrefix [field])
          if selected.isEmpty then []
          else if selected.contains (.negative []) then [.negative [field]]
          else (normalizeEntries classes fuel target selected).map (Entry.prepend [field])
        if !declaration.fields.isEmpty && declaration.fields.all
            (fun field => children.contains (.positive [field.1])) then
          [.positive []]
        else children

def normalize (classes : ClassTable) (ty : ViewType) : ViewType :=
  let depth := ty.entries.foldl (fun depth entry => max depth entry.path.length) 0
  { ty with entries := normalizeEntries classes (depth + 1) ty.className ty.entries }

def Normalized (classes : ClassTable) (ty : ViewType) : Prop :=
  normalize classes ty = ty

instance (classes : ClassTable) (ty : ViewType) : Decidable (Normalized classes ty) :=
  inferInstanceAs (Decidable (normalize classes ty = ty))

def focus (classes : ClassTable) (ty : ViewType) (path : Path) : Option ViewType := do
  if !decide (ty.WellFormed classes) then none else do
    let source := normalize classes ty
    if !positive classes source path then none else do
      let target ← classAt classes source.className path
      if path.isEmpty then some source
      else if source.entries.any (fun entry => match entry with
          | .positive initialPath => initialPath.isPrefixOf path
          | .negative _ => false) then
        some (.whole target)
      else some (normalize classes ⟨target, source.entries.filterMap (Entry.dropPrefix path)⟩)

-- Expand a whole subtree only along the path being taken. Its siblings retain
-- positive entries; the target itself is omitted and will receive one negative
-- entry in emptyPath. Recursion is on the finite target path.
def remainingAfterMove (classes : ClassTable) (name : ClassName) : Path → List Entry
  | [] => []
  | field :: rest =>
    match classes.lookup name with
    | none => []
    | some declaration => declaration.fields.flatMap fun (other, target) =>
        if other == field then
          (remainingAfterMove classes target rest).map (Entry.prepend [other])
        else [.positive [other]]

def emptyPath (classes : ClassTable) (ty : ViewType) (path : Path) : Option ViewType :=
  if !decide (ty.WellFormed classes) || path.isEmpty then none
  else
    let source := normalize classes ty
    if !positive classes source path then none
    else
      let retained := source.entries.flatMap fun entry =>
        if path.isPrefixOf entry.path then []
        else match entry with
        | .negative _ => [entry]
        | .positive initialPath =>
          if initialPath.isPrefixOf path then
            match classAt classes source.className initialPath with
            | none => []
            | some target =>
              (remainingAfterMove classes target (path.drop initialPath.length)).map
                (Entry.prepend initialPath)
          else [entry]
      some (normalize classes ⟨source.className, retained ++ [.negative path]⟩)

def Subtype (classes : ClassTable) (source target : ViewType) : Prop :=
  source.className = target.className ∧
    (∀ path, Pos classes (normalize classes target) path →
      Pos classes (normalize classes source) path) ∧
    (∀ path, Neg (normalize classes target) path → Neg (normalize classes source) path)

theorem normalize_className (classes : ClassTable) (ty : ViewType) :
    (normalize classes ty).className = ty.className := rfl

theorem normalize_whole (classes : ClassTable) (name : ClassName) :
    normalize classes (.whole name) = .whole name := by
  simp [normalize, normalizeEntries, ViewType.whole]

theorem Pos.root (classes : ClassTable) (ty : ViewType) : Pos classes ty [] := by
  rfl

theorem positive_whole (classes : ClassTable) (name : ClassName) (path : Path) :
    positive classes (.whole name) path = (classAt classes name path).isSome := by
  simp [positive, ViewType.whole, Entry.path]

theorem Pos.valid (known : Pos classes ty path) :
    (classAt classes ty.className path).isSome = true := by
  exact (Bool.and_eq_true_iff.mp known).1

theorem focus_root (wf : ty.WellFormed classes) :
    focus classes ty [] = some (normalize classes ty) := by
  simp [focus, wf, positive, classAt]

theorem emptyPath_root (classes : ClassTable) (ty : ViewType) :
    emptyPath classes ty [] = none := by
  simp [emptyPath]

theorem Subtype.refl (classes : ClassTable) (ty : ViewType) : Subtype classes ty ty :=
  ⟨rfl, fun _ h => h, fun _ h => h⟩

theorem Subtype.trans (first : Subtype classes source middle)
    (second : Subtype classes middle target) : Subtype classes source target :=
  ⟨first.1.trans second.1,
    fun path h => first.2.1 path (second.2.1 path h),
    fun path h => first.2.2 path (second.2.2 path h)⟩

theorem negative_whole (name : ClassName) (path : Path) :
    negative (.whole name) path = false := by
  rfl

end Dada.Unique.Typing
