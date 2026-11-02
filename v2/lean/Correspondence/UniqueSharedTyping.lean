import Correspondence.UniqueSharedUnpacking
import Unique.TypingEffects
import Shared.TypingEffects
import Shared.TypingViewLemmas

namespace Dada.Correspondence.Typing

def embedType (ty : Unique.Typing.ViewType) : Shared.Typing.ValueType := ⟨.given, ty⟩

def embedClass (declaration : Unique.Typing.TypedClass) : Shared.Typing.TypedClass :=
  ⟨declaration.fields.map fun field => (field.1, ⟨.given, field.2⟩)⟩

def embedClasses (classes : Unique.Typing.ClassTable) : Shared.Typing.ClassTable :=
  classes.map fun entry => (entry.1, embedClass entry.2)

def embedEnvironment (environment : Unique.Typing.Environment) : Shared.Typing.Environment :=
  environment.map fun entry => (entry.1, entry.2.map embedType)

def eraseEnvironment (environment : Shared.Typing.Environment) : Unique.Typing.Environment :=
  environment.map fun entry => (entry.1, entry.2.map Shared.Typing.ValueType.nominal)

@[simp] theorem nominal_embed (classes : Unique.Typing.ClassTable) :
    (embedClasses classes).nominal = classes := by
  simp only [embedClasses, Shared.Typing.ClassTable.nominal, List.map_map]
  conv => rhs; rw [← List.map_id classes]
  apply List.map_congr_left
  intro entry _
  rcases entry with ⟨name, ⟨fields⟩⟩
  simp [embedClass, List.map_map, Function.comp_def]

@[simp] theorem erase_embed_classes (classes : Unique.Typing.ClassTable) :
    (embedClasses classes).erase = Dada.Correspondence.embedClasses classes.erase := by
  simp [embedClasses, embedClass, Shared.Typing.ClassTable.erase,
    Dada.Correspondence.embedClasses, Unique.Typing.ClassTable.erase,
    List.map_map, Function.comp_def]

@[simp] theorem embed_classes_keys (classes : Unique.Typing.ClassTable) :
    (embedClasses classes).map Prod.fst = classes.map Prod.fst := by
  simp [embedClasses, List.map_map, Function.comp_def]

@[simp] theorem embed_environment_keys (environment : Unique.Typing.Environment) :
    (embedEnvironment environment).map Prod.fst = environment.map Prod.fst := by
  simp [embedEnvironment, List.map_map, Function.comp_def]

@[simp] theorem erase_embed_environment (environment : Unique.Typing.Environment) :
    eraseEnvironment (embedEnvironment environment) = environment := by
  simp [eraseEnvironment, embedEnvironment, embedType, List.map_map,
    Function.comp_def, Option.map_map]

@[simp] theorem admissible_embed (classes : Unique.Typing.ClassTable)
    (ty : Unique.Typing.ViewType) :
    Shared.Typing.Admissible (embedClasses classes) (embedType ty) ↔
      Unique.Typing.Admissible classes ty := by
  simp [Shared.Typing.Admissible, Shared.Typing.ValueType.WellFormed,
    Shared.Typing.Normalized, embedType, Unique.Typing.Admissible]

@[simp] theorem environment_wellFormed_embed (classes : Unique.Typing.ClassTable)
    (environment : Unique.Typing.Environment) :
    (embedEnvironment environment).WellFormed (embedClasses classes) ↔
      environment.WellFormed classes := by
  constructor
  · rintro ⟨keys, entries⟩
    refine ⟨by simpa using keys, List.all_eq_true.mpr ?_⟩
    rintro ⟨name, slot⟩ member
    have checked := List.all_eq_true.mp entries (name, slot.map embedType)
      (List.mem_map.mpr ⟨(name, slot), member, rfl⟩)
    cases slot with
    | none => rfl
    | some ty =>
      exact decide_eq_true ((admissible_embed classes ty).mp (of_decide_eq_true checked))
  · rintro ⟨keys, entries⟩
    refine ⟨by simpa using keys, List.all_eq_true.mpr ?_⟩
    intro entry member
    change entry ∈ environment.map (fun entry => (entry.1, entry.2.map embedType)) at member
    obtain ⟨⟨name, slot⟩, originalMember, rfl⟩ := List.mem_map.mp member
    have checked := List.all_eq_true.mp entries (name, slot) originalMember
    cases slot with
    | none => rfl
    | some ty =>
      exact decide_eq_true ((admissible_embed classes ty).mpr (of_decide_eq_true checked))

@[simp] theorem splitPlace_embed (place : Unique.Place) :
    Shared.Typing.splitPlace (embedPlace place) = Unique.Typing.splitPlace place := by
  induction place with
  | «variable» => rfl
  | field base name ih => simp [Shared.Typing.splitPlace, Unique.Typing.splitPlace, embedPlace, ih]

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

@[simp] theorem lookup_embed_class (classes : Unique.Typing.ClassTable) (name : String) :
    (embedClasses classes).lookup name = (classes.lookup name).map embedClass :=
  lookup_map_value classes name _

@[simp] theorem lookup_embed_field (declaration : Unique.Typing.TypedClass) (name : String) :
    (embedClass declaration).fields.lookup name =
      (declaration.fields.lookup name).map (fun target => (⟨.given, target⟩ : Shared.Typing.FieldType)) :=
  lookup_map_value declaration.fields name _

theorem declaredPermission_embed (classes : Unique.Typing.ClassTable) (name : String)
    (path : Unique.Typing.Path) :
    Shared.Typing.declaredPermission (embedClasses classes) name path =
      (Unique.Typing.classAt classes name path).map (fun _ => Shared.Typing.Perm.given) := by
  induction path generalizing name with
  | nil => rfl
  | cons field rest ih =>
    cases found : classes.lookup name with
    | none => simp [Shared.Typing.declaredPermission, Unique.Typing.classAt, found]
    | some declaration =>
      cases fieldFound : declaration.fields.lookup field with
      | none => simp [Shared.Typing.declaredPermission, Unique.Typing.classAt, found, fieldFound]
      | some target =>
        simp [Shared.Typing.declaredPermission, Unique.Typing.classAt, found, fieldFound, ih,
          Shared.Typing.Perm.comp_given_left]

theorem focus_embed (classes : Unique.Typing.ClassTable) (ty : Unique.Typing.ViewType)
    (path : Unique.Typing.Path) :
    Shared.Typing.focus (embedClasses classes) (embedType ty) path =
      (Unique.Typing.focus classes ty path).map embedType := by
  cases atClass : Unique.Typing.classAt classes ty.className path with
  | none =>
    have noFocus : Unique.Typing.focus classes ty path = none := by
      simp [Unique.Typing.focus, Unique.Typing.normalize_className, atClass]
    simp [Shared.Typing.focus, embedType, noFocus]
  | some target =>
    simp [Shared.Typing.focus, Shared.Typing.ValueType.base, embedType,
      declaredPermission_embed, atClass, Shared.Typing.Perm.comp_given_left]
    cases Unique.Typing.focus classes ty path <;> rfl

theorem emptyPath_embed (classes : Unique.Typing.ClassTable) (ty : Unique.Typing.ViewType)
    (path : Unique.Typing.Path) :
    Shared.Typing.emptyPath (embedClasses classes) (embedType ty) path =
      (Unique.Typing.emptyPath classes ty path).map embedType := by
  simp only [Shared.Typing.emptyPath, embedType, nominal_embed]
  rfl

@[simp] theorem environment_lookup_embed (environment : Unique.Typing.Environment) (name : String) :
    (embedEnvironment environment).lookup name = (environment.lookup name).map (Option.map embedType) := by
  simp [Shared.Typing.Environment.lookup, Unique.Typing.Environment.lookup,
    embedEnvironment, List.find?_map, Function.comp_def, Option.map_map]

theorem environment_replace_embed (environment : Unique.Typing.Environment) (name : String)
    (description : Unique.Typing.SlotDescription) :
    (embedEnvironment environment).replace name (description.map embedType) =
      embedEnvironment (environment.replace name description) := by
  simp only [Shared.Typing.Environment.replace, Unique.Typing.Environment.replace,
    embedEnvironment, List.map_map]
  apply List.map_congr_left
  intro entry _
  by_cases same : entry.1 = name <;> simp [same]

theorem give_embed (classes : Unique.Typing.ClassTable) (environment : Unique.Typing.Environment)
    (place : Unique.Place) :
    Shared.Typing.give (embedClasses classes) (embedEnvironment environment) (embedPlace place) =
      (Unique.Typing.take classes environment place).map
        (fun result => (embedType result.1, embedEnvironment result.2)) := by
  simp only [Shared.Typing.give, Unique.Typing.take, splitPlace_embed, environment_lookup_embed]
  cases sourceFound : environment.lookup (Unique.Typing.splitPlace place).1 with
  | none => rfl
  | some sourceSlot =>
    cases sourceSlot with
    | none => rfl
    | some source =>
      dsimp only [Option.map, Bind.bind, Option.bind]
      rw [focus_embed]
      cases focused : Unique.Typing.focus classes source (Unique.Typing.splitPlace place).2 with
      | none => rfl
      | some result =>
        dsimp only [Option.map, Bind.bind, Option.bind]
        simp only [show (embedType result).permission = .given from rfl, reduceCtorEq, ↓reduceIte]
        by_cases empty : (Unique.Typing.splitPlace place).2 = []
        · simp [empty, ← environment_replace_embed]
        · simp only [empty, ↓reduceIte, emptyPath_embed]
          cases Unique.Typing.emptyPath classes source (Unique.Typing.splitPlace place).2 with
          | none => rfl
          | some remaining =>
            simp [← environment_replace_embed]

theorem subtype_embed (classes : Unique.Typing.ClassTable) (source target : Unique.Typing.ViewType) :
    Shared.Typing.Subtype (embedClasses classes) (embedType source) (embedType target) ↔
      Unique.Typing.Subtype classes source target := by
  simp [Shared.Typing.Subtype, embedType]

theorem fieldDescription_embed (classes : Unique.Typing.ClassTable)
    (ty : Unique.Typing.ViewType) (field : String) :
    Shared.Typing.fieldDescription (embedClasses classes) (embedType ty) field =
      (Unique.Typing.fieldDescription classes ty field).map (Option.map embedType) := by
  unfold Shared.Typing.fieldDescription Unique.Typing.fieldDescription
  change (if Unique.Typing.negative ty [field] then some none else
    (Shared.Typing.focus (embedClasses classes) (embedType ty) [field]).map some) = _
  rw [focus_embed]
  cases Unique.Typing.negative ty [field] <;> simp [Option.map_map, Function.comp_def]

@[simp] theorem embed_environment_append (left right : Unique.Typing.Environment) :
    embedEnvironment (left ++ right) = embedEnvironment left ++ embedEnvironment right := by
  simp [embedEnvironment]

@[simp] theorem embed_environment_cons (name : String) (slot : Unique.Typing.SlotDescription)
    (rest : Unique.Typing.Environment) :
    embedEnvironment ((name, slot) :: rest) = (name, slot.map embedType) :: embedEnvironment rest := rfl

theorem expression_forward
    (typed : Unique.Typing.ExprTyped classes before value ty after) :
    Shared.Typing.ExprTyped (embedClasses classes) (embedEnvironment before) (embedValue value)
      (embedType ty) (embedEnvironment after) := by
  induction typed using Unique.Typing.ExprTyped.rec
    (motive_2 := fun before values names after _ =>
      Shared.Typing.ArgsTyped (embedClasses classes) (embedEnvironment before)
        (values.map embedValue) (names.map fun name => ⟨.given, name⟩) (embedEnvironment after)) with
  | give beforeWf taken admissible afterWf =>
    simp only [embedValue]
    exact .give (by simpa using beforeWf) (by simp [give_embed, taken])
      (by simpa using admissible) (by simpa using afterWf)
  | @new before after name declaration arguments declared typedArgs admissible ih =>
    simp only [embedValue]
    apply Shared.Typing.ExprTyped.new (classes := embedClasses classes) (name := name)
      (declaration := embedClass declaration)
      (List.mem_map.mpr ⟨(name, declaration), declared, rfl⟩)
    · simpa [embedClass, List.map_map, Function.comp_def] using ih
    · exact (admissible_embed _ _).mpr admissible
  | weaken _ admissible subtype ih =>
    exact .weaken ih ((admissible_embed _ _).mpr admissible) ((subtype_embed _ _ _).mpr subtype)
  | nil wf => exact .nil (by simpa using wf)
  | cons _ _ first rest => exact .cons first rest

theorem arguments_forward
    (typed : Unique.Typing.ArgsTyped classes before values names after) :
    Shared.Typing.ArgsTyped (embedClasses classes) (embedEnvironment before)
      (values.map embedValue) (names.map fun name => ⟨.given, name⟩) (embedEnvironment after) := by
  induction typed using Unique.Typing.ArgsTyped.rec (motive_1 := fun _ _ _ _ _ => True) with
  | give => trivial
  | new => trivial
  | weaken => trivial
  | nil wf => exact .nil (by simpa using wf)
  | cons first _ _ rest => exact .cons (expression_forward first) rest

theorem fieldBindings_forward
    (typed : Unique.Typing.FieldBindings classes ty fields bindings) :
    Shared.Typing.FieldBindings (embedClasses classes) (embedType ty) fields
      (embedEnvironment bindings) := by
  induction typed with
  | nil => exact .nil
  | cons field _ ih =>
    exact .cons (by simp [fieldDescription_embed, field]) ih

theorem binding_forward
    (typed : Unique.Typing.BindingTyped classes before pattern ty after) :
    Shared.Typing.BindingTyped (embedClasses classes) (embedEnvironment before)
      (Unpacking.embedPattern pattern) (embedType ty) (embedEnvironment after) := by
  cases typed with
  | «variable» wf admissible fresh =>
    exact .variable (by simpa using wf) (by simpa using admissible) (by simpa using fresh)
  | @unpack ty name declaration fields bindings wf admissible base declared permutation
      distinct fresh described afterWf =>
    rw [embed_environment_append]
    apply Shared.Typing.BindingTyped.unpack (classes := embedClasses classes)
      (declaration := embedClass declaration)
      (by simpa using wf) (by simpa using admissible) rfl base
      (List.mem_map.mpr ⟨(name, declaration), declared, rfl⟩)
    · simpa [embedClass, List.map_map, Function.comp_def] using permutation
    · exact distinct
    · simpa using fresh
    · exact fieldBindings_forward described
    · simpa using (environment_wellFormed_embed classes (bindings ++ before)).mpr afterWf

theorem statement_forward
    (typed : Unique.Typing.StatementTyped classes before statement after) :
    Shared.Typing.StatementTyped (embedClasses classes) (embedEnvironment before)
      (Unpacking.embedStatement statement) (embedEnvironment after) := by
  cases typed with
  | letValue expression binding => exact .letValue (expression_forward expression) (binding_forward binding)

theorem sequence_forward
    (typed : Unique.Typing.SequenceTyped classes before statements after) :
    Shared.Typing.SequenceTyped (embedClasses classes) (embedEnvironment before)
      (statements.map Unpacking.embedStatement) (embedEnvironment after) := by
  induction typed with
  | nil wf => exact .nil (by simpa using wf)
  | cons first _ rest => exact .cons (statement_forward first) rest

theorem expression_reflect_general
    (typed : Shared.Typing.ExprTyped (embedClasses classes) before value ty after) :
    ∀ originalBefore originalValue,
      before = embedEnvironment originalBefore → value = embedValue originalValue →
      ∃ originalAfter, after = embedEnvironment originalAfter ∧ ty.permission = .given ∧
        Unique.Typing.ExprTyped classes originalBefore originalValue ty.nominal originalAfter := by
  induction typed using Shared.Typing.ExprTyped.rec
    (motive_2 := fun before values fields after _ =>
      ∀ originalBefore originalValues,
        before = embedEnvironment originalBefore → values = originalValues.map embedValue →
        ∃ originalAfter, after = embedEnvironment originalAfter ∧
          Unique.Typing.ArgsTyped classes originalBefore originalValues
            (fields.map Shared.Typing.FieldType.className) originalAfter) with
  | @give before after place ty beforeWf given admissible afterWf =>
    intro originalBefore originalValue beforeEq valueEq
    subst before
    cases originalValue with
    | new name args => simp only [embedValue] at valueEq; cases valueEq
    | give originalPlace =>
      simp only [embedValue, Shared.Value.give.injEq] at valueEq
      subst place
      rw [give_embed] at given
      obtain ⟨⟨originalType, originalAfter⟩, taken, resultEq⟩ := Option.map_eq_some_iff.mp given
      cases resultEq
      exact ⟨originalAfter, rfl, rfl, .give (by simpa using beforeWf) taken
        ((admissible_embed _ _).mp admissible) (by simpa using afterWf)⟩
  | giveShare =>
    intro originalBefore originalValue _ valueEq
    cases originalValue <;> simp only [embedValue] at valueEq <;> cases valueEq
  | @new before after name declaration arguments declared typedArgs admissible ih =>
    intro originalBefore originalValue beforeEq valueEq
    cases originalValue with
    | give place => simp only [embedValue] at valueEq; cases valueEq
    | new originalName originalArguments =>
      simp only [embedValue, Shared.Value.new.injEq] at valueEq
      obtain ⟨rfl, rfl⟩ := valueEq
      change (name, declaration) ∈ classes.map
        (fun entry => (entry.1, embedClass entry.2)) at declared
      obtain ⟨⟨name, originalDeclaration⟩, originalDeclared, equal⟩ := List.mem_map.mp declared
      cases equal
      obtain ⟨originalAfter, afterEq, argumentsTyped⟩ := ih originalBefore originalArguments beforeEq rfl
      refine ⟨originalAfter, afterEq, rfl, ?_⟩
      apply Unique.Typing.ExprTyped.new originalDeclared
      · simpa [embedClass, List.map_map, Function.comp_def] using argumentsTyped
      · exact (admissible_embed _ _).mp admissible
  | @weaken before after value ty other typed admissible subtype ih =>
    intro originalBefore originalValue beforeEq valueEq
    obtain ⟨originalAfter, afterEq, given, originalTyped⟩ := ih originalBefore originalValue beforeEq valueEq
    have otherGiven := subtype.1.symm.trans given
    refine ⟨originalAfter, afterEq, otherGiven, .weaken originalTyped ?_ ?_⟩
    · simpa [Shared.Typing.Admissible, Shared.Typing.ValueType.WellFormed,
        Shared.Typing.Normalized, Unique.Typing.Admissible] using admissible
    · simpa using subtype.2
  | @nil environment wf =>
    rename_i originalBefore originalValues beforeEq valuesEq
    cases originalValues with
    | cons value rest => cases valuesEq
    | nil =>
      subst environment
      exact ⟨originalBefore, rfl, .nil (by simpa using wf)⟩
  | @cons before middle after value values field fields first rest firstIH restIH =>
    rename_i originalBefore originalValues beforeEq valuesEq
    cases originalValues with
    | nil => cases valuesEq
    | cons originalValue originalValues =>
      have parts := List.cons.inj valuesEq
      obtain ⟨originalMiddle, middleEq, _, firstTyped⟩ :=
        firstIH originalBefore originalValue beforeEq parts.1
      obtain ⟨originalAfter, afterEq, restTyped⟩ :=
        restIH originalMiddle originalValues middleEq parts.2
      exact ⟨originalAfter, afterEq, .cons firstTyped restTyped⟩

theorem expression_backward
    (typed : Shared.Typing.ExprTyped (embedClasses classes) (embedEnvironment before)
      (embedValue value) (embedType ty) (embedEnvironment after)) :
    Unique.Typing.ExprTyped classes before value ty after := by
  obtain ⟨originalAfter, afterEq, _, originalTyped⟩ := expression_reflect_general typed before value rfl rfl
  have same : after = originalAfter := by
    simpa using congrArg eraseEnvironment afterEq
  subst originalAfter
  exact originalTyped

theorem expression_correspondence :
    Unique.Typing.ExprTyped classes before value ty after ↔
      Shared.Typing.ExprTyped (embedClasses classes) (embedEnvironment before)
        (embedValue value) (embedType ty) (embedEnvironment after) :=
  ⟨expression_forward, expression_backward⟩

theorem fieldBindings_reflect_general
    (typed : Shared.Typing.FieldBindings (embedClasses classes) (embedType ty) fields bindings) :
    ∃ originalBindings, bindings = embedEnvironment originalBindings ∧
      Unique.Typing.FieldBindings classes ty fields originalBindings := by
  induction typed with
  | nil => exact ⟨[], rfl, .nil⟩
  | @cons field destination description fields bindings described rest ih =>
    rw [fieldDescription_embed] at described
    obtain ⟨originalDescription, originalDescribed, same⟩ := Option.map_eq_some_iff.mp described
    obtain ⟨originalBindings, bindingsEq, originalRest⟩ := ih
    subst description bindings
    exact ⟨(destination, originalDescription) :: originalBindings, rfl,
      .cons originalDescribed originalRest⟩

theorem binding_reflect_general
    (typed : Shared.Typing.BindingTyped (embedClasses classes) before pattern ty after) :
    ∀ originalBefore originalPattern originalType,
      before = embedEnvironment originalBefore → pattern = Unpacking.embedPattern originalPattern →
      ty = embedType originalType →
      ∃ originalAfter, after = embedEnvironment originalAfter ∧
        Unique.Typing.BindingTyped classes originalBefore originalPattern originalType originalAfter := by
  cases typed with
  | @«variable» name ty wf admissible fresh =>
    intro originalBefore originalPattern originalType beforeEq patternEq typeEq
    subst before ty
    cases originalPattern with
    | unpack name fields => simp only [Unpacking.embedPattern] at patternEq; cases patternEq
    | «variable» originalName =>
      simp only [Unpacking.embedPattern, Shared.Unpacking.Pattern.variable.injEq] at patternEq
      subst name
      exact ⟨(originalName, some originalType) :: originalBefore, rfl,
        .variable (by simpa using wf) (by simpa using admissible) (by simpa using fresh)⟩
  | @unpack ty name declaration fields bindings wf admissible given base declared
      permutation distinct fresh described afterWf =>
    intro originalBefore originalPattern originalType beforeEq patternEq typeEq
    subst before ty
    cases originalPattern with
    | «variable» name => simp only [Unpacking.embedPattern] at patternEq; cases patternEq
    | unpack originalName originalFields =>
      simp only [Unpacking.embedPattern, Shared.Unpacking.Pattern.unpack.injEq] at patternEq
      obtain ⟨rfl, rfl⟩ := patternEq
      change (name, declaration) ∈ classes.map
        (fun entry => (entry.1, embedClass entry.2)) at declared
      obtain ⟨⟨name, originalDeclaration⟩, originalDeclared, equal⟩ := List.mem_map.mp declared
      cases equal
      obtain ⟨originalBindings, bindingsEq, originalDescription⟩ := fieldBindings_reflect_general described
      subst bindings
      refine ⟨originalBindings ++ originalBefore, (embed_environment_append _ _).symm, ?_⟩
      apply Unique.Typing.BindingTyped.unpack (before := originalBefore) (ty := originalType)
        (declaration := originalDeclaration)
        (by simpa using wf) ((admissible_embed _ _).mp admissible) base originalDeclared
      · simpa [embedClass, List.map_map, Function.comp_def] using permutation
      · exact distinct
      · simpa using fresh
      · exact originalDescription
      · exact (environment_wellFormed_embed _ _).mp (by simpa using afterWf)

theorem binding_backward
    (typed : Shared.Typing.BindingTyped (embedClasses classes) (embedEnvironment before)
      (Unpacking.embedPattern pattern) (embedType ty) (embedEnvironment after)) :
    Unique.Typing.BindingTyped classes before pattern ty after := by
  obtain ⟨originalAfter, afterEq, original⟩ := binding_reflect_general typed before pattern ty rfl rfl rfl
  have same : after = originalAfter := by simpa using congrArg eraseEnvironment afterEq
  subst originalAfter
  exact original

theorem binding_correspondence :
    Unique.Typing.BindingTyped classes before pattern ty after ↔
      Shared.Typing.BindingTyped (embedClasses classes) (embedEnvironment before)
        (Unpacking.embedPattern pattern) (embedType ty) (embedEnvironment after) :=
  ⟨binding_forward, binding_backward⟩

theorem statement_reflect_general
    (typed : Shared.Typing.StatementTyped (embedClasses classes) (embedEnvironment before)
      (Unpacking.embedStatement statement) after) :
    ∃ originalAfter, after = embedEnvironment originalAfter ∧
      Unique.Typing.StatementTyped classes before statement originalAfter := by
  cases statement with
  | mk pattern value =>
    cases typed with
    | letValue expression binding =>
      rename_i middle ty
      obtain ⟨originalMiddle, middleEq, given, originalExpression⟩ :=
        expression_reflect_general expression before value rfl rfl
      have typeEq : ty = embedType ty.nominal := by
        cases ty with
        | mk permission nominal => simp only at given; simp [given, embedType]
      obtain ⟨originalAfter, afterEq, originalBinding⟩ := binding_reflect_general binding
        originalMiddle pattern ty.nominal middleEq rfl typeEq
      exact ⟨originalAfter, afterEq, .letValue originalExpression originalBinding⟩

theorem statement_backward
    (typed : Shared.Typing.StatementTyped (embedClasses classes) (embedEnvironment before)
      (Unpacking.embedStatement statement) (embedEnvironment after)) :
    Unique.Typing.StatementTyped classes before statement after := by
  obtain ⟨originalAfter, afterEq, original⟩ := statement_reflect_general typed
  have same : after = originalAfter := by simpa using congrArg eraseEnvironment afterEq
  subst originalAfter
  exact original

theorem statement_correspondence :
    Unique.Typing.StatementTyped classes before statement after ↔
      Shared.Typing.StatementTyped (embedClasses classes) (embedEnvironment before)
        (Unpacking.embedStatement statement) (embedEnvironment after) :=
  ⟨statement_forward, statement_backward⟩

theorem sequence_reflect_general
    (typed : Shared.Typing.SequenceTyped (embedClasses classes) before statements after) :
    ∀ originalBefore originalStatements,
      before = embedEnvironment originalBefore → statements = originalStatements.map Unpacking.embedStatement →
      ∃ originalAfter, after = embedEnvironment originalAfter ∧
        Unique.Typing.SequenceTyped classes originalBefore originalStatements originalAfter := by
  induction typed with
  | nil wf =>
    intro originalBefore originalStatements beforeEq statementsEq
    cases originalStatements with
    | cons => cases statementsEq
    | nil =>
      rw [beforeEq] at wf
      exact ⟨originalBefore, beforeEq, .nil (by simpa using wf)⟩
  | cons first rest ih =>
    intro originalBefore originalStatements beforeEq statementsEq
    cases originalStatements with
    | nil => cases statementsEq
    | cons statement statements =>
      have parts := List.cons.inj statementsEq
      rw [beforeEq, parts.1] at first
      obtain ⟨originalMiddle, middleEq, firstTyped⟩ := statement_reflect_general first
      obtain ⟨originalAfter, afterEq, restTyped⟩ := ih originalMiddle statements middleEq parts.2
      exact ⟨originalAfter, afterEq, .cons firstTyped restTyped⟩

theorem sequence_backward
    (typed : Shared.Typing.SequenceTyped (embedClasses classes) (embedEnvironment before)
      (statements.map Unpacking.embedStatement) (embedEnvironment after)) :
    Unique.Typing.SequenceTyped classes before statements after := by
  obtain ⟨originalAfter, afterEq, original⟩ := sequence_reflect_general typed before statements rfl rfl
  have same : after = originalAfter := by simpa using congrArg eraseEnvironment afterEq
  subst originalAfter
  exact original

theorem sequence_correspondence :
    Unique.Typing.SequenceTyped classes before statements after ↔
      Shared.Typing.SequenceTyped (embedClasses classes) (embedEnvironment before)
        (statements.map Unpacking.embedStatement) (embedEnvironment after) :=
  ⟨sequence_forward, sequence_backward⟩

theorem classes_wellFormed_correspondence (classes : Unique.Typing.ClassTable) :
    (embedClasses classes).WellFormed ↔ classes.WellFormed := by
  constructor
  · intro wf
    simpa using wf.nominal
  · intro wf
    refine ⟨by simpa using wf.1, ?_⟩
    intro entry member
    change entry ∈ classes.map (fun entry => (entry.1, embedClass entry.2)) at member
    obtain ⟨⟨name, declaration⟩, declared, rfl⟩ := List.mem_map.mp member
    refine ⟨?_, ?_⟩
    · simpa [embedClass, List.map_map, Function.comp_def] using (wf.2 _ declared).1
    · intro field member
      change field ∈ declaration.fields.map (fun field =>
        (field.1, (⟨.given, field.2⟩ : Shared.Typing.FieldType))) at member
      obtain ⟨⟨field, target⟩, originalMember, rfl⟩ := List.mem_map.mp member
      simpa using (wf.2 _ declared).2 (field, target) originalMember

theorem program_correspondence (classes : Unique.Typing.ClassTable)
    (statements : List Unique.Unpacking.Statement) :
    Unique.Typing.ProgramTyped classes statements ↔
      Shared.Typing.ProgramTyped (embedClasses classes) (statements.map Unpacking.embedStatement) := by
  constructor
  · rintro ⟨classesWf, final, typed⟩
    exact ⟨(classes_wellFormed_correspondence classes).mpr classesWf,
      embedEnvironment final, sequence_forward typed⟩
  · rintro ⟨classesWf, final, typed⟩
    obtain ⟨originalFinal, _, original⟩ := sequence_reflect_general typed [] statements rfl rfl
    exact ⟨(classes_wellFormed_correspondence classes).mp classesWf, originalFinal, original⟩

-- The embedding adds given to every static type and unique to every runtime
-- reference. Backward execution quantifies over arbitrary Shared successors.
theorem given_fragment (classes : Unique.Typing.ClassTable) :
    (∀ before value ty after,
      Unique.Typing.ExprTyped classes before value ty after ↔
        Shared.Typing.ExprTyped (embedClasses classes) (embedEnvironment before)
          (embedValue value) (embedType ty) (embedEnvironment after)) ∧
    (∀ before pattern ty after,
      Unique.Typing.BindingTyped classes before pattern ty after ↔
        Shared.Typing.BindingTyped (embedClasses classes) (embedEnvironment before)
          (Unpacking.embedPattern pattern) (embedType ty) (embedEnvironment after)) ∧
    (∀ before statement after,
      Unique.Typing.StatementTyped classes before statement after ↔
        Shared.Typing.StatementTyped (embedClasses classes) (embedEnvironment before)
          (Unpacking.embedStatement statement) (embedEnvironment after)) ∧
    (∀ before statements after,
      Unique.Typing.SequenceTyped classes before statements after ↔
        Shared.Typing.SequenceTyped (embedClasses classes) (embedEnvironment before)
          (statements.map Unpacking.embedStatement) (embedEnvironment after)) ∧
    (∀ statements, Unique.Typing.ProgramTyped classes statements ↔
      Shared.Typing.ProgramTyped (embedClasses classes) (statements.map Unpacking.embedStatement)) ∧
    (∀ before after,
      Shared.Unpacking.Step (embedClasses classes).erase (Unpacking.embedConfiguration before) after ↔
        ∃ successor, Unique.Unpacking.Step classes.erase before successor ∧
          after = Unpacking.embedConfiguration successor) ∧
    (∀ before after,
      Shared.Unpacking.Steps (embedClasses classes).erase (Unpacking.embedConfiguration before) after ↔
        ∃ successor, Unique.Unpacking.Steps classes.erase before successor ∧
          after = Unpacking.embedConfiguration successor) ∧
    (∀ configuration, (Unpacking.embedConfiguration configuration).finished ↔ configuration.finished) ∧
    (∀ configuration,
      (∃ final, Shared.Unpacking.Steps (embedClasses classes).erase
        (Unpacking.embedConfiguration configuration) final ∧ final.finished) ↔
      (∃ final, Unique.Unpacking.Steps classes.erase configuration final ∧ final.finished)) := by
  refine ⟨fun _ _ _ _ => expression_correspondence,
    fun _ _ _ _ => binding_correspondence, fun _ _ _ => statement_correspondence,
    fun _ _ _ => sequence_correspondence, program_correspondence classes, ?_, ?_,
    Unpacking.finished_correspondence, ?_⟩
  · intro before after
    simpa using (Unpacking.step_correspondence (classes := classes.erase)
      (before := before) (after := after))
  · intro before after
    simpa using (Unpacking.steps_correspondence (classes := classes.erase)
      (before := before) (after := after))
  · intro configuration
    simpa using (Unpacking.completion_correspondence (classes := classes.erase) configuration)

end Dada.Correspondence.Typing
