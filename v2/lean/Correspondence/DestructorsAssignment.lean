import Assignment.Step
import Destructors.Step

namespace Dada.Correspondence.DestructorsAssignment

def statement : Destructors.Statement → Assignment.Statement
  | .local s => .local s
  | .call destination name arguments => .call destination name arguments
  | .dropStruct place => .dropStruct place

def body (source : Destructors.Body) : Assignment.Body :=
  ⟨source.statements.map statement, source.result⟩

def declaration (source : Destructors.Declaration) : Assignment.Declaration :=
  ⟨source.signature, body source.body⟩

def declarations (source : Destructors.Declarations) : Assignment.Declarations :=
  source.map fun (name, decl) => (name, declaration decl)

def frame (source : Destructors.Frame) : Assignment.Frame :=
  ⟨source.variables, body source.body, source.destination⟩

def configuration (source : Destructors.Configuration) : Assignment.Configuration :=
  ⟨source.objects, source.nextId, source.frames.map frame⟩

theorem running (state : Shared.State) (code : Destructors.Body) frames destination :
    configuration (.running state code frames destination) =
      .running state (body code) (frames.map frame) destination := rfl

theorem resultEval (h : Destructors.ResultEval classes before value after reference) :
    Assignment.ResultEval classes before value after reference := by
  cases h with
  | none => exact .none _
  | some evaluated => exact .some evaluated

theorem deliver (h : Destructors.Deliver before destination reference after) :
    Assignment.Deliver before destination reference after := by
  cases h with
  | none => exact .none _
  | some fresh => exact .some fresh

theorem raw_forward (h : Destructors.RawStep classes decls before after) :
    Assignment.RawStep classes (declarations decls) (configuration before) (configuration after) := by
  cases h with
  | «local» stepped => exact .local stepped
  | call declared shape fresh evaluated arity =>
    apply Assignment.RawStep.call (declaration := declaration _) _ shape fresh evaluated arity
    exact List.mem_map.mpr ⟨_, declared, rfl⟩
  | dropStruct evaluated structRef => exact .dropStruct evaluated structRef
  | @«return» before evaluated result reference caller frames destination variables evaluation delivered finished =>
    exact .return (evaluated := evaluated) (caller := frame caller)
      (resultEval evaluation) (deliver delivered) finished
  | exit finished => exact .exit finished

theorem collect (source : Destructors.Configuration) :
    configuration source.collect = (configuration source).collect := by
  have roots : (source.frames.map frame).flatMap Assignment.Frame.variables =
      source.frames.flatMap Destructors.Frame.variables := by
    simp [List.flatMap_map, frame]
  simp [configuration, Destructors.Configuration.collect, Assignment.Configuration.collect,
    Destructors.Configuration.rootState, Assignment.Configuration.rootState, roots]

theorem step_forward (h : Destructors.Step classes decls before after) :
    Assignment.Step classes (declarations decls) (configuration before) (configuration after) := by
  cases h with
  | collect raw => rw [collect]; exact .collect (raw_forward raw)

end Dada.Correspondence.DestructorsAssignment
