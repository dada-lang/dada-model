import Unique.TypingRealization

namespace Dada.Unique.Typing

def ConfigurationTyped (classes : ClassTable) (configuration : Unpacking.Configuration)
    (finalEnvironment : Environment) : Prop :=
  ∃ current, Realizes classes current configuration.state [] ∧
    SequenceTyped classes current configuration.code finalEnvironment

theorem ConfigurationTyped.initial
    (typed : ProgramTyped classes code) :
    ∃ finalEnvironment, ConfigurationTyped classes ⟨State.empty, code⟩ finalEnvironment := by
  obtain ⟨classesWf, finalEnvironment, sequence⟩ := typed
  exact ⟨finalEnvironment, [], Realizes.empty classesWf, sequence⟩

theorem ConfigurationTyped.finished
    (typed : ConfigurationTyped classes configuration finalEnvironment)
    (finished : configuration.finished) :
    Realizes classes finalEnvironment configuration.state [] := by
  obtain ⟨current, realized, sequence⟩ := typed
  change configuration.code = [] at finished
  rw [finished] at sequence
  cases sequence
  exact realized

end Dada.Unique.Typing
