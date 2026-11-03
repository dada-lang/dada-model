-- Executed by scripts/check-assumptions.sh after rebuilding all dependencies.
import Unique.Normalization
import Unique.TypingSafety
import Unique.Liveness
import Shared.KindSafety
import Shared.Liveness
import Shared.TypingSafety
import Correspondence.UniqueSharedUnpacking
import Correspondence.UniqueSharedTyping
import Correspondence.UniqueShared

#print axioms Dada.Unique.Typing.normalization_correct
#print axioms Dada.Unique.Typing.expression_soundness
#print axioms Dada.Unique.Typing.ConfigurationTyped.progress
#print axioms Dada.Unique.Typing.ConfigurationTyped.preservation
#print axioms Dada.Unique.Typing.program_safety
#print axioms Dada.Unique.Unpacking.Step.preserves_wellFormed
#print axioms Dada.Shared.WellFormed.path_mode_exclusive
#print axioms Dada.Shared.Typing.expression_soundness
#print axioms Dada.Shared.Typing.ConfigurationTyped.progress
#print axioms Dada.Shared.Typing.ConfigurationTyped.preservation
#print axioms Dada.Shared.Typing.program_safety
#print axioms Dada.Shared.Unpacking.Step.preserves_wellFormed
#print axioms Dada.Correspondence.step_correspondence
#print axioms Dada.Correspondence.steps_correspondence
#print axioms Dada.Correspondence.boundary_correspondence

#print axioms Dada.Correspondence.Typing.given_fragment

#print axioms Dada.Shared.Eval.preserves_kinds
#print axioms Dada.Shared.Steps.wellFormed_from_initial
