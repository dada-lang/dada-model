import Unique.RootedChecks
import Shared.RootedChecks
import Shared.RootedPathChecks
import Assignment.ExecutionChecks
import Correspondence.DestructorsAssignment
-- Executed by scripts/check-assumptions.sh after rebuilding all dependencies.
import Unique.FrameChecks
import Shared.FrameChecks
import Shared.FrameInvariants
import Correspondence.UniqueSharedFrames
import Correspondence.SharedFunctionsFrames
import Destructors.ExecutionChecks
import Correspondence.FunctionsDestructors
import Functions.Checks
import Functions.SafetyChecks
import Correspondence.SharedFunctions
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

#print axioms Dada.Functions.Configuration.collect_eq_self
#print axioms Dada.Functions.terminal_heap_empty
#print axioms Dada.Functions.finished_no_step
#print axioms Dada.Functions.call_arity
#print axioms Dada.Correspondence.SharedFunctions.step_correspondence
#print axioms Dada.Correspondence.SharedFunctions.steps_backward
#print axioms Dada.Correspondence.SharedFunctions.typing_correspondence
#print axioms Dada.Correspondence.SharedFunctions.finished_correspondence
#print axioms Dada.Correspondence.SharedFunctions.stuck_correspondence
#print axioms Dada.Functions.Checks.identity_execution
#print axioms Dada.Functions.Checks.shared_execution
#print axioms Dada.Functions.Checks.method_execution
#print axioms Dada.Functions.Checks.leave_execution
#print axioms Dada.Functions.Checks.nested_execution
#print axioms Dada.Functions.Checks.recursive_step

#print axioms Dada.Unique.Framed.program_safety
#print axioms Dada.Shared.Framed.program_safety
#print axioms Dada.Unique.Framed.completion
#print axioms Dada.Shared.Framed.completion
#print axioms Dada.Shared.Framed.base_soundness
#print axioms Dada.Correspondence.Framed.collect_correspondence
#print axioms Dada.Correspondence.Framed.base_step_correspondence
#print axioms Dada.Correspondence.Framed.pattern_step_correspondence
#print axioms Dada.Correspondence.Framed.base_boundary_correspondence
#print axioms Dada.Correspondence.SharedFunctions.framed_step_correspondence
#print axioms Dada.Correspondence.SharedFunctions.framed_steps_backward
#print axioms Dada.Correspondence.SharedFunctions.framed_finished_correspondence
#print axioms Dada.Correspondence.SharedFunctions.framed_stuck_correspondence

#print axioms Dada.Functions.ConfigurationTyped.progress
#print axioms Dada.Functions.ConfigurationTyped.preservation
#print axioms Dada.Functions.program_safety
#print axioms Dada.Functions.ConfigurationTyped.ownership
#print axioms Dada.Functions.ConfigurationTyped.finished_heap_empty
#print axioms Dada.Shared.Typing.Realizes.collect_pending
#print axioms Dada.Shared.Typing.BindingTyped.preserves_realization_pending

#print axioms Dada.Unique.Framed.ConfigurationTyped.progress
#print axioms Dada.Unique.Framed.ConfigurationTyped.preservation
#print axioms Dada.Shared.Framed.ConfigurationTyped.progress
#print axioms Dada.Shared.Framed.ConfigurationTyped.preservation

#print axioms Dada.Destructors.ConfigurationTyped.progress
#print axioms Dada.Destructors.ConfigurationTyped.preservation
#print axioms Dada.Destructors.RawStep.sound
#print axioms Dada.Destructors.program_safety
#print axioms Dada.Destructors.ConfigurationTyped.finished_heap_empty
#print axioms Dada.Destructors.collectPending_retains_classes
#print axioms Dada.Destructors.Checks.wrapper_execution
#print axioms Dada.Destructors.Checks.recursive_prefix
#print axioms Dada.Correspondence.FunctionsDestructors.step_correspondence
#print axioms Dada.Correspondence.FunctionsDestructors.steps_backward

#print axioms Dada.Assignment.store_preserves_bindings
#print axioms Dada.Assignment.store_wellFormed
#print axioms Dada.Assignment.Write.objectKeys
#print axioms Dada.Assignment.Checks.refill_raw
#print axioms Dada.Correspondence.DestructorsAssignment.step_forward

#print axioms Dada.Unique.Typing.readPath_no_cycle
#print axioms Dada.Unique.Take.preserves_pending
#print axioms Dada.Shared.Give.preserves_pending
#print axioms Dada.Shared.Typing.Route.unique
