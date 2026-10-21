import Thesis.Examples.HedgeConditionalClosedReadout.Graph

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeConditionalClosedReentry

open Probability
open CurrentKernelFailureExtraction (partitionGraph)

/-!
# Engine checks for the earlier-conditioner closed-readout query

These are the corresponding three executable assertions for the second
original query. The identical private Boolean helper is local to this module;
its visibility and body do not become a new public identification API.

The original entry point `Examples.HedgeConditionalClosedReadout` still
imports these checks and constructs the same semantic countermodels. Every
original statement and proof body is retained, with no omitted finite test
and no increase to the local resource limits.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

private def failed (result : IdentificationOutcome signature) : Bool :=
  match result with
  | .failed _ => true
  | _ => false

theorem earlier_no_exchange : (conditionalExchangeStep? graph earlierQuery).isNone = true := by decide +kernel
theorem earlier_joint_program_failed : failed (identifyJointKernel graph earlierQuery.jointNumerator) = true := by decide +kernel
theorem earlier_conditional_program_failed : failed (identifyConditionalKernel graph earlierQuery) = true := by decide +kernel

end HedgeConditionalClosedReentry
end Examples
end Causality
end Thesis
