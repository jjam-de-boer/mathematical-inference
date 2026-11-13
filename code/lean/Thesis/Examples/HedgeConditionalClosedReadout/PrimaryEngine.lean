import Thesis.Examples.HedgeConditionalClosedReadout.Graph

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeConditionalClosedReentry

open Probability
open CurrentKernelFailureExtraction (partitionGraph)

/-!
# Engine checks for the internal-conditioner closed-readout query

The nonexchange, joint-failure and conditional-failure assertions below
concern the first original query. The local Boolean failure flag is the
unchanged private helper, not a supplied result for either algorithm.

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

theorem no_exchange : (conditionalExchangeStep? graph query).isNone = true := by decide +kernel
theorem joint_program_failed : failed (identifyJointKernel graph query.jointNumerator) = true := by decide +kernel
theorem conditional_program_failed : failed (identifyConditionalKernel graph query) = true := by decide +kernel
end HedgeConditionalClosedReentry
end Examples
end Causality
end Thesis
