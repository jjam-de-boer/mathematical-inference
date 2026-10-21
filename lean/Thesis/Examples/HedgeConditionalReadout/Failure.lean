import Thesis.Examples.HedgeConditionalReadout.Exchange

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeConditionalMergedReadout

/-!
# Actual joint and conditional failures for the merged readout

These are the original executable engine equations on the six-node graph,
including the exact large/small failure coordinates. Separating these checks
from routing proofs does not replace program evaluation by a supplied result.

Every original statement and proof body is retained. The original
`Examples.HedgeConditionalReadout` entry point still imports these checks
before constructing its semantic countermodels; the full audit checks all
of them under the same constructive axiom policy.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

private def computedFailure : IdentificationFail signature :=
  match identifyJointKernel graph query.jointNumerator with
  | .failed fail => fail
  | _ => ⟨NodeSet.empty, NodeSet.empty⟩

/-- The failure is on the confounded three-node component, not the entire
six-node numerator host.  Its small forest consists of both roots. -/
theorem joint_failed : identifyJointKernel graph query.jointNumerator = .failed ⟨forestHost, rootMask⟩ := by
  have failed : identifyJointKernel graph query.jointNumerator = .failed computedFailure := rfl
  have large : computedFailure.remaining = forestHost :=
    (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)
  have small : computedFailure.free = rootMask :=
    (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)
  have coordinates : computedFailure = ⟨forestHost, rootMask⟩ := by
    cases record : computedFailure with
    | mk remaining free =>
        rw [record] at large small
        cases large
        cases small
        rfl
  exact failed.trans (congrArg IdentificationOutcome.failed coordinates)

theorem conditional_failed : identifyConditionalKernel graph query = .failed ⟨forestHost, rootMask⟩ := by
  simpa only [identifyConditionalKernel, identifyConditionalKernelFuel, no_exchange] using joint_failed

end HedgeConditionalMergedReadout
end Examples
end Causality
end Thesis
