import Thesis.Examples.ConditionalReadout
import Thesis.CausalTransport.ConditionalFailurePaths

namespace Thesis
namespace Causality
namespace Examples
namespace ConditionalReadoutRegression
namespace Paths

/-!
# Optional exact IDC and searched-path checks for the readout fixture

The companion semantic fixture constructs the original-query countermodels
and derives actual IDC failure from soundness and termination.  This separate
computational regression retains the stronger exact fail-record comparison,
exhausted exchange search, and actual searched back-door path codes.

These checks can require substantially more kernel memory because they reduce
the expanded-latent separation computation.  They are deliberately separate
from the small semantic fixture and are not imported by the top-level smoke
test.  No semantic countermodel theorem relies on their computation.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem selected_endpoints : geometry.parent = parent ∧ geometry.endpoint = outcome := by decide +kernel

theorem directed_route_codes : geometry.route.destinations.map Fin.val = [3, 4] := by decide +kernel

private def failureTest (result : IdentificationOutcome signature) : Bool :=
  match result with
  | .failed fail => NodeSet.equal fail.remaining large && NodeSet.equal fail.free small
  | _ => false

private theorem failureOfTest (result : IdentificationOutcome signature) (checked : failureTest result = true) :
    result = .failed ⟨large, small⟩ := by
  cases result with
  | identified _ => cases checked
  | unfinished => cases checked
  | failed fail =>
      have parts := Bool.and_eq_true_iff.mp checked
      have largeEq := (NodeSet.equal_eq_true_iff _ _).mp parts.1
      have smallEq := (NodeSet.equal_eq_true_iff _ _).mp parts.2
      cases fail with
      | mk remaining free => cases largeEq; cases smallEq; rfl

theorem no_exchange : conditionalExchangeStep? graph target = none := by decide +kernel

theorem original_query_failed : identifyConditionalKernel graph target = .failed ⟨large, small⟩ :=
  failureOfTest _ (by decide +kernel)

def backdoor : ConditionalBackdoorPath graph target root :=
  .ofNoExchange graph target no_exchange root (by decide +kernel)

theorem backdoor_path_codes : backdoor.path.nodes.map SeparationNode.code = [2, 0, 3, 4] := by decide +kernel

end Paths
end ConditionalReadoutRegression
end Examples
end Causality
end Thesis
