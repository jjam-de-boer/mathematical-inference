import Thesis.Examples.HedgeConditionalReadout.Graph

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeConditionalMergedReadout

/-!
# The concrete conditional readout has no exchange step

This finite rule-2 check retains the nonempty original conditioner.
It is checked separately from joint engine reduction so each independent
graph computation has its own unchanged local resource limit.

Every original statement and proof body is retained. The original
`Examples.HedgeConditionalReadout` entry point still imports these checks
before constructing its semantic countermodels; the full audit checks all
of them under the same constructive axiom policy.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem no_exchange : conditionalExchangeStep? graph query = none := rfl

end HedgeConditionalMergedReadout
end Examples
end Causality
end Thesis
