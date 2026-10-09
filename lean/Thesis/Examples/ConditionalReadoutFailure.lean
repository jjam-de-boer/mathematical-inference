import Thesis.Examples.ConditionalReadout
import Thesis.CausalTransport.ConditionalCounterexampleFailure

namespace Thesis
namespace Causality
namespace Examples
namespace ConditionalReadoutRegression

/-!
# Actual IDC failure of the independently constructed readout countermodel

This small bridge keeps success/termination compilation separate from the
SCM construction regression.  The theorem concerns the actual public entry
point on the original query, but does not normalize its full graph decision
or claim an exact identity for its recorded forest sets.  The companion
`ConditionalReadoutPaths` contains those stronger computational comparisons.
-/

set_option maxRecDepth 2000 in
/-- Genuine failure of the original public IDC invocation.  The independent
semantic countermodel and general success/termination theorems rule out every
non-failure output, without recomputing a separation matrix in this proof.
The shared named failure tag avoids elaborating a new concrete program match,
and the opaque non-identifiability theorem keeps the large SCM structure out
of the semantic bridge. -/
theorem original_query_failed :
    (identifyConditionalKernel graph target).isFailed = true :=
  identifyConditionalKernel_failed_of_not_identifiable
    (S := signature) (graph := graph) (C := GraphModelClass.positive graph)
    (fun member => member.2) target original_query_not_identifiable

end ConditionalReadoutRegression
end Examples
end Causality
end Thesis
