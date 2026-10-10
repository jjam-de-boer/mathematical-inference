import Thesis.CausalTransport.ActivePathBoundary
import Thesis.CausalTransport.HedgeChannelPathInputs

namespace Thesis
namespace Causality
namespace HedgeChannelEnvironmentInstallation

open PathSpecification Probability FiniteBooleanInteraction

/-!
# The installed path phase has the actual endpoint/collider character

`HedgeChannelPathInputs` installs the kept incoming parents and original
reserved roots of the actual path and reduces its entire head phase to a
computed observed boundary.  `ActivePathBoundary` identifies that boundary
from list simplicity and actual DAG adjacency, without balance premises.

This one-way bridge combines those two results.  Every cube point, including
all assignments of the original reserved inputs, satisfies the endpoint and
internal-collider character identity.  The observed source's first edge need
not be incoming for this conservation law; that back-door constraint is
required later to construct a supported direction with one odd source row.

The collider bits have not yet been routed to conditioning evidence here.
Actual normalized activation traces must be installed and combined with the
path, and every mandatory Small row must still be integrated.  Consequently
this theorem is not a universal conditional terminal countermodel theorem.
-/

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S} {m : GraphMutilation S}
  {given : NodeSet S} {source target : Fin S.count}

namespace LinearSignal

/-- Whole-cube conservation for the actual installed path-head interaction:
the two distinct observed endpoints XOR the actual internal collider rows.
Reserved inputs cancel in the installed signal, and the graph boundary is
proved from the supplied path rather than supplied as a matching flag. -/
theorem ofActivePath_forestPhase_endpointCollider
    (path : ActivePath graph m given (.observed source) (.observed target)) (distinct : source ≠ target)
    (point : Cube graph) :
    ((ofActivePath path).forestPhase (ActivePathInput.headRows graph m path.nodes)).value point =
      (maskPhase _ (cubeMask graph (ActivePathInput.endpointColliderBoundary graph m path.nodes source target))).value point := by
  rw [ofActivePath_forestPhase, ActivePathInput.observedBoundary_eq_endpointColliderBoundary path distinct]

end LinearSignal
end HedgeChannelEnvironmentInstallation
end Causality
end Thesis
