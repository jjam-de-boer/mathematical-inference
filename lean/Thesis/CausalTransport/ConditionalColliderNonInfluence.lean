import Thesis.CausalTransport.ConditionalCollider
import Thesis.Causality.PrivateNoiseNonInfluence

namespace Thesis
namespace Causality

open Probability

/-!
# Route readiness of the actual observed-parent collider

The fair parent and conditioned collider precede the final directed readouts
as *updates*, but need not both precede every readout destination in the
signature's topological order.  Non-influence must therefore be derived from
their actual mechanisms, rather than imposed as an extra order assumption.

The general readout lemma retains the complete old observed value, including
background labels outside the two distinguished bits.  Ignoring the updated
coordinate's old bit is not sufficient to ignore its old full value.  The
base non-influence proof controls that background; the separate parent-signal
proof controls the only newly introduced observed dependence.

The collider reads only its displayed fair parent.  It consequently preserves
non-influence of every other initially ignored vertex, even if an ambient edge
from that vertex to the collider is permitted.  This is readiness for a later
semantic construction, not an assertion that arbitrary base vertices are
ignored or that mixed active paths have already been implemented.
-/

variable {S : ObservedSignature.{0}}

/-- A parent signal which respects agreement away from an ignored coordinate
cannot introduce dependence on that coordinate.  The old full-value carrier
is controlled by the base model's non-influence, in either injection mode. -/
theorem FiniteLatentSCM.withHedgeReadout_otherMechanismsIgnore_of_parentSignal
    (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (pivot node : Fin S.count) (noise : FiniteProbRecord Bool)
    (injectOld : Bool) (parentSignal : S.ParentValues pivot -> Bool)
    (ignored : base.OtherMechanismsIgnore node)
    (signalIgnores : forall (first second : S.ParentValues pivot),
      (forall parent (edge : S.directed parent pivot = true), parent ≠ node ->
        first parent edge = second parent edge) -> parentSignal first = parentSignal second) :
    (base.withHedgeReadout rich pivot noise injectOld parentSignal).OtherMechanismsIgnore node := by
  apply base.withPrivateBooleanNoise_otherMechanismsIgnore_of_replacement pivot node noise _ ignored
  intro different first second inputs bit agree
  have old := ignored pivot different first second inputs agree
  have signal := signalIgnores first second agree
  simp only [hedgeNoisyReadout, old, signal]

namespace ConditionalCollider

/-- The actual two-step collider keeps every initially ignored coordinate
other than its displayed fair parent ignored.  There is no requirement that
the collider lie before that coordinate or lack an ambient incoming edge. -/
theorem model_otherMechanismsIgnore (base : ExactModel S)
    (rich : ObservedSignature.ValueRich S) (parent child : Fin S.count)
    (edge : S.directed parent child = true) (noise : FiniteProbRecord Bool)
    (node : Fin S.count) (different : parent ≠ node)
    (ignored : base.OtherMechanismsIgnore node) :
    (model base rich parent child edge noise).OtherMechanismsIgnore node := by
  have masked := base.withHedgeReadout_otherMechanismsIgnore_of_parentSignal rich parent node
    ColliderChannel.fairMask false (fun _ => false) ignored (fun _ _ _ => rfl)
  apply (maskModel base rich parent).withHedgeReadout_otherMechanismsIgnore_of_parentSignal
    rich child node noise true (parentSignal rich parent child edge) masked
  intro first second agree
  exact congrArg (hedgeIsSecond rich parent) (agree parent edge different)

end ConditionalCollider
end Causality
end Thesis
