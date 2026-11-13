import Thesis.CausalTransport.HedgeChannelMarginal
import Thesis.Examples.ConditionalCollider

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeChannelMarginal

/-!
# A genuine irreducible conditional outside the flow-balance family

Reuse the existing three-valued collider fixture `U -> R <- A`, `A <-> R`,
with the original query `P(U | do(A), R)`.  Its corrected conditional program
fails, no conditioner can be exchanged, and the existing collider construction
already supplies a positive original-query counterexample.

For the unrestricted channel pair's default numerator outcome flow, the
small forest is the conditioned root `R`.  That flow stops at `R`, because
the joint numerator inspects both `U` and `R`.  Consequently every actual
flow sink is inspected by the conditioner.  The general conservation
obstruction rules out *every* outcome-flow balance direction, not just a
singleton flip, one search policy, or one finite candidate enumeration.

This is a limitation of the stated marginal-balancing family, not evidence
that the conditional is identifiable or that a countermodel cannot exist.
The existing collider counterexample proves the opposite.  A universal
conditional-completeness argument must handle this alternative geometry;
it must not assume that the default channel pair always admits a matched
conditioning marginal or keep searching for a direction proved impossible.
-/

open ConditionalColliderRegression

/-- The default composed numerator flow's entire boundary is the original
conditioner.  Only this three-node graph calculation is reduced; no complete
channel-model probability or augmented latent support is enumerated. -/
theorem actual_flowSinks_are_condition :
    keptSinks witness.smallOutcomeFlowNodes witness.smallOutcomeFlowSuccessor = query.condition :=
  (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)

/-- There is no balance direction for this actual supplied hedge and
conditioner.  Conservation proves the general impossibility, so the result
does not depend on exhausting a chosen bounded search or candidate family. -/
theorem no_balanceDirection :
    ¬ Nonempty (Causality.HedgeChannelInstallation.OutcomeFlowBalanceDirection witness query.condition) := by
  apply Causality.HedgeChannelInstallation.OutcomeFlowBalanceDirection.not_nonempty_of_inspected_contains_sinks
  intro child selected
  rw [actual_flowSinks_are_condition] at selected
  exact selected

/-- The balance obstruction occurs at a real irreducible failed query
which has a positive original-alphabet conditional counterexample.  The
contradistinction prevents a proof-family limit from being confused with an
identifiability theorem or with failure of the full requested objective. -/
theorem irreducible_failure_without_balanceDirection :
    conditionalExchangeStep? graph query = none ∧
    identifyConditionalKernel graph query = .failed ⟨large, small⟩ ∧
    ¬ Nonempty (Causality.HedgeChannelInstallation.OutcomeFlowBalanceDirection witness query.condition) ∧
    ¬ (GraphModelClass.positive graph).conditionalIdentifiable query :=
  ⟨no_exchange, original_query_failed, no_balanceDirection, original_query_not_identifiable⟩

end HedgeChannelMarginal
end Examples
end Causality
end Thesis
