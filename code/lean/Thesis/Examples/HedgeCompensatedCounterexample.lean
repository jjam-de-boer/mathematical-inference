import Thesis.CausalTransport.HedgeCompensatedCounterexample
import Thesis.Examples.HedgeCompensatedConservation

namespace Thesis
namespace Causality
namespace Examples

open Probability

/-!
# Actual positive countermodels beyond the kept-sink readout case

The first example integrates the four real fresh factors of the existing
three-value re-entry chain.  Its internal route vertex has a retained kept
child, so the old sink-only constructor cannot discharge this fixture.
The new counterexample uses exactly the already checked compensated models,
not a different model pair whose root signal happens to be separated.

The second example retains the original composite action of the checked
three-node hedge.  Both examples inhabit `CounterexampleIn` for the original
full outcome kernel and derive semantic non-identifiability.  They are not
just parity-signal comparisons or countermodels for substituted root queries.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace HedgeCompensatedReentry

open HedgeCarrierReentryReplay (signature graph rich witness query internalNode outcomeNode noise)

private theorem counterexample_allowed : forall node, witness.rootReadoutNodes node = true ->
    witness.small node = true ∨ witness.large node = false := by decide +kernel

private theorem counterexample_noise_positive : forall node, witness.smallOutcomeFlowNodes node = true ->
    forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit) := by
  intro _node _selected bit
  cases bit <;> decide +kernel

private theorem counterexample_noise_bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
    FiniteProbRecord.eventMass noise.atoms id + 1 := by decide +kernel

/-- This responding internal pivot is genuinely outside the older
kept-sink hypothesis, while the compensated countermodel covers it. -/
theorem routed_internal_has_kept_child : witness.rootReadoutNodes internalNode = true ∧
    witness.child internalNode = some outcomeNode := by decide +kernel

noncomputable def counterexample : CounterexampleIn (GraphModelClass.positive graph) query :=
  witness.positiveCounterexampleOfCarrierFlowReadoutPlan rich (fun _node => noise) counterexample_allowed
    counterexample_noise_positive (fun _node => 1) (fun _node _selected => Nat.zero_lt_one)
    (fun _node _selected => counterexample_noise_bias)

/-- Probability integration concerns the same large compensated SCM as
the earlier pointwise, support, compatibility, and observational checks. -/
theorem counterexample_left_is_actual : counterexample.left = left := rfl

/-- The nested endpoint is likewise the exact previously checked model. -/
theorem counterexample_right_is_actual : counterexample.right = right := rfl

theorem query_not_identifiable : Not ((GraphModelClass.positive graph).identifiable query) :=
  counterexample.not_identifiable

end HedgeCompensatedReentry

namespace HedgeCompensatedCompositeAction

open HedgeWeightedTernaryIntervention (signature graph rich query)

noncomputable def counterexample : CounterexampleIn (GraphModelClass.positive graph) query :=
  witness.positiveCounterexampleOfSmallOrOutsideCarrierFlow rich (by decide +kernel)

/-- The constructor retains the composite action and original outcome;
the intervened non-sink from `action_has_non_sink` is not removed. -/
theorem query_not_identifiable : Not ((GraphModelClass.positive graph).identifiable query) :=
  counterexample.not_identifiable

end HedgeCompensatedCompositeAction
end Examples
end Causality
end Thesis
