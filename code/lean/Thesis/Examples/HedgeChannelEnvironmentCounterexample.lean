import Thesis.Examples.HedgeChannelEnvironment
import Thesis.CausalTransport.HedgeChannelEnvironmentFactorization

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeChannelEnvironment

open Probability
open HedgeChannelLatentBoundary
open HedgeChannelEnvironmentInstallation

/-!
# Actual countermodel assembly for the shared-input gap fixture

The companion finite module computes only the four independent environment
assignments and leaves the large main-prior mass symbolic.  Here its complete
cross-product inequality is connected to actual SCM kernel cells and the
unchanged three-valued query through the general semantic constructor.
The background-weighted criterion is checked against that independently
computed gap as well, and now supplies the countermodel assembly.  This
regression does not recompute the large source support or assume a new gap.

Keeping assembly separate permits the finite calculation and its semantic
consequence to be checked in independent small compiler sessions.  It adds
no hypothesis, selected reference or different source pair to the proof.
-/

/-- Spell the finite module's target and cylinder arguments directly as
the original query operations.  This prevents a checker from reducing the
entire event integral just to compare two names for the same argument. -/
theorem kernel_cross_separated :
    leftEventNumerator witness rich smallSignal backgroundSignal
        (query.binary.operationKernel.intervention sourceReference)
        (query.binary.operationKernel.numeratorEvent sourceReference) *
      rightEventNumerator witness smallSignal backgroundSignal
        (query.binary.operationKernel.intervention sourceReference)
        (query.binary.operationKernel.conditionEvent sourceReference) ≠
    rightEventNumerator witness smallSignal backgroundSignal
        (query.binary.operationKernel.intervention sourceReference)
        (query.binary.operationKernel.numeratorEvent sourceReference) *
      leftEventNumerator witness rich smallSignal backgroundSignal
        (query.binary.operationKernel.intervention sourceReference)
        (query.binary.operationKernel.conditionEvent sourceReference) := cross_separated

/-- The new complete background/interaction criterion detects the already
proved genuine latent-entry gap.  Both integrals include every environment;
no claim about a conditional at one frozen environment is used here. -/
theorem background_change_separated :
    interactionEventSum witness smallSignal backgroundSignal
        (query.binary.operationKernel.intervention sourceReference)
        (query.binary.operationKernel.numeratorEvent sourceReference) *
      backgroundEventSum witness backgroundSignal
        (query.binary.operationKernel.intervention sourceReference)
        (query.binary.operationKernel.conditionEvent sourceReference) ≠
    backgroundEventSum witness backgroundSignal
        (query.binary.operationKernel.intervention sourceReference)
        (query.binary.operationKernel.numeratorEvent sourceReference) *
      interactionEventSum witness smallSignal backgroundSignal
        (query.binary.operationKernel.intervention sourceReference)
        (query.binary.operationKernel.conditionEvent sourceReference) := by
  intro balanced
  apply kernel_cross_separated
  exact (event_cross_eq_iff_background_balanced_of_action witness rich smallSignal backgroundSignal
    (query.binary.operationKernel.intervention sourceReference) false (by rfl)
    (query.binary.operationKernel.numeratorEvent sourceReference)
    (query.binary.operationKernel.conditionEvent sourceReference)).mpr balanced

/-- The widened models' actual Boolean kernel cells are separated, rather
than just one proposed unnormalized monomial being nonzero. -/
theorem source_cell_separated : Not (Nonempty (ProbabilityResult.Equivalent
    (query.binary.sourceTerm.denote (HedgeChannelEnvironmentInstallation.leftModel witness rich smallSignal backgroundSignal) sourceReference)
    (query.binary.sourceTerm.denote (HedgeChannelEnvironmentInstallation.rightModel witness smallSignal backgroundSignal) sourceReference))) :=
  binary_conditionalCell_separated_of_cross (S := signature) (G := graph) (query := query)
    witness rich smallSignal backgroundSignal sourceReference kernel_cross_separated

/-- A positive countermodel pair on the unchanged original three-valued
signature, from this widened channel construction itself.  Every original
label has support and no observed arrow or query coordinate is altered. -/
noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  conditionalCounterexampleOfBackgroundChange (S := signature) (G := graph) (query := query)
    witness rich smallSignal backgroundSignal sourceReference background_change_separated

theorem query_not_identifiable : ¬ (GraphModelClass.positive graph).conditionalIdentifiable query :=
  counterexample.not_identifiable

end HedgeChannelEnvironment
end Examples
end Causality
end Thesis
