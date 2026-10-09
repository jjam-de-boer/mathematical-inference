import Thesis.CausalTransport.HedgeChannelEnvironmentInstallation
import Thesis.CausalTransport.HedgeChannelConditionalCell
import Thesis.CausalTransport.ValueRefinementConditionalCounterexample

namespace Thesis
namespace Causality
namespace HedgeChannelEnvironmentInstallation

open Probability
open HedgeChannelInstallation (channelCount leftTables rightTables capacities_equal)

/-!
# Conditional countermodels from the complete shared-input environment sum

The widened hedge pair is compatible, fully positive and observationally
equal.  Conditional separation needs more: compare its full numerator and
conditioning cylinders after integrating every independent environment.
The two named natural masses below are those actual complete integrals.

Their equality with the enlarged model's literal event numerators follows
from the checked prior decomposition and frozen-centre identities.  The
shared conditional-cell theorem then makes a cross-product inequality a
genuine source-kernel gap, even when both conditioning masses change.

The original-alphabet constructor transports the same supplied source cell
through explicit coordinate recoding and private label refinement.  It
does not search the enormous response-function source space, restrict the
original outcome or conditioner, or add a common latent switching source.
Applications still have to construct legal local signals and prove their
complete integrated cross-product inequality.  Universal terminal coverage
is not asserted by this arithmetic-to-countermodel bridge.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S} {q : JointKernelQuery S}

/-- The complete left event numerator after summing every actual independent
environment.  The inner integral retains the entire ordinary main prior. -/
def leftEventNumerator (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal G) (target : Fin S.count -> Option Bool)
    (event : Event S.binary.Assignment) : Nat :=
  ((PairRootChannels.Environment.enumeration G.binary).map (fun environment =>
    HedgeChannelTable.eventNumerator G (channelCount w) (leftTables w)
      (HedgeChannelInstallation.leftSignals w rich (frozenParentSignal smallSignal environment)
        (frozenParentSignal backgroundSignal environment)) target event)).sum

/-- The complete right event numerator on the very same environment support.
This is a natural probability mass, not a signed expansion coefficient. -/
def rightEventNumerator (w : HedgeWitness G q)
    (smallSignal backgroundSignal : ParentSignal G) (target : Fin S.count -> Option Bool)
    (event : Event S.binary.Assignment) : Nat :=
  ((PairRootChannels.Environment.enumeration G.binary).map (fun environment =>
    HedgeChannelTable.eventNumerator G (channelCount w) (rightTables w)
      (HedgeChannelInstallation.rightSignals w (frozenParentSignal smallSignal environment)
        (frozenParentSignal backgroundSignal environment)) target event)).sum

/-- The named left sum is literally the actual enlarged model's event
numerator.  This identity precedes any claim about a normalized query gap. -/
theorem left_eventNumerator_eq (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal G) (target : Fin S.count -> Option Bool)
    (event : Event S.binary.Assignment) :
    HedgeChannelTable.eventNumerator G (channelCount w + 1) (HedgeChannelEnvironment.paddedTables (leftTables w))
        (HedgeChannelEnvironment.paddedSignals G (channelCount w) (leftSignals w rich smallSignal backgroundSignal)) target event =
      leftEventNumerator w rich smallSignal backgroundSignal target event := by
  rw [HedgeChannelEnvironment.eventNumerator_split]
  simp only [frozen_leftSignals, leftEventNumerator]

/-- The same literal identity holds for the right sum, with every full-
small/background interaction and every forced zero cell retained. -/
theorem right_eventNumerator_eq (w : HedgeWitness G q)
    (smallSignal backgroundSignal : ParentSignal G) (target : Fin S.count -> Option Bool)
    (event : Event S.binary.Assignment) :
    HedgeChannelTable.eventNumerator G (channelCount w + 1) (HedgeChannelEnvironment.paddedTables (rightTables w))
        (HedgeChannelEnvironment.paddedSignals G (channelCount w) (rightSignals w smallSignal backgroundSignal)) target event =
      rightEventNumerator w smallSignal backgroundSignal target event := by
  rw [HedgeChannelEnvironment.eventNumerator_split]
  simp only [frozen_rightSignals, rightEventNumerator]

variable {query : ConditionalKernelQuery S}

/-- A strict complete cross-product gap separates the actual source cell.
The independent environment is integrated before conditioning; agreement
of conditionals at every frozen environment is not substituted for this test. -/
theorem binary_conditionalCell_separated_of_cross
    (w : HedgeWitness G query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal G) (reference : S.binary.Assignment)
    (separated : leftEventNumerator w rich smallSignal backgroundSignal
          (query.binary.operationKernel.intervention reference) (query.binary.operationKernel.numeratorEvent reference) *
        rightEventNumerator w smallSignal backgroundSignal
          (query.binary.operationKernel.intervention reference) (query.binary.operationKernel.conditionEvent reference) ≠
      rightEventNumerator w smallSignal backgroundSignal
          (query.binary.operationKernel.intervention reference) (query.binary.operationKernel.numeratorEvent reference) *
        leftEventNumerator w rich smallSignal backgroundSignal
          (query.binary.operationKernel.intervention reference) (query.binary.operationKernel.conditionEvent reference)) :
    Not (Nonempty (ProbabilityResult.Equivalent (query.binary.sourceTerm.denote (leftModel w rich smallSignal backgroundSignal) reference)
      (query.binary.sourceTerm.denote (rightModel w smallSignal backgroundSignal) reference))) := by
  intro supplied
  have cross := (HedgeChannelTable.conditionalCell_equivalent_iff_cross G (channelCount w + 1)
    (HedgeChannelEnvironment.paddedTables (leftTables w)) (HedgeChannelEnvironment.paddedTables (rightTables w))
    (HedgeChannelEnvironment.paddedSignals G (channelCount w) (leftSignals w rich smallSignal backgroundSignal))
    (HedgeChannelEnvironment.paddedSignals G (channelCount w) (rightSignals w smallSignal backgroundSignal))
    query.binary.operationKernel reference).mp supplied
  rw [left_eventNumerator_eq, right_eventNumerator_eq, right_eventNumerator_eq, left_eventNumerator_eq] at cross
  exact separated cross

/-- Lift the widened family's actual separated source cell to the unchanged
full original alphabet.  All labels, action values and query coordinates
remain present; no matched conditioning marginal or extra observed node is
required.  A separating complete cross-product is still an application proof. -/
noncomputable def conditionalCounterexampleOfCross
    (w : HedgeWitness G query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal G) (reference : S.binary.Assignment)
    (separated : leftEventNumerator w rich smallSignal backgroundSignal
          (query.binary.operationKernel.intervention reference) (query.binary.operationKernel.numeratorEvent reference) *
        rightEventNumerator w smallSignal backgroundSignal
          (query.binary.operationKernel.intervention reference) (query.binary.operationKernel.conditionEvent reference) ≠
      rightEventNumerator w smallSignal backgroundSignal
          (query.binary.operationKernel.intervention reference) (query.binary.operationKernel.numeratorEvent reference) *
        leftEventNumerator w rich smallSignal backgroundSignal
          (query.binary.operationKernel.intervention reference) (query.binary.operationKernel.conditionEvent reference)) :
    ConditionalCounterexampleIn (GraphModelClass.positive G) query :=
  ObservedValueRefinement.positiveConditionalCounterexampleOfBinaryCell query rich
    (leftModel w rich smallSignal backgroundSignal) (rightModel w smallSignal backgroundSignal)
    (models_compatible w rich smallSignal backgroundSignal).1 (models_compatible w rich smallSignal backgroundSignal).2
    (models_positive w rich smallSignal backgroundSignal).1 (models_positive w rich smallSignal backgroundSignal).2
    (models_observationallyEquivalent w rich smallSignal backgroundSignal) reference
    (binary_conditionalCell_separated_of_cross w rich smallSignal backgroundSignal reference separated)

end HedgeChannelEnvironmentInstallation
end Causality
end Thesis
