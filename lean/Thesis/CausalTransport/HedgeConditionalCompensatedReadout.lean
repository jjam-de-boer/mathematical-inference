import Thesis.CausalTransport.HedgeReadoutPreservation
import Thesis.CausalTransport.HedgeCompensatedCounterexample
import Thesis.CausalTransport.ConditionalFailureExtraction

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Conditional countermodels with responding readouts and protected conditioners

The compensated joint constructor permits internal small-forest pivots and
responding descendants.  Conditional separation additionally requires that
the denominator agree in those same new models; a separated numerator alone
does not establish non-identifiability of its normalization.

`HedgeReadoutPreservation` supplies a local invariant for every row outside
the installed mask.  It proves full-value and kernel preservation on both
carrier sides under arbitrary interventions.  Its protected set includes
outer-only forest vertices, whose mechanisms may have retained parents,
as well as unmodified outside-large vertices.  Thus the conditioner need not
lie outside the large forest, and readout pivots need not be kept sinks.

The base denominator agrees by the general root-omitted marginal theorem.
The protected set omits every small root automatically, so no denominator
identifiability premise or specially chosen model pair is needed.  The
checked chain argument then refutes the original conditional in the actual
compensated models.  An arbitrary-depth IDC failure can transport this
terminal counterexample back along its already extracted exchange trace.

Conditioners on installed rows and outer-only route updates remain open
general cases.  These constructors retain their geometric premises and do
not claim to inhabit the universal conditional field of published completeness.
-/

/-- Construct the original conditional counterexample in the compensated
joint pair, with separately supported biased noise at every installed row.
Only route permission and protection of the conditioner are supplied: no
kept-sink, denominator equality, observed-law equality, parity identity,
denominator identifiability, or semantic separation is assumed. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfCarrierFlowOfConditionProtectedWithNoise
    {G : ObservedGraph S} {query : ConditionalKernelQuery S}
    (w : HedgeWitness G query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false)
    (conditionProtected : NodeSet.Subset query.condition w.carrierFlowProtectedNodes)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (noisePositive : forall node, w.smallOutcomeFlowNodes node = true ->
      forall bit, (noise node).EventPositive (FiniteProbRecord.singletonEvent bit))
    (gap : Fin S.count -> Nat) (gapPositive : forall node, w.smallOutcomeFlowNodes node = true -> 0 < gap node)
    (bias : forall node, w.smallOutcomeFlowNodes node = true ->
      FiniteProbRecord.eventMass (noise node).atoms (fun bit => !bit) =
        FiniteProbRecord.eventMass (noise node).atoms id + gap node) :
    ConditionalCounterexampleIn (GraphModelClass.positive G) query := by
  let joint := w.positiveCounterexampleOfCarrierFlowReadoutPlan rich noise allowed noisePositive gap gapPositive bias
  have denominator : query.jointDenominator.ValueEquivalent joint.left joint.right :=
    w.carrierDefectParityModels_carrierFlowReadoutPlan_valueEquivalent_of_protected rich noise allowed
      query.jointDenominator conditionProtected
  exact ConditionalCounterexampleIn.ofJointNumeratorOfDenominatorEquivalent
    (C := GraphModelClass.positive G) (fun member => member.2) query joint denominator

/-- The canonical supported stay-biased coin discharges all noise data.
The conditioner may include protected outer-only forest vertices, including
free rows with responding kept parents.  It must still avoid installed rows. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfCarrierFlowOfConditionProtected
    {G : ObservedGraph S} {query : ConditionalKernelQuery S}
    (w : HedgeWitness G query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false)
    (conditionProtected : NodeSet.Subset query.condition w.carrierFlowProtectedNodes) :
    ConditionalCounterexampleIn (GraphModelClass.positive G) query := by
  let joint := w.positiveCounterexampleOfSmallOrOutsideCarrierFlow rich allowed
  have denominator : query.jointDenominator.ValueEquivalent joint.left joint.right :=
    w.carrierDefectParityModels_carrierFlowReadoutPlan_valueEquivalent_of_protected rich
      (fun _node => FiniteProbRecord.biasedFlip 1 1 (by decide)) allowed query.jointDenominator conditionProtected
  exact ConditionalCounterexampleIn.ofJointNumeratorOfDenominatorEquivalent
    (C := GraphModelClass.positive G) (fun member => member.2) query joint denominator

/-- Close the actual original IDC failure at any exchange depth when its
extracted terminal satisfies these geometric premises.  The countermodel is
constructed for the terminal's exact numerator hedge and denominator before
the certified trace restores the original query; no new nested-fail unpacker
or assumed success of an exchange is needed. -/
noncomputable def ConditionalKernelFailure.counterexampleOfProtectedCarrierFlowTerminal
    {G : ObservedGraph S} {query : ConditionalKernelQuery S} {fail : IdentificationFail S}
    (failure : ConditionalKernelFailure G query fail) (rich : ObservedSignature.ValueRich S)
    (allowed : forall node, failure.hedge.witness.rootReadoutNodes node = true ->
      failure.hedge.witness.small node = true ∨ failure.hedge.witness.large node = false)
    (conditionProtected : NodeSet.Subset failure.terminal.condition failure.hedge.witness.carrierFlowProtectedNodes) :
    ConditionalCounterexampleIn (GraphModelClass.positive G) query :=
  failure.counterexampleOfTerminal (C := GraphModelClass.positive G) (fun member => member.2)
    (failure.hedge.witness.positiveConditionalCounterexampleOfCarrierFlowOfConditionProtected rich allowed conditionProtected)

end Causality
end Thesis
