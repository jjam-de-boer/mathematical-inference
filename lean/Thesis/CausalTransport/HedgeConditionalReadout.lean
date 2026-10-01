import Thesis.CausalTransport.HedgeReadoutPlan
import Thesis.CausalTransport.ConditionalFailureExtraction

namespace Thesis
namespace Causality

open Probability

/-!
# Positive conditional countermodels with routed common-root parity

A joint numerator counterexample does not automatically refute a conditional:
the interventional denominator could change in exactly the way that cancels
the numerator gap.  This module proves the required denominator equality for
the *same* positive models built by the canonical all-root readout plan.

The conditioner lies outside the original large forest and outside the
modified routing vertices.  Its kernel agrees in the original carrier pair,
and every installed private readout preserves it on each side separately.
The checked chain-rule constructor then converts numerator separation into
conditional separation without assuming denominator identifiability.

Common roots need not be original outcome coordinates: the real SCM routing
transports their parity to the numerator's queried sinks.  Any number of
roots, merging paths, multiple sinks, and full observed alphabets are allowed.
This is an integration boundary, not a dependency from the joint completeness
development back to soundness.  The remaining geometric premises are stated
explicitly.  The later `HedgeConditionalCompensatedReadout` constructor covers
small-forest re-entry with responding children and protected outer-only
conditioners by local mechanism closure.  Conditioners on installed rows and
outer-only route updates still require the general terminal argument.
-/

variable {S : ObservedSignature.{0}}

/-- A canonical routed conditional countermodel with independently specified
positive biased noise at every selected routing vertex.

Every route pivot must be a sink of the original kept forest map, as in the
joint constructor.  The conditioner must be disjoint from the large forest
and the route nodes.  It may nevertheless be a graphical descendant of the
queried outcome: the constructed off-forest mechanisms ignore their parents,
and the off-pivot preservation theorem concerns the actual mechanisms, not
an independence assertion about all models compatible with the graph.

All countermodel fields retain the same two SCMs.  In particular, the proof
does not replace the routed pair by the base pair when comparing denominators.
No supplied ordering, hand-written readout instructions, parity pullback,
observational equality, or semantic kernel gap is required. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfRootReadoutSinksOfConditionOutsideWithNoise
    {G : ObservedGraph S} {query : ConditionalKernelQuery S}
    (w : HedgeWitness G query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (sinks : forall node, w.rootReadoutNodes node = true -> w.child node = none)
    (conditionOutsideLarge : NodeSet.Disjoint query.condition w.large)
    (conditionOutsideRoutes : NodeSet.Disjoint query.condition w.rootReadoutNodes)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (noisePositive : forall node, w.rootReadoutNodes node = true ->
      forall bit, (noise node).EventPositive (FiniteProbRecord.singletonEvent bit))
    (biased : forall node, w.rootReadoutNodes node = true -> Exists fun gap =>
      0 < gap ∧ FiniteProbRecord.eventMass (noise node).atoms (fun bit => !bit) =
        FiniteProbRecord.eventMass (noise node).atoms id + gap) :
    ConditionalCounterexampleIn (GraphModelClass.positive G) query := by
  let plan := w.rootReadoutPlan noise
  let instructions := HedgeLinearReadoutPlan.readouts rich plan
  let joint := w.positiveCounterexampleOfRootReadoutSinksWithNoise rich sinks noise noisePositive biased
  have ordered := HedgeLinearReadoutPlan.readouts_ordered rich plan
    (HedgeRoutingReadoutPlan.steps_ordered w.rootReadoutNodes w.roots w.rootReadoutSuccessor
      w.rootReadoutSuccessor_wellFormed noise)
  have pivots : forall instruction, instruction ∈ instructions -> w.rootReadoutNodes instruction.pivot = true := by
    intro instruction listed
    rcases List.mem_map.mp listed with ⟨step, stepListed, same⟩
    subst instruction
    rcases List.mem_map.mp stepListed with ⟨node, nodeListed, same⟩
    subst step
    exact (NodeSet.mem_members_iff w.rootReadoutNodes node).mp nodeListed
  have denominator : query.jointDenominator.ValueEquivalent joint.left joint.right := by
    change query.jointDenominator.ValueEquivalent
      ((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich instructions)
      ((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich instructions)
    apply w.carrierDefectParityModels_withHedgeReadouts_valueEquivalent_of_outsideLarge_of_off
      rich query.jointDenominator instructions ordered
      (fun instruction listed => sinks instruction.pivot (pivots instruction listed)) conditionOutsideLarge
    intro instruction listed
    cases selected : query.condition instruction.pivot with
    | false => exact selected
    | true =>
        have excluded := conditionOutsideRoutes instruction.pivot selected
        rw [pivots instruction listed] at excluded
        cases excluded
  exact ConditionalCounterexampleIn.ofJointNumeratorOfDenominatorEquivalent
    (C := GraphModelClass.positive G) (fun member => member.2) query joint denominator

/-- The automatic routed conditional constructor with the explicit common
private-noise factor whose stay mass is two and flip mass is one.  Support
and bias are internal facts.  Only the kept-sink condition and the two
conditioner-disjointness properties remain geometric premises.

This removes the earlier requirement that all common roots already belong
to the conditional outcome, but does not claim a countermodel for every
irreducible IDC terminal. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfRootReadoutSinksOfConditionOutside
    {G : ObservedGraph S} {query : ConditionalKernelQuery S}
    (w : HedgeWitness G query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (sinks : forall node, w.rootReadoutNodes node = true -> w.child node = none)
    (conditionOutsideLarge : NodeSet.Disjoint query.condition w.large)
    (conditionOutsideRoutes : NodeSet.Disjoint query.condition w.rootReadoutNodes) :
    ConditionalCounterexampleIn (GraphModelClass.positive G) query :=
  w.positiveConditionalCounterexampleOfRootReadoutSinksOfConditionOutsideWithNoise rich sinks
    conditionOutsideLarge conditionOutsideRoutes (fun _ => hedgeReadoutNoise)
    (fun _ _ => hedgeReadoutNoise_positive)
    (fun _ _ => ⟨1, by decide, hedgeReadoutNoise_bias⟩)

end Causality
end Thesis
