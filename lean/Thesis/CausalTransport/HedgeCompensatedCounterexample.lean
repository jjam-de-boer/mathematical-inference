import Thesis.CausalTransport.HedgeCompensatedConservation
import Thesis.CausalTransport.HedgeReadoutNoise
import Thesis.CausalTransport.HedgeRoutedCounterexample

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Positive original-query countermodels with responding internal readouts

The compensated large and nested flow identities now meet the real
finite-prior integration theorem.  Every installed row has its own private
Boolean factor.  Integrating those factors preserves the original root
signal gap whenever each factor has a positive stay-bias gap.  The final
separated event depends only on the original queried outcome sinks, and all
countermodel fields concern the very same pair of positive compatible SCMs.

This constructor includes responding internal small-forest vertices, old
children off the explicit route, merging routes, and composite actions with
non-sink action vertices.  It does not assume that installed rows are kept
sinks or that other mechanisms ignore them.  Observed alphabets remain the
full finite alphabets of the supplied rich signature.

The one geometric restriction remains explicit: the canonical outcome
routes may enter the small forest or leave the large forest, but may not
modify an outer-only forest vertex.  This is not yet the universal
`hedge_counterexample` field of `PublishedCompleteness`.  Removing that
restriction and constructing the remaining conditional terminal families
are still required for the complete published theorem.
-/

namespace HedgeCompensatedCounterexample

variable {G : ObservedGraph S} {q : JointKernelQuery S}

private theorem freshParity (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) (bits : Fin S.count -> Bool) :
    hedgeReadoutFreshParity (w.carrierFlowReadoutPlan rich noise) bits = hedgeNodeXor w.smallOutcomeFlowNodes bits := by
  simp only [hedgeReadoutFreshParity, HedgeWitness.carrierFlowReadoutPlan, List.foldl_map,
    HedgeWitness.carrierFlowReadoutStep, hedgeNodeXor]

/-- The nested original signal is the defect on every latent unit, not
only on support atoms.  Explicit recovery transports the existing encoded
unit theorem without choosing a representing unit from an existential. -/
private theorem smallRootSignal (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (unit : (w.smallCarrierDefectParityModel rich).latent.Assignment) :
    hedgeRootParityEvent rich w.roots ((w.smallCarrierDefectParityModel rich).evalUnder
      (hedgeDoSecond rich q.action) unit) = hedgeDefectBitOf G unit := by
  have encoded := w.smallCarrierDefectParityModel_rootParity_eq_defect rich
    (hedgeDefectOldAssignment G unit) (hedgeDefectBitOf G unit)
  rw [hedgeDefectAssignment_recover G unit] at encoded
  exact encoded

end HedgeCompensatedCounterexample

/-! ## Separation after integrating every actual fresh factor -/

/-- The final outcome-sink event remains separated under the original
action.  This integrates actual SCM priors rather than replacing them by
postulated noisy signal distributions.  Distinct pivots are proved from the
plan, and each supplied bias belongs to that pivot's real noise record. -/
theorem HedgeWitness.carrierDefectParityModels_carrierFlowReadoutPlan_sinkParity_not_equiv_doSecond
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false)
    (gap : Fin S.count -> Nat)
    (gapPositive : forall node, w.smallOutcomeFlowNodes node = true -> 0 < gap node)
    (bias : forall node, w.smallOutcomeFlowNodes node = true ->
      FiniteProbRecord.eventMass (noise node).atoms (fun bit => !bit) =
        FiniteProbRecord.eventMass (noise node).atoms id + gap node) :
    Not (QProb.Equiv
      (((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)).interventionalValue
        (hedgeDoSecond rich q.action) (hedgeRootParityEvent rich (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor)))
      (((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)).interventionalValue
        (hedgeDoSecond rich q.action) (hedgeRootParityEvent rich (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor)))) := by
  let left := w.largeCarrierDefectParityModel rich
  let right := w.smallCarrierDefectParityModel rich
  let steps := w.carrierFlowReadoutPlan rich noise
  let oldSignal := hedgeRootParityEvent rich w.roots
  let newSignal := hedgeRootParityEvent rich (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor)
  have planPositive : forall step, step ∈ steps -> 0 < gap step.pivot := by
    intro step listed
    rcases List.mem_map.mp listed with ⟨node, member, same⟩
    subst step
    exact gapPositive node ((NodeSet.mem_members_iff w.smallOutcomeFlowNodes node).mp member)
  have planBias : forall step, step ∈ steps -> FiniteProbRecord.eventMass step.noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass step.noise.atoms id + gap step.pivot := by
    intro step listed
    rcases List.mem_map.mp listed with ⟨node, member, same⟩
    subst step
    exact bias node ((NodeSet.mem_members_iff w.smallOutcomeFlowNodes node).mp member)
  have leftEquation : forall bits unit,
      newSignal ((left.withHedgeReadouts rich steps).evalUnder (hedgeDoSecond rich q.action)
        (left.hedgeReadoutAssignment rich bits steps unit)) =
      Bool.xor (oldSignal (left.evalUnder (hedgeDoSecond rich q.action) unit)) (hedgeReadoutFreshParity steps bits) := by
    intro bits unit
    rw [HedgeCompensatedCounterexample.freshParity]
    exact w.largeCarrierDefectParityModel_carrierFlowReadoutPlan_sinkParity_doSecond rich noise allowed bits unit
  have rightEquation : forall bits unit,
      newSignal ((right.withHedgeReadouts rich steps).evalUnder (hedgeDoSecond rich q.action)
        (right.hedgeReadoutAssignment rich bits steps unit)) =
      Bool.xor (oldSignal (right.evalUnder (hedgeDoSecond rich q.action) unit)) (hedgeReadoutFreshParity steps bits) := by
    intro bits unit
    rw [HedgeCompensatedCounterexample.freshParity]
    have original := HedgeCompensatedCounterexample.smallRootSignal w rich unit
    change oldSignal (right.evalUnder (hedgeDoSecond rich q.action) unit) = hedgeDefectBitOf G unit at original
    rw [original]
    exact w.smallCarrierDefectParityModel_carrierFlowReadoutPlan_sinkParity_doSecond rich noise allowed bits unit
  have reflect := FiniteLatentSCM.withHedgeReadouts_prior_parity_equiv_iff left right rich steps
    (w.carrierFlowReadoutPlan_pivots_distinct rich noise) gap planPositive planBias
    (fun unit => oldSignal (left.evalUnder (hedgeDoSecond rich q.action) unit))
    (fun unit => oldSignal (right.evalUnder (hedgeDoSecond rich q.action) unit))
    (fun unit => newSignal ((left.withHedgeReadouts rich steps).evalUnder (hedgeDoSecond rich q.action) unit))
    (fun unit => newSignal ((right.withHedgeReadouts rich steps).evalUnder (hedgeDoSecond rich q.action) unit))
    leftEquation rightEquation
  intro equivalent
  have newPrior := QProb.equiv_trans
    (QProb.equiv_symm ((left.withHedgeReadouts rich steps).interventionalValue_eq (hedgeDoSecond rich q.action) newSignal))
    (QProb.equiv_trans equivalent
      ((right.withHedgeReadouts rich steps).interventionalValue_eq (hedgeDoSecond rich q.action) newSignal))
  have oldPrior := reflect.mp newPrior
  exact w.carrierDefectParityModels_rootParity_not_equiv_doSecond rich
    (QProb.equiv_trans (left.interventionalValue_eq (hedgeDoSecond rich q.action) oldSignal)
      (QProb.equiv_trans oldPrior (QProb.equiv_symm (right.interventionalValue_eq (hedgeDoSecond rich q.action) oldSignal))))

/-! ## The same model pair refutes the original full outcome kernel -/

/-- Construct positive countermodels for the original query using the
canonical compensated plan.  The sole geometric premise excludes outer-only
route updates; there is no caller-supplied plan, parity identity, observational
law, sink condition, or separation premise.  Support and bias are checked for
each actual independent factor and may vary from vertex to vertex. -/
noncomputable def HedgeWitness.positiveCounterexampleOfCarrierFlowReadoutPlan
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false)
    (noisePositive : forall node, w.smallOutcomeFlowNodes node = true ->
      forall bit, (noise node).EventPositive (FiniteProbRecord.singletonEvent bit))
    (gap : Fin S.count -> Nat) (gapPositive : forall node, w.smallOutcomeFlowNodes node = true -> 0 < gap node)
    (bias : forall node, w.smallOutcomeFlowNodes node = true ->
      FiniteProbRecord.eventMass (noise node).atoms (fun bit => !bit) =
        FiniteProbRecord.eventMass (noise node).atoms id + gap node) :
    CounterexampleIn (GraphModelClass.positive G) q := by
  let steps := w.carrierFlowReadoutPlan rich noise
  let left := (w.largeCarrierDefectParityModel rich).withHedgeReadouts rich steps
  let right := (w.smallCarrierDefectParityModel rich).withHedgeReadouts rich steps
  refine {
    left := left
    right := right
    left_mem := ⟨FiniteLatentSCM.withHedgeReadouts_compatible _ (w.largeCarrierDefectParityModel_compatible rich) rich steps,
      w.largeCarrierDefectParityModel_carrierFlowReadoutPlan_positive rich noise noisePositive⟩
    right_mem := ⟨FiniteLatentSCM.withHedgeReadouts_compatible _ (w.smallCarrierDefectParityModel_compatible rich) rich steps,
      w.smallCarrierDefectParityModel_carrierFlowReadoutPlan_positive rich noise noisePositive⟩
    observationally_equal := w.carrierDefectParityModels_carrierFlowReadoutPlan_observationally_equivalent rich noise allowed
    query_separated := ?_ }
  let nodes := NodeSet.members (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor)
  have outcomeLocal : forall node, node ∈ nodes -> q.outcome node = true := by
    intro node listed
    exact w.rootReadoutSinks_subset_outcome node
      ((NodeSet.mem_members_iff (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor) node).mp listed)
  let eventQuery := w.readoutOutcomeEventQuery rich nodes outcomeLocal
  have gap := w.carrierDefectParityModels_carrierFlowReadoutPlan_sinkParity_not_equiv_doSecond rich noise allowed
    gap gapPositive bias
  have eventGap : Not (QProb.Equiv (eventQuery.value left) (eventQuery.value right)) := by
    simpa only [eventQuery, w.readoutOutcomeEventQuery_value] using gap
  have kernelGap := eventQuery.not_kernelValueEquivalent_of_not_value left right eventGap
  simpa only [eventQuery, w.readoutOutcomeEventQuery_kernel] using kernelGap

/-- A fixed supported stay-biased coin discharges all noise conditions.
The remaining premise is purely geometric, not a model-existence assumption. -/
noncomputable def HedgeWitness.positiveCounterexampleOfSmallOrOutsideCarrierFlow
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false) :
    CounterexampleIn (GraphModelClass.positive G) q :=
  w.positiveCounterexampleOfCarrierFlowReadoutPlan rich (fun _node => FiniteProbRecord.biasedFlip 1 1 (by decide)) allowed
    (fun _node _selected bit => by
      change (FiniteProbRecord.biasedFlip 1 1 (by decide)).EventPositive (FiniteProbRecord.singletonEvent bit)
      cases bit <;> decide +kernel)
    (fun _node => 1) (fun _node _selected => Nat.zero_lt_one)
    (fun _node _selected => by
      change FiniteProbRecord.eventMass (FiniteProbRecord.biasedFlip 1 1 (by decide)).atoms (fun bit => !bit) =
        FiniteProbRecord.eventMass (FiniteProbRecord.biasedFlip 1 1 (by decide)).atoms id + 1
      decide +kernel)

end Causality
end Thesis
