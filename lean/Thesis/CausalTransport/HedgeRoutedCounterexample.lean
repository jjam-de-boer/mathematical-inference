import Thesis.CausalTransport.HedgeReadoutPullback

namespace Thesis
namespace Causality

open Probability

/-!
# Positive original-query countermodels from a finite readout plan

The observational and interventional components now meet at one checked
constructor.  A finite increasing linear readout plan defines the two actual
SCMs.  Sink pivots of the kept forest map preserve their complete observed
laws; supported private noise preserves strict positivity; biased-channel
pullback carries a final outcome parity event back to the original common
root parity.  All four countermodel fields therefore concern the same pair
and the original joint query.

The constructor's routing conditions are explicit and geometric: initial
kept sinks, freedom from the action, outcome-local coordinates, and a pure
finite substitution identity.  It does not ask for observational equality
or interventional separation of the newly built models.  `HedgeReadoutPlan`
now constructs the canonical all-root plan and proves its substitution
identity.  It does not prove the initial non-influence condition for an
arbitrary hedge: internal-forest re-entry still needs a different
observational argument.
-/

variable {S : ObservedSignature.{0}}

/-- A parity list is local to any outcome set containing all its entries,
including lists with repeated entries and the empty event. -/
theorem hedgeParityList_dependsOnlyOn (rich : ObservedSignature.ValueRich S)
    (nodes : List (Fin S.count)) (outcome : NodeSet S)
    (outcomeLocal : forall node, node ∈ nodes -> outcome node = true) :
    EventDependsOnlyOn outcome (hedgeParityList rich nodes) := by
  intro first second agree
  unfold hedgeParityList
  apply foldl_congr_of_mem
  intro total node listed
  rw [agree node (outcomeLocal node listed)]

/-- Realize the requested original outcome parity under the original
hedge action.  The distributional query is retained verbatim. -/
def HedgeWitness.readoutOutcomeEventQuery
    {G : ObservedGraph S} {q : JointKernelQuery S} (_w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (nodes : List (Fin S.count))
    (outcomeLocal : forall node, node ∈ nodes -> q.outcome node = true) : InterventionalQuery S where
  intervention := hedgeDoSecondIntervention rich q.action
  outcomeNodes := q.outcome
  action_outcome_disjoint := by
    rw [hedgeDoSecondIntervention_targets]
    exact q.action_outcome_disjoint
  event := hedgeParityList rich nodes
  event_local := hedgeParityList_dependsOnlyOn rich nodes q.outcome outcomeLocal

theorem HedgeWitness.readoutOutcomeEventQuery_kernel
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (nodes : List (Fin S.count))
    (outcomeLocal : forall node, node ∈ nodes -> q.outcome node = true) :
    (w.readoutOutcomeEventQuery rich nodes outcomeLocal).kernelQuery = q := by
  simp only [readoutOutcomeEventQuery, InterventionalQuery.kernelQuery, hedgeDoSecondIntervention_targets]

theorem HedgeWitness.readoutOutcomeEventQuery_value
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (nodes : List (Fin S.count))
    (outcomeLocal : forall node, node ∈ nodes -> q.outcome node = true) (model : ExactModel S) :
    (w.readoutOutcomeEventQuery rich nodes outcomeLocal).value model =
      model.interventionalValue (hedgeDoSecond rich q.action) (hedgeParityList rich nodes) := by
  have active : finAny S.count q.action = true := finAny_eq_true_of q.action w.actionSeed w.actionSeed_in_action
  simp only [readoutOutcomeEventQuery, InterventionalQuery.value, InterventionalQuery.distribution,
    hedgeDoSecondIntervention_targets, active, ↓reduceIte]
  rfl

namespace HedgeLinearReadoutPlan

theorem readouts_ordered (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeLinearReadoutStep S))
    (ordered : steps.Pairwise (fun first second => first.pivot.val < second.pivot.val)) :
    (readouts rich steps).Pairwise (fun first second => first.pivot.val < second.pivot.val) :=
  List.Pairwise.map (fun step : HedgeLinearReadoutStep S => step.toReadoutStep rich)
    (fun _ _ earlier => earlier) ordered

theorem readouts_ignored (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeLinearReadoutStep S))
    (ignored : forall step, step ∈ steps -> base.OtherMechanismsIgnore step.pivot) :
    forall instruction, instruction ∈ readouts rich steps -> base.OtherMechanismsIgnore instruction.pivot := by
  intro instruction listed
  rcases List.mem_map.mp listed with ⟨step, included, same⟩
  subst instruction
  exact ignored step included

theorem readouts_noise_positive (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeLinearReadoutStep S))
    (positive : forall step, step ∈ steps ->
      forall bit, step.noise.EventPositive (FiniteProbRecord.singletonEvent bit)) :
    forall instruction, instruction ∈ readouts rich steps ->
      forall bit, instruction.noise.EventPositive (FiniteProbRecord.singletonEvent bit) := by
  intro instruction listed
  rcases List.mem_map.mp listed with ⟨step, included, same⟩
  subst instruction
  exact positive step included

end HedgeLinearReadoutPlan

/-- Positive countermodels for the original joint query from an explicit
finite routed plan.  The pure pullback identity may include duplicate
coordinates and XOR cancellations; it need not be literal list equality.

Every model field is constructed before the separation proof: no model pair
is chosen from a proposition.  The final local event refutes equality of the
original full outcome kernel, not just a substituted root query.  The noise
conditions are separate: both values have support for full positivity, and
strict bias prevents erasure of the interventional gap. -/
noncomputable def HedgeWitness.positiveCounterexampleOfReadoutPlan
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (steps : List (HedgeLinearReadoutStep S))
    (ordered : steps.Pairwise (fun first second => first.pivot.val < second.pivot.val))
    (sinks : forall step, step ∈ steps -> w.child step.pivot = none)
    (free : forall step, step ∈ steps -> q.action step.pivot = false)
    (noisePositive : forall step, step ∈ steps ->
      forall bit, step.noise.EventPositive (FiniteProbRecord.singletonEvent bit))
    (biased : forall step, step ∈ steps -> Exists fun gap =>
      0 < gap ∧ FiniteProbRecord.eventMass step.noise.atoms (fun bit => !bit) =
        FiniteProbRecord.eventMass step.noise.atoms id + gap)
    (nodes : List (Fin S.count))
    (outcomeLocal : forall node, node ∈ nodes -> q.outcome node = true)
    (pullback : forall sample, hedgeParityList rich (HedgeLinearReadoutPlan.pullbackNodes steps nodes) sample =
      hedgeRootParityEvent rich w.roots sample) :
    CounterexampleIn (GraphModelClass.positive G) q := by
  let leftBase := w.largeCarrierDefectParityModel rich
  let rightBase := w.smallCarrierDefectParityModel rich
  let instructions := HedgeLinearReadoutPlan.readouts rich steps
  have orderedInstructions := HedgeLinearReadoutPlan.readouts_ordered rich steps ordered
  have leftIgnored : forall step, step ∈ steps -> leftBase.OtherMechanismsIgnore step.pivot :=
    fun step listed => w.largeCarrierDefectParityModel_otherMechanismsIgnore rich step.pivot (sinks step listed)
  have rightIgnored : forall step, step ∈ steps -> rightBase.OtherMechanismsIgnore step.pivot :=
    fun step listed => w.smallCarrierDefectParityModel_otherMechanismsIgnore rich step.pivot (sinks step listed)
  let left := leftBase.withHedgeReadouts rich instructions
  let right := rightBase.withHedgeReadouts rich instructions
  refine {
    left := left
    right := right
    left_mem := ⟨leftBase.withHedgeReadouts_compatible (w.largeCarrierDefectParityModel_compatible rich) rich instructions,
      leftBase.withHedgeReadouts_positive (w.largeCarrierDefectParityModel_positive rich) rich instructions
        (HedgeLinearReadoutPlan.readouts_noise_positive rich steps noisePositive)⟩
    right_mem := ⟨rightBase.withHedgeReadouts_compatible (w.smallCarrierDefectParityModel_compatible rich) rich instructions,
      rightBase.withHedgeReadouts_positive (w.smallCarrierDefectParityModel_positive rich) rich instructions
        (HedgeLinearReadoutPlan.readouts_noise_positive rich steps noisePositive)⟩
    observationally_equal := FiniteLatentSCM.withHedgeReadouts_observationally_equivalent leftBase rightBase
      (w.carrierDefectParityModels_observationally_equivalent rich) rich instructions orderedInstructions
      (HedgeLinearReadoutPlan.readouts_ignored leftBase rich steps leftIgnored)
      (HedgeLinearReadoutPlan.readouts_ignored rightBase rich steps rightIgnored)
    query_separated := ?_ }
  have gap : Not (QProb.Equiv
      (left.interventionalValue (hedgeDoSecond rich q.action) (hedgeParityList rich nodes))
      (right.interventionalValue (hedgeDoSecond rich q.action) (hedgeParityList rich nodes))) := by
    intro equivalent
    have restored := (HedgeLinearReadoutPlan.interventionalValue_equiv_iff leftBase rightBase rich steps ordered
      leftIgnored rightIgnored (hedgeDoSecond rich q.action)
      (fun step listed => hedgeDoSecond_of_false rich q.action (free step listed)) biased nodes).mp equivalent
    have eventEqual : hedgeParityList rich (HedgeLinearReadoutPlan.pullbackNodes steps nodes) =
        hedgeRootParityEvent rich w.roots := funext pullback
    rw [eventEqual] at restored
    exact w.carrierDefectParityModels_rootParity_not_equiv_doSecond rich restored
  let eventQuery := w.readoutOutcomeEventQuery rich nodes outcomeLocal
  have eventGap : Not (QProb.Equiv (eventQuery.value left) (eventQuery.value right)) := by
    simpa only [eventQuery, w.readoutOutcomeEventQuery_value] using gap
  have kernelGap := eventQuery.not_kernelValueEquivalent_of_not_value left right eventGap
  simpa only [eventQuery, w.readoutOutcomeEventQuery_kernel] using kernelGap

end Causality
end Thesis
