import Thesis.CausalTransport.HedgeReadoutConditioning
import Thesis.CausalTransport.ConditionalMarginalization
import Thesis.Causality.KernelConditioning
import Thesis.Causality.ConditionalCounterexampleWitness

namespace Thesis
namespace Causality

open Probability

/-!
# Carrying an actual conditional countermodel along an observed arrow

A useful readout on an active path need not already belong to the queried
outcome.  An independent private readout can carry its bit through a declared
incoming arrow to a later observed coordinate.  Conditioning must keep the
whole original context, and the two posterior denominators need not agree.

The first constructor takes an actual supported old conditional signal gap
and connects the installed readout to the original kernel.  The stronger
incoming-parent adapter starts with an existing positive singleton-outcome
countermodel.  Its finite cell selector derives the reference and source gap
internally; there is no assumed separation of the already modified kernel.
The target query can contain additional outcomes, but its action and given
set must remain those of the old query.

Non-influence of the target pivot is still needed for whole observational
equality and unchanged evidence.  This is a genuine semantic route step,
not a claim that arbitrary active-path vertices are ignored, or that general
collider activation and mixed-edge paths have already been assembled.
-/

variable {S : ObservedSignature.{0}}

namespace ConditionalReadout

/-- The actual singleton kernel cell equals the real conditioned readout
bit probability.  The reference observes the true bit as one full label;
nonbinary false-bit labels are never identified with a singleton cell. -/
noncomputable def contextKernel_denote (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (pivot : Fin S.count) (noise : FiniteProbRecord Bool)
    (injectOld : Bool) (parentSignal : S.ParentValues pivot -> Bool)
    (ignored : base.OtherMechanismsIgnore pivot)
    (action nodes : NodeSet S) (reference : S.Assignment) (away : nodes pivot = false)
    (supported : base.prior.EventPositive (HedgeReadoutConditioning.sourceContext base
      ((Kernel.mk (NodeSet.singleton pivot) action nodes).intervention reference) (Kernel.agreesOn nodes reference)))
    (second : reference pivot = rich.second pivot) :
    ProbabilityResult.Equivalent
      ((Kernel.mk (NodeSet.singleton pivot) action nodes).denote
        (base.withHedgeReadout rich pivot noise injectOld parentSignal) reference)
      (some ((HedgeReadoutConditioning.posterior base rich pivot noise injectOld parentSignal ignored
        ((Kernel.mk (NodeSet.singleton pivot) action nodes).intervention reference)
        nodes (Kernel.agreesOn nodes reference) (Kernel.agreesOn_dependsOnlyOn nodes reference) away supported).probVal id)) := by
  let kernel : Kernel S := ⟨NodeSet.singleton pivot, action, nodes⟩
  let actual := base.withHedgeReadout rich pivot noise injectOld parentSignal
  let intervention := kernel.intervention reference
  let context := Kernel.agreesOn nodes reference
  let actualSupported := HedgeReadoutConditioning.evidence_positive base rich pivot noise injectOld parentSignal
    ignored intervention nodes context (Kernel.agreesOn_dependsOnlyOn nodes reference) away supported
  have value := kernel.denote_prior_conditionOn actual reference actualSupported
  have cylinder := (actual.prior.conditionOn _ actualSupported).probVal_congr
    (fun unit => Kernel.agreesOn (NodeSet.singleton pivot) reference (actual.evalUnder intervention unit))
    (fun unit => hedgeIsSecond rich pivot (actual.evalUnder intervention unit pivot)) (fun unit => by
      dsimp only
      rw [Kernel.agreesOn_singleton, second]
      rfl)
  have mapped := (actual.prior.conditionOn _ actualSupported).map_probVal
    (fun unit => hedgeIsSecond rich pivot (actual.evalUnder intervention unit pivot)) id
  exact ProbabilityResult.trans value (.value (QProb.equiv_trans cylinder (QProb.equiv_symm mapped)))

/-- Install an actual positive conditional countermodel for the whole
original query from a supported old readout-signal gap.  Both fresh models,
their support, observational equality and the new kernel gap are proved by
the constructor.  Additional outcomes are restored by marginalization. -/
noncomputable def contextCounterexample {graph : ObservedGraph S}
    (query : ConditionalKernelQuery S) (left right : ExactModel S)
    (leftCompatible : Compatible left graph) (rightCompatible : Compatible right graph)
    (leftPositive : ObservationallyPositive left) (rightPositive : ObservationallyPositive right)
    (observational : ObservationallyEquivalent left right)
    (rich : ObservedSignature.ValueRich S) (pivot : Fin S.count) (selected : query.outcome pivot = true)
    (leftIgnored : left.OtherMechanismsIgnore pivot) (rightIgnored : right.OtherMechanismsIgnore pivot)
    (injectOld : Bool) (parentSignal : S.ParentValues pivot -> Bool)
    (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit))
    (gap : Nat) (positiveGap : 0 < gap)
    (bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass noise.atoms id + gap)
    (reference : S.Assignment) (second : reference pivot = rich.second pivot)
    (leftSupported : left.prior.EventPositive (HedgeReadoutConditioning.sourceContext left
      (query.operationKernel.intervention reference) (Kernel.agreesOn query.condition reference)))
    (rightSupported : right.prior.EventPositive (HedgeReadoutConditioning.sourceContext right
      (query.operationKernel.intervention reference) (Kernel.agreesOn query.condition reference)))
    (sourceGap : Not (QProb.Equiv
      ((left.prior.conditionOn (HedgeReadoutConditioning.sourceContext left
          (query.operationKernel.intervention reference) (Kernel.agreesOn query.condition reference)) leftSupported).probVal
        (fun old => hedgeReadoutSignal rich pivot injectOld parentSignal (left.evalUnder (query.operationKernel.intervention reference) old)))
      ((right.prior.conditionOn (HedgeReadoutConditioning.sourceContext right
          (query.operationKernel.intervention reference) (Kernel.agreesOn query.condition reference)) rightSupported).probVal
        (fun old => hedgeReadoutSignal rich pivot injectOld parentSignal (right.evalUnder (query.operationKernel.intervention reference) old))))) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query := by
  let leftModel := left.withHedgeReadout rich pivot noise injectOld parentSignal
  let rightModel := right.withHedgeReadout rich pivot noise injectOld parentSignal
  have leftMem : (GraphModelClass.positive graph).Mem leftModel :=
    ⟨left.withHedgeReadout_compatible leftCompatible rich pivot noise injectOld parentSignal,
      left.withHedgeReadout_positive leftPositive rich pivot noise noisePositive injectOld parentSignal⟩
  have rightMem : (GraphModelClass.positive graph).Mem rightModel :=
    ⟨right.withHedgeReadout_compatible rightCompatible rich pivot noise injectOld parentSignal,
      right.withHedgeReadout_positive rightPositive rich pivot noise noisePositive injectOld parentSignal⟩
  have subset : NodeSet.Subset (NodeSet.singleton pivot) query.outcome := by
    intro node included
    rw [(NodeSet.singleton_eq_true_iff pivot node).mp included]
    exact selected
  have away := query.outcome_condition_disjoint pivot selected
  have free : query.operationKernel.intervention reference pivot = none := by
    simp only [ConditionalKernelQuery.operationKernel, Kernel.intervention,
      query.action_outcome_disjoint.symm pivot selected, Bool.false_eq_true, if_false]
  let restricted := query.restrictOutcome (NodeSet.singleton pivot) subset
  apply ConditionalCounterexampleIn.ofRestrictedOutcome (C := GraphModelClass.positive graph)
    (fun member => member.2) query (NodeSet.singleton pivot) subset
  refine ⟨leftModel, rightModel, leftMem, rightMem,
    left.withPrivateReadout_observationally_equivalent right observational pivot noise
      (hedgeNoisyReadout rich pivot injectOld parentSignal) leftIgnored rightIgnored, ?_⟩
  intro equivalent
  rcases equivalent reference
    (leftMem.2.kernelPositiveSupportedValue restricted.operationKernel reference).toSupported
    (rightMem.2.kernelPositiveSupportedValue restricted.operationKernel reference).toSupported with ⟨between⟩
  have leftValue : ProbabilityResult.Equivalent (restricted.sourceTerm.denote leftModel reference) _ :=
    contextKernel_denote left rich pivot noise injectOld parentSignal leftIgnored query.action query.condition reference away leftSupported second
  have rightValue : ProbabilityResult.Equivalent (restricted.sourceTerm.denote rightModel reference) _ :=
    contextKernel_denote right rich pivot noise injectOld parentSignal rightIgnored query.action query.condition reference away rightSupported second
  have outputs := ProbabilityResult.trans (ProbabilityResult.symm leftValue) (ProbabilityResult.trans between rightValue)
  cases outputs with
  | value equal =>
      exact sourceGap ((HedgeReadoutConditioning.posterior_probVal_equiv_iff_of_bias left right rich pivot noise
        injectOld parentSignal leftIgnored rightIgnored (query.operationKernel.intervention reference) free query.condition
        (Kernel.agreesOn query.condition reference) (Kernel.agreesOn_dependsOnlyOn query.condition reference) away
        leftSupported rightSupported gap positiveGap bias).mp equal)

/-- Reserve the actual separated reference label for bit one at each
coordinate.  The first label is computed from the supplied rich pair, so no
alternative observed value is chosen from an existence proposition. -/
private def readoutValues (rich : ObservedSignature.ValueRich S) (reference : S.Assignment) :
    ObservedSignature.ValueRich S where
  first := fun node => if reference node = rich.first node then rich.second node else rich.first node
  second := reference
  first_enumerated := fun node => S.value_complete node _
  second_enumerated := fun node => S.value_complete node _
  different := by
    intro node
    by_cases same : reference node = rich.first node
    · simp only [same, if_true]
      exact Ne.symm (rich.different node)
    · simp only [same, if_false]
      exact Ne.symm same

/-- Carry any existing positive singleton-outcome conditional countermodel
along a declared observed arrow.  The target can have additional outcomes;
the entire action and conditioner are retained.  Finite cell search supplies
the actual old conditional gap and its labels, not a hand-supplied reference
or an assumed new-kernel separation. -/
noncomputable def ofIncomingParentWithNoise {graph : ObservedGraph S}
    (source target : ConditionalKernelQuery S)
    (counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) source)
    (rich : ObservedSignature.ValueRich S) (parent pivot : Fin S.count)
    (sourceOutcome : source.outcome = NodeSet.singleton parent) (targetSelected : target.outcome pivot = true)
    (action : source.action = target.action) (condition : source.condition = target.condition)
    (edge : S.directed parent pivot = true)
    (leftIgnored : counterexample.left.OtherMechanismsIgnore pivot)
    (rightIgnored : counterexample.right.OtherMechanismsIgnore pivot)
    (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit))
    (gap : Nat) (positiveGap : 0 < gap)
    (bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass noise.atoms id + gap) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) target := by
  let cell := counterexample.separatedCell (fun member => member.2)
  let reference := cell.reference
  let values := readoutValues rich reference
  let parentSignal := fun parents : S.ParentValues pivot => hedgeIsSecond values parent (parents parent edge)
  have supported (model : ExactModel S) (positive : ObservationallyPositive model) :
      model.prior.EventPositive (HedgeReadoutConditioning.sourceContext model
        (target.operationKernel.intervention reference) (Kernel.agreesOn target.condition reference)) :=
    positive.kernel_prior_cylinder_positive target.operationKernel target.condition reference
  have signalLaw (model : ExactModel S) (positive : ObservationallyPositive model) :
      ProbabilityResult.Equivalent (source.sourceTerm.denote model reference)
        (some ((model.prior.conditionOn (HedgeReadoutConditioning.sourceContext model
            (target.operationKernel.intervention reference) (Kernel.agreesOn target.condition reference))
            (supported model positive)).probVal
          (fun old => hedgeReadoutSignal values pivot false parentSignal
            (model.evalUnder (target.operationKernel.intervention reference) old)))) := by
    have sourceSupported := positive.kernel_prior_cylinder_positive source.operationKernel source.condition reference
    have law := source.operationKernel.denote_prior_conditionOn model reference sourceSupported
    simp only [ConditionalKernelQuery.operationKernel, Kernel.conditionEvent, action, condition] at law
    simp only [ConditionalKernelQuery.sourceTerm, ConditionalKernelQuery.operationKernel, action, condition]
    apply ProbabilityResult.trans law
    apply ProbabilityResult.Equivalent.value
    apply FiniteProbRecord.probVal_congr
    intro old
    rw [sourceOutcome, Kernel.agreesOn_singleton]
    simp only [hedgeReadoutSignal, Bool.false_eq_true, if_false, Bool.false_xor]
    rfl
  have leftLaw := ProbabilityResult.trans (ProbabilityResult.symm cell.leftValue.equivalent)
    (signalLaw counterexample.left counterexample.left_mem.2)
  have rightLaw := ProbabilityResult.trans (ProbabilityResult.symm cell.rightValue.equivalent)
    (signalLaw counterexample.right counterexample.right_mem.2)
  apply contextCounterexample target counterexample.left counterexample.right
    counterexample.left_mem.1 counterexample.right_mem.1 counterexample.left_mem.2 counterexample.right_mem.2
    counterexample.observationally_equal values pivot targetSelected leftIgnored rightIgnored false parentSignal
    noise noisePositive gap positiveGap bias reference rfl
    (supported counterexample.left counterexample.left_mem.2) (supported counterexample.right counterexample.right_mem.2)
  intro equal
  cases leftLaw with
  | value leftEqual =>
      cases rightLaw with
      | value rightEqual =>
          exact cell.separated (QProb.equiv_trans leftEqual (QProb.equiv_trans equal (QProb.equiv_symm rightEqual)))

/-- The same general arrow step with explicit supported `2:1` stay/flip
noise.  The finite reference search and concrete noise introduce no choice. -/
noncomputable def ofIncomingParent {graph : ObservedGraph S}
    (source target : ConditionalKernelQuery S)
    (counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) source)
    (rich : ObservedSignature.ValueRich S) (parent pivot : Fin S.count)
    (sourceOutcome : source.outcome = NodeSet.singleton parent) (targetSelected : target.outcome pivot = true)
    (action : source.action = target.action) (condition : source.condition = target.condition)
    (edge : S.directed parent pivot = true)
    (leftIgnored : counterexample.left.OtherMechanismsIgnore pivot)
    (rightIgnored : counterexample.right.OtherMechanismsIgnore pivot) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) target :=
  ofIncomingParentWithNoise source target counterexample rich parent pivot sourceOutcome targetSelected action condition edge
    leftIgnored rightIgnored (FiniteProbRecord.biasedFlip 1 1 (by decide))
    (by intro bit; cases bit <;> decide +kernel) 1 (by decide) (by decide +kernel)

end ConditionalReadout
end Causality
end Thesis
