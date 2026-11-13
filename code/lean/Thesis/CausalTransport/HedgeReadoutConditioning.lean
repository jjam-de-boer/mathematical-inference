import Thesis.CausalTransport.HedgeReadout
import Thesis.Probability.ConditionalNoise
import Thesis.Probability.FiniteRecordSlicing

namespace Thesis
namespace Causality

open Probability

/-!
# Actual private readout channels under retained conditioning evidence

The one-coordinate interventional readout theorem does not by itself route a
conditional gap.  A denominator can change even when the new output bit has
the desired marginal signal.  This module retains the complete original
context and proves the actual normalized posterior of a private readout.

Non-influence of the updated pivot keeps every off-pivot context coordinate
unchanged.  The actual appended prior is a finite independent product, so
conditioning it on that old source evidence leaves the new bit independent
of the genuinely conditioned source.  The resulting posterior is therefore
the existing biased XOR channel of the old conditional readout signal.
Its nonzero bias reflects gaps even when the two evidence masses differ.

The parent signal is any function of declared typed parent values.  In
particular, a source-free readout can copy one incoming parent bit to a later
observed outcome.  This is a semantic step for composing conditional routes,
not a theorem that every active path consists of such ignored pivots.  A
complete conditional countermodel still needs graph-compatible route data,
whole observational equality, and a final connection to the original kernel.
-/

variable {S : ObservedSignature.{0}}

/-- An earlier readout cannot introduce dependence on a later observed
coordinate.  This is the non-influence invariant needed before another
conditional route step, independent of its evidence or noise bias. -/
theorem FiniteLatentSCM.withHedgeReadout_otherMechanismsIgnore_of_earlier
    (base : ExactModel S) (rich : ObservedSignature.ValueRich S) (pivot later : Fin S.count)
    (noise : FiniteProbRecord Bool) (injectOld : Bool) (parentSignal : S.ParentValues pivot -> Bool)
    (ignored : base.OtherMechanismsIgnore later) (earlier : pivot.val < later.val) :
    (base.withHedgeReadout rich pivot noise injectOld parentSignal).OtherMechanismsIgnore later :=
  base.withPrivateBooleanNoise_otherMechanismsIgnore_of_earlier pivot later noise
    (fun parents inputs bit => hedgeNoisyReadout rich pivot injectOld parentSignal parents
      (base.mechanism pivot parents inputs) bit) ignored earlier

namespace HedgeReadoutConditioning

/-- Source evidence is evaluated under the same original intervention that
will be used in the installed model.  It keeps all full observed labels. -/
def sourceContext (base : ExactModel S)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (context : Event S.Assignment) : Event base.latent.Assignment :=
  fun old => context (base.evalUnder intervention old)

/-- Actual evidence in the installed model, not an unrelated source event
assumed to have the same probability. -/
def evidence (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (pivot : Fin S.count) (noise : FiniteProbRecord Bool)
    (injectOld : Bool) (parentSignal : S.ParentValues pivot -> Bool)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (context : Event S.Assignment) :
    Event (base.withHedgeReadout rich pivot noise injectOld parentSignal).latent.Assignment :=
  sourceContext (base.withHedgeReadout rich pivot noise injectOld parentSignal) intervention context

/-- The full context is pointwise unchanged on every encoded old unit and
new noise bit.  The pivot can have arbitrary ambient descendants, but the
displayed base model must prove that its other mechanisms ignore it. -/
theorem context_assignment (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (pivot : Fin S.count) (noise : FiniteProbRecord Bool)
    (injectOld : Bool) (parentSignal : S.ParentValues pivot -> Bool)
    (ignored : base.OtherMechanismsIgnore pivot)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (nodes : NodeSet S) (context : Event S.Assignment) (localContext : EventDependsOnlyOn nodes context)
    (away : nodes pivot = false) (old : base.latent.Assignment) (bit : Bool) :
    context ((base.withHedgeReadout rich pivot noise injectOld parentSignal).evalUnder intervention
      (PrivateBooleanNoise.assignment base.latent bit old)) = context (base.evalUnder intervention old) := by
  apply localContext
  intro node selected
  have different : node ≠ pivot := by
    intro same
    rw [same, away] at selected
    cases selected
  exact base.withPrivateBooleanNoise_evalNodeUnder_eq_of_ne pivot noise
    (fun parents inputs bit => hedgeNoisyReadout rich pivot injectOld parentSignal parents
      (base.mechanism pivot parents inputs) bit) ignored intervention old bit node different

/-- Evidence support and denominator preservation come from actual
evaluation and finite integration.  No noise-support atom is selected. -/
theorem evidence_probVal (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (pivot : Fin S.count) (noise : FiniteProbRecord Bool)
    (injectOld : Bool) (parentSignal : S.ParentValues pivot -> Bool)
    (ignored : base.OtherMechanismsIgnore pivot)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (nodes : NodeSet S) (context : Event S.Assignment) (localContext : EventDependsOnlyOn nodes context)
    (away : nodes pivot = false) :
    QProb.Equiv
      ((base.withHedgeReadout rich pivot noise injectOld parentSignal).prior.probVal
        (evidence base rich pivot noise injectOld parentSignal intervention context))
      (base.prior.probVal (sourceContext base intervention context)) := by
  have pushed := (noise.product base.prior).map_probVal
    (fun pair => PrivateBooleanNoise.assignment base.latent pair.1 pair.2)
    (evidence base rich pivot noise injectOld parentSignal intervention context)
  have contexts := (noise.product base.prior).probVal_congr _ _ (fun pair =>
    context_assignment base rich pivot noise injectOld parentSignal ignored intervention
      nodes context localContext away pair.2 pair.1)
  exact QProb.equiv_trans pushed (QProb.equiv_trans contexts
    (noise.product_probVal_right base.prior (sourceContext base intervention context)))

/-- Supported old context gives supported actual evidence after installation.
The denominator identity transports positivity directly, without selecting a
noise bit or an old latent realization. -/
theorem evidence_positive (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (pivot : Fin S.count) (noise : FiniteProbRecord Bool)
    (injectOld : Bool) (parentSignal : S.ParentValues pivot -> Bool)
    (ignored : base.OtherMechanismsIgnore pivot)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (nodes : NodeSet S) (context : Event S.Assignment) (localContext : EventDependsOnlyOn nodes context)
    (away : nodes pivot = false) (supported : base.prior.EventPositive (sourceContext base intervention context)) :
    (base.withHedgeReadout rich pivot noise injectOld parentSignal).prior.EventPositive
      (evidence base rich pivot noise injectOld parentSignal intervention context) :=
  (QProb.equiv_num_pos_iff (evidence_probVal base rich pivot noise injectOld parentSignal
    ignored intervention nodes context localContext away)).mpr supported

/-- The observed pivot-bit posterior sampled from the actual conditioned
augmented prior.  Its support is proved above, not assumed of the installed
model or borrowed from an abstract channel. -/
def posterior (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (pivot : Fin S.count) (noise : FiniteProbRecord Bool)
    (injectOld : Bool) (parentSignal : S.ParentValues pivot -> Bool)
    (ignored : base.OtherMechanismsIgnore pivot)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (nodes : NodeSet S) (context : Event S.Assignment) (localContext : EventDependsOnlyOn nodes context)
    (away : nodes pivot = false) (supported : base.prior.EventPositive (sourceContext base intervention context)) :
    FiniteProbRecord Bool :=
  let actual := base.withHedgeReadout rich pivot noise injectOld parentSignal
  (actual.prior.conditionOn (evidence base rich pivot noise injectOld parentSignal intervention context)
    (evidence_positive base rich pivot noise injectOld parentSignal ignored intervention
      nodes context localContext away supported)).map
    (fun unit => hedgeIsSecond rich pivot (actual.evalUnder intervention unit pivot))

/-- Every actual posterior event equals the corresponding event after an
independent flip of the old conditioned source signal.  Both the evidence
and response are transported through the real appended-coordinate encoding;
the denominator is retained before any bias argument is invoked. -/
theorem posterior_probVal (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (pivot : Fin S.count) (noise : FiniteProbRecord Bool)
    (injectOld : Bool) (parentSignal : S.ParentValues pivot -> Bool)
    (ignored : base.OtherMechanismsIgnore pivot)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (free : intervention pivot = none)
    (nodes : NodeSet S) (context : Event S.Assignment) (localContext : EventDependsOnlyOn nodes context)
    (away : nodes pivot = false) (supported : base.prior.EventPositive (sourceContext base intervention context))
    (event : Event Bool) :
    QProb.Equiv
      ((posterior base rich pivot noise injectOld parentSignal ignored intervention
        nodes context localContext away supported).probVal event)
      (((base.prior.conditionOn (sourceContext base intervention context) supported).xorChannel
        (fun old => hedgeReadoutSignal rich pivot injectOld parentSignal (base.evalUnder intervention old)) noise).probVal event) := by
  let actual := base.withHedgeReadout rich pivot noise injectOld parentSignal
  let encode := fun pair : Bool × base.latent.Assignment => PrivateBooleanNoise.assignment base.latent pair.1 pair.2
  let actualEvidence := evidence base rich pivot noise injectOld parentSignal intervention context
  let actualSupported := evidence_positive base rich pivot noise injectOld parentSignal ignored intervention
    nodes context localContext away supported
  let actualBit := fun unit => hedgeIsSecond rich pivot (actual.evalUnder intervention unit pivot)
  have evidenceEq : (fun pair => actualEvidence (encode pair)) =
      (fun pair : Bool × base.latent.Assignment => sourceContext base intervention context pair.2) := by
    funext pair
    exact context_assignment base rich pivot noise injectOld parentSignal ignored intervention
      nodes context localContext away pair.2 pair.1
  have responseEq (pair : Bool × base.latent.Assignment) : actualBit (encode pair) =
      Bool.xor (hedgeReadoutSignal rich pivot injectOld parentSignal (base.evalUnder intervention pair.2)) pair.1 := by
    change hedgeIsSecond rich pivot ((base.withPrivateReadout pivot noise
      (hedgeNoisyReadout rich pivot injectOld parentSignal)).evalNodeUnder intervention (encode pair) pivot) = _
    rw [base.withPrivateReadout_evalNodeUnder_pivot pivot noise
      (hedgeNoisyReadout rich pivot injectOld parentSignal) intervention free pair.2 pair.1]
    simp only [hedgeNoisyReadout, hedgeIsSecond_parityCarrierValue]
    rfl
  have mapped := (actual.prior.conditionOn actualEvidence actualSupported).map_probVal actualBit event
  have pulled := (noise.product base.prior).map_conditionOn_probVal encode actualEvidence
    (fun unit => event (actualBit unit)) actualSupported
  -- The support proof travels with its event equality.  Their propositions
  -- agree after transport, so no new support witness or latent unit is chosen.
  simp only [evidenceEq] at pulled
  have response := ((noise.product base.prior).conditionOn
    (fun pair => sourceContext base intervention context pair.2)
    (noise.product_evidence_right_positive base.prior (sourceContext base intervention context) supported)).probVal_congr
      _ _ (fun pair => congrArg event (responseEq pair))
  exact QProb.equiv_trans mapped (QProb.equiv_trans pulled (QProb.equiv_trans response
    (base.prior.xorChannel_conditionOn_noise_first_probVal
      (fun old => hedgeReadoutSignal rich pivot injectOld parentSignal (base.evalUnder intervention old))
      (sourceContext base intervention context) supported noise event)))

/-- Equality of actual conditional outputs reflects equality of their old
conditional signals whenever the supplied independent noise has nonzero
bias.  The models' latent carriers and context denominators may differ. -/
theorem posterior_probVal_equiv_iff_of_bias (left right : ExactModel S)
    (rich : ObservedSignature.ValueRich S) (pivot : Fin S.count) (noise : FiniteProbRecord Bool)
    (injectOld : Bool) (parentSignal : S.ParentValues pivot -> Bool)
    (leftIgnored : left.OtherMechanismsIgnore pivot) (rightIgnored : right.OtherMechanismsIgnore pivot)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (free : intervention pivot = none)
    (nodes : NodeSet S) (context : Event S.Assignment) (localContext : EventDependsOnlyOn nodes context)
    (away : nodes pivot = false)
    (leftSupported : left.prior.EventPositive (sourceContext left intervention context))
    (rightSupported : right.prior.EventPositive (sourceContext right intervention context))
    (gap : Nat) (positiveGap : 0 < gap)
    (bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass noise.atoms id + gap) :
    QProb.Equiv
      ((posterior left rich pivot noise injectOld parentSignal leftIgnored intervention
        nodes context localContext away leftSupported).probVal id)
      ((posterior right rich pivot noise injectOld parentSignal rightIgnored intervention
        nodes context localContext away rightSupported).probVal id) ↔
      QProb.Equiv
        ((left.prior.conditionOn (sourceContext left intervention context) leftSupported).probVal
          (fun old => hedgeReadoutSignal rich pivot injectOld parentSignal (left.evalUnder intervention old)))
        ((right.prior.conditionOn (sourceContext right intervention context) rightSupported).probVal
          (fun old => hedgeReadoutSignal rich pivot injectOld parentSignal (right.evalUnder intervention old))) := by
  have leftLaw := posterior_probVal left rich pivot noise injectOld parentSignal leftIgnored intervention free
    nodes context localContext away leftSupported id
  have rightLaw := posterior_probVal right rich pivot noise injectOld parentSignal rightIgnored intervention free
    nodes context localContext away rightSupported id
  have channel := FiniteProbRecord.xorChannel_probVal_equiv_iff_of_bias
    (left.prior.conditionOn _ leftSupported)
    (fun old => hedgeReadoutSignal rich pivot injectOld parentSignal (left.evalUnder intervention old))
    (right.prior.conditionOn _ rightSupported)
    (fun old => hedgeReadoutSignal rich pivot injectOld parentSignal (right.evalUnder intervention old))
    noise gap positiveGap bias
  constructor
  · intro equal
    exact channel.mp (QProb.equiv_trans (QProb.equiv_symm leftLaw) (QProb.equiv_trans equal rightLaw))
  · intro equal
    exact QProb.equiv_trans leftLaw (QProb.equiv_trans (channel.mpr equal) (QProb.equiv_symm rightLaw))

end HedgeReadoutConditioning
end Causality
end Thesis
