import Thesis.CausalTransport.HedgePositive
import Thesis.Probability.BooleanNoise

namespace Thesis
namespace Causality

open Probability

/-!
# Finite private-noise transport for hedge parity

The positive root-parity carrier pair is already separated under the original
hedge action.  Routing that signal to the original outcome needs additional
private flips: deterministic readout copies alone would impose zero-probability
observational assignments.  `Probability.BooleanNoise` proves that arbitrary
finite biased flip families restore Boolean support without erasing a gap.

This module connects those finite-record results to SCM interventional signals
and the full observed-value alphabet.  The support constructor retains every
background value, not just the two values used to encode parity.  Separation
allows any finite number of independent flips and any positive excess stay
weight; no real-valued small-noise limit is assumed.

The boundary is deliberate: a noisy *signal distribution* is not a new SCM.
These theorems do not assert that replacing mechanisms preserves observational
equivalence, nor that root parity is already the original outcome.  The routed
hedge construction must still realize these channels with graph-compatible
mechanisms and prove equality of the complete observational laws.
-/

/-! ## Independent noise on a model's interventional event -/

/-- The Boolean event signal obtained by intervening on a finite model and
then adding an independent finite noise bit.  The product is at prior-record
level; it does not add a causal edge or mutate the supplied model. -/
def FiniteLatentSCM.noisyInterventionalSignal
    (model : FiniteLatentSCM S)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (event : S.Assignment -> Bool) (noise : FiniteProbRecord Bool) :
    FiniteProbRecord Bool :=
  model.prior.xorChannel (fun latent => event (model.evalUnder intervention latent)) noise

/-- A nonzero biased independent channel preserves and reflects equality of
interventional event probabilities.  The two models may use different latent
spaces.  Finite pushforward semantics aligns the event with its prior signal;
the probability-record theorem then cancels the nonzero channel bias. -/
theorem FiniteLatentSCM.noisyInterventionalSignal_equiv_iff_of_bias
    (left right : FiniteLatentSCM S)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (event : S.Assignment -> Bool) (noise : FiniteProbRecord Bool)
    (gap : Nat) (gapPositive : 0 < gap)
    (bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass noise.atoms id + gap) :
    QProb.Equiv ((left.noisyInterventionalSignal intervention event noise).probVal id)
      ((right.noisyInterventionalSignal intervention event noise).probVal id) ↔
      QProb.Equiv (left.interventionalValue intervention event)
        (right.interventionalValue intervention event) := by
  have channel := FiniteProbRecord.xorChannel_probVal_equiv_iff_of_bias
    left.prior (fun latent => event (left.evalUnder intervention latent))
    right.prior (fun latent => event (right.evalUnder intervention latent)) noise gap gapPositive bias
  constructor
  · intro equivalent
    exact QProb.equiv_trans (left.interventionalValue_eq intervention event)
      (QProb.equiv_trans (channel.mp equivalent)
        (QProb.equiv_symm (right.interventionalValue_eq intervention event)))
  · intro equivalent
    exact channel.mpr
      (QProb.equiv_trans (QProb.equiv_symm (left.interventionalValue_eq intervention event))
        (QProb.equiv_trans equivalent (right.interventionalValue_eq intervention event)))

/-- Separation survives any finite sequence of private biased flips.  Count
zero retains the unsoftened signal, while a positive count can provide support
for both Boolean outputs when the flip weight is positive. -/
theorem FiniteLatentSCM.noisyInterventionalSignal_not_equiv
    (left right : FiniteLatentSCM S)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (event : S.Assignment -> Bool)
    (flip gap : Nat) (gapPositive : 0 < gap) (count : Nat)
    (separated : Not (QProb.Equiv (left.interventionalValue intervention event)
      (right.interventionalValue intervention event))) :
    Not (QProb.Equiv
      ((left.noisyInterventionalSignal intervention event
        (FiniteProbRecord.biasedFlipParity flip gap gapPositive count)).probVal id)
      ((right.noisyInterventionalSignal intervention event
        (FiniteProbRecord.biasedFlipParity flip gap gapPositive count)).probVal id)) := by
  intro equivalent
  exact separated ((FiniteLatentSCM.noisyInterventionalSignal_equiv_iff_of_bias left right
    intervention event (FiniteProbRecord.biasedFlipParity flip gap gapPositive count)
    (gap ^ count) (Nat.pow_pos gapPositive)
    (FiniteProbRecord.biasedFlipParity_bias flip gap gapPositive count)).mp equivalent)

/-! ## Full-alphabet support rather than Boolean-only positivity -/

/-- Encode a noisy Boolean signal with an independent observed-value
background.  A bit-zero output retains all non-`second` background labels;
the carrier's reconstruction law also realizes the distinguished `second`. -/
def hedgeNoisyCarrierDistribution (rich : ObservedSignature.ValueRich S)
    (child : Fin S.count) (signalRecord : FiniteProbRecord Ω) (signal : Ω -> Bool)
    (noise : FiniteProbRecord Bool) (background : FiniteProbRecord (S.Value child)) :
    FiniteProbRecord (S.Value child) :=
  ((signalRecord.xorChannel signal noise).product background).map
    (fun pair => hedgeParityCarrierValue rich child pair.1 pair.2)

/-- Every observed value receives positive mass once both signal bits and
every background label have positive mass.  The proof exhibits a positive
rectangle in the carrier's preimage; no support point is chosen from an
existential proposition. -/
theorem hedgeNoisyCarrierDistribution_positive
    (rich : ObservedSignature.ValueRich S) (child : Fin S.count)
    (signalRecord : FiniteProbRecord Ω) (signal : Ω -> Bool)
    (noise : FiniteProbRecord Bool) (background : FiniteProbRecord (S.Value child))
    (bitPositive : forall bit, (signalRecord.xorChannel signal noise).EventPositive
      (FiniteProbRecord.singletonEvent bit))
    (backgroundPositive : forall value, background.EventPositive (FiniteProbRecord.singletonEvent value))
    (value : S.Value child) :
    (hedgeNoisyCarrierDistribution rich child signalRecord signal noise background).EventPositive
      (FiniteProbRecord.singletonEvent value) := by
  let bit := hedgeIsSecond rich child value
  let bitRecord := signalRecord.xorChannel signal noise
  let rectangle := fun pair : Bool × S.Value child =>
    FiniteProbRecord.singletonEvent bit pair.1 && FiniteProbRecord.singletonEvent value pair.2
  let carrier := fun pair : Bool × S.Value child => hedgeParityCarrierValue rich child pair.1 pair.2
  have rectanglePositive : 0 < FiniteProbRecord.eventMass (bitRecord.product background).atoms rectangle := by
    rw [FiniteProbRecord.product, FiniteProbRecord.eventMass_weightedCartesian]
    exact Nat.mul_pos (bitPositive bit) (backgroundPositive value)
  have included : forall pair, rectangle pair = true ->
      FiniteProbRecord.singletonEvent value (carrier pair) = true := by
    intro pair selected
    have bits := Bool.and_eq_true_iff.mp selected
    have sameBit : pair.1 = bit := of_decide_eq_true bits.1
    have sameValue : pair.2 = value := of_decide_eq_true bits.2
    change decide (hedgeParityCarrierValue rich child pair.1 pair.2 = value) = true
    rw [sameBit, sameValue]
    exact decide_eq_true (hedgeParityCarrierValue_reconstruct rich child value)
  have bound := FiniteProbRecord.eventMass_mono (bitRecord.product background).atoms rectangle
    (fun pair => FiniteProbRecord.singletonEvent value (carrier pair)) included
  have positive := Nat.lt_of_lt_of_le rectanglePositive bound
  have mapped := FiniteProbRecord.eventMass_map_labels (bitRecord.product background).atoms
    carrier (FiniteProbRecord.singletonEvent value)
  change 0 < FiniteProbRecord.eventMass
    ((bitRecord.product background).atoms.map (fun atom => (carrier atom.1, atom.2)))
    (FiniteProbRecord.singletonEvent value)
  rw [mapped]
  exact positive

/-- An arbitrary nonempty number of independent biased flips supplies the bit support
required by the full-alphabet carrier.  Only the background's genuine finite
support remains a premise; no binary-only value restriction is introduced. -/
theorem hedgeNoisyCarrierDistribution_biasedFlipParity_positive
    (rich : ObservedSignature.ValueRich S) (child : Fin S.count)
    (signalRecord : FiniteProbRecord Ω) (signal : Ω -> Bool)
    (flip gap : Nat) (gapPositive : 0 < gap) (flipPositive : 0 < flip) (count : Nat)
    (background : FiniteProbRecord (S.Value child))
    (backgroundPositive : forall value, background.EventPositive (FiniteProbRecord.singletonEvent value))
    (value : S.Value child) :
    (hedgeNoisyCarrierDistribution rich child signalRecord signal
      (FiniteProbRecord.biasedFlipParity flip gap gapPositive (count + 1)) background).EventPositive
      (FiniteProbRecord.singletonEvent value) :=
  hedgeNoisyCarrierDistribution_positive rich child signalRecord signal _ background
    (FiniteProbRecord.xorChannel_biasedFlipParity_positive signalRecord signal flip gap gapPositive flipPositive count)
    backgroundPositive value

/-! ## The existing hedge separation tolerates every finite private-noise count -/

/-- The positive carrier pair's root-parity gap survives arbitrary finite
biased softening.  This is a signal theorem at the original intervention, not
a claim that the root event has already been routed to the original outcome. -/
theorem HedgeWitness.carrierDefectRootParity_noisy_not_equiv
    {S : ObservedSignature.{0}} {G : ObservedGraph S} {query : JointKernelQuery S}
    (witness : HedgeWitness G query) (rich : ObservedSignature.ValueRich S)
    (flip gap : Nat) (gapPositive : 0 < gap) (count : Nat) :
    Not (QProb.Equiv
      (((witness.largeCarrierDefectParityModel rich).noisyInterventionalSignal
        (hedgeDoSecond rich query.action) (hedgeRootParityEvent rich witness.roots)
        (FiniteProbRecord.biasedFlipParity flip gap gapPositive count)).probVal id)
      (((witness.smallCarrierDefectParityModel rich).noisyInterventionalSignal
        (hedgeDoSecond rich query.action) (hedgeRootParityEvent rich witness.roots)
        (FiniteProbRecord.biasedFlipParity flip gap gapPositive count)).probVal id)) :=
  FiniteLatentSCM.noisyInterventionalSignal_not_equiv _ _ _ _ flip gap gapPositive count
    (witness.carrierDefectParityModels_rootParity_not_equiv_doSecond rich)

end Causality
end Thesis
