import Thesis.Probability.FiniteRecord

namespace Thesis
namespace Probability
namespace FiniteProbRecord

/-!
# Finite biased-noise channels for parity signals

A private bit flip restores support only if both flip values have positive
mass.  It preserves a parity gap only if those values are not equiprobable.
This module makes both requirements explicit at natural event-mass level.
There are no limits, real parameters, or informal small-epsilon arguments.

`xorChannel` independently pairs an arbitrary finite signal with an explicit
Boolean noise record.  If the false-noise mass exceeds the true-noise mass by
`gap`, its output numerator is `gap * signalMass + trueNoiseMass * signalDen`.
Positive `gap` makes this affine channel injective on rational probabilities.

For a finite family of independent coins, the accumulated parity bias is the
product of their biases.  The homogeneous family below uses any natural flip
weight and any positive excess stay weight; after `count` coins the excess is
exactly `gap ^ count`.  Thus an arbitrary finite route does not erase a signal
merely because it contains several private flips.

These are probability-record theorems, not an automatic transformation of
causal models.  Applying them to a routed hedge still requires graph-compatible
mechanisms and a proof of observational equivalence for those mechanisms.
-/

/-! ## Boolean partitions and independent XOR event masses -/

/-- A Boolean event and its complement partition the complete finite mass.
Repeated labels and zero atom weights are allowed. -/
theorem eventMass_add_complement (atoms : List (Ω × Nat)) (event : Event Ω) :
    eventMass atoms event + eventMass atoms (fun value => !(event value)) = totalMass atoms := by
  induction atoms with
  | nil => rfl
  | cons atom atoms inductionHypothesis =>
      rcases atom with ⟨value, weight⟩
      cases selected : event value <;>
        simp only [eventMass, totalMass, selected, Bool.not_false, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Complementing the compared events preserves and reflects equality of
their actual normalized probabilities.  The source spaces and denominators
may differ.  Each Boolean partition sums to its own complete record mass,
so no equality of evidence probabilities or chosen coupling is needed. -/
theorem probVal_complement_equiv_iff (left : FiniteProbRecord Ω) (leftEvent : Event Ω)
    (right : FiniteProbRecord X) (rightEvent : Event X) :
    QProb.Equiv (left.probVal (fun value => !leftEvent value)) (right.probVal (fun value => !rightEvent value)) ↔
      QProb.Equiv (left.probVal leftEvent) (right.probVal rightEvent) := by
  have leftTotal := congrArg (fun mass => mass * right.den)
    ((eventMass_add_complement left.atoms leftEvent).trans left.total_mass)
  have rightTotal := congrArg (fun mass => mass * left.den)
    ((eventMass_add_complement right.atoms rightEvent).trans right.total_mass)
  simp only [Nat.add_mul] at leftTotal rightTotal
  have common : left.den * right.den = right.den * left.den := Nat.mul_comm _ _
  constructor
  · intro equal
    change eventMass left.atoms (fun value => !leftEvent value) * right.den =
      eventMass right.atoms (fun value => !rightEvent value) * left.den at equal
    change eventMass left.atoms leftEvent * right.den = eventMass right.atoms rightEvent * left.den
    omega
  · intro equal
    change eventMass left.atoms leftEvent * right.den = eventMass right.atoms rightEvent * left.den at equal
    change eventMass left.atoms (fun value => !leftEvent value) * right.den =
      eventMass right.atoms (fun value => !rightEvent value) * left.den
    omega

/-- The two ways to obtain odd XOR parity are disjoint rectangular events.
The formula is exact for arbitrary records and needs no equality decision on
the signal's sample type. -/
theorem eventMass_weightedCartesian_xor (atoms : List (Ω × Nat))
    (noise : List (Bool × Nat)) (signal : Event Ω) :
    eventMass (weightedCartesian atoms noise) (fun pair => Bool.xor (signal pair.1) pair.2) =
      eventMass atoms signal * eventMass noise (fun bit => !bit) +
        eventMass atoms (fun value => !(signal value)) * eventMass noise id := by
  induction atoms with
  | nil => simp only [weightedCartesian, List.flatMap_nil, eventMass, Nat.zero_mul, Nat.zero_add]
  | cons atom atoms inductionHypothesis =>
      rcases atom with ⟨value, weight⟩
      change eventMass
        (noise.map (fun atom => ((value, atom.1), weight * atom.2)) ++ weightedCartesian atoms noise)
        (fun pair => Bool.xor (signal pair.1) pair.2) = _
      rw [eventMass_append, eventMass_map_weight noise (fun bit => (value, bit)) weight,
        inductionHypothesis]
      cases selected : signal value <;>
        simp only [eventMass, selected, Bool.not_false, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, Bool.false_xor, Bool.true_xor, Nat.add_mul] <;> ac_rfl

/-- Add independent Boolean noise to any finite Boolean signal.  The explicit
product is the independence assumption; it is not inferred from marginal laws. -/
def xorChannel (signalRecord : FiniteProbRecord Ω) (signal : Event Ω)
    (noise : FiniteProbRecord Bool) : FiniteProbRecord Bool :=
  (signalRecord.product noise).map (fun pair => Bool.xor (signal pair.1) pair.2)

/-- Exact odd output mass, before any rational normalization. -/
theorem xorChannel_true_mass (signalRecord : FiniteProbRecord Ω) (signal : Event Ω)
    (noise : FiniteProbRecord Bool) :
    eventMass (xorChannel signalRecord signal noise).atoms id =
      eventMass signalRecord.atoms signal * eventMass noise.atoms (fun bit => !bit) +
        eventMass signalRecord.atoms (fun value => !(signal value)) * eventMass noise.atoms id := by
  exact (eventMass_map_labels (signalRecord.product noise).atoms
    (fun pair => Bool.xor (signal pair.1) pair.2) id).trans
      (eventMass_weightedCartesian_xor _ _ _)

/-- The appended-source SCM prior samples noise before the old latent unit.
Expanding that order gives the same two XOR rectangles as the signal-first
channel, with the factors reversed.  No general record-permutation axiom or
assumed independence of marginals is used. -/
theorem eventMass_weightedCartesian_xor_noise_first (noise : List (Bool × Nat))
    (atoms : List (Ω × Nat)) (signal : Event Ω) :
    eventMass (weightedCartesian noise atoms) (fun pair => Bool.xor (signal pair.2) pair.1) =
      eventMass noise (fun bit => !bit) * eventMass atoms signal +
        eventMass noise id * eventMass atoms (fun value => !(signal value)) := by
  induction noise with
  | nil => simp only [weightedCartesian, List.flatMap_nil, eventMass, Nat.zero_mul, Nat.zero_add]
  | cons atom rest inductionHypothesis =>
      rcases atom with ⟨bit, weight⟩
      change eventMass
        (atoms.map (fun atom => ((bit, atom.1), weight * atom.2)) ++ weightedCartesian rest atoms)
        (fun pair => Bool.xor (signal pair.2) pair.1) = _
      rw [eventMass_append, eventMass_map_weight atoms (fun value => (bit, value)) weight,
        inductionHypothesis]
      cases bit <;>
        simp only [eventMass, id_eq, Bool.not_false, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, Bool.xor_false, Bool.xor_true, Nat.add_mul] <;> ac_rfl

/-- Realizing the same independent XOR channel in noise-first order agrees
with `xorChannel` at the observed signal event.  Unequal denominators and
zero or deterministic masses are allowed. -/
theorem xorChannel_noise_first_probVal (signalRecord : FiniteProbRecord Ω) (signal : Event Ω)
    (noise : FiniteProbRecord Bool) :
    QProb.Equiv
      ((noise.product signalRecord).probVal (fun pair => Bool.xor (signal pair.2) pair.1))
      ((signalRecord.xorChannel signal noise).probVal id) := by
  change eventMass (weightedCartesian noise.atoms signalRecord.atoms)
      (fun pair => Bool.xor (signal pair.2) pair.1) * (signalRecord.den * noise.den) =
    eventMass (signalRecord.xorChannel signal noise).atoms id * (noise.den * signalRecord.den)
  rw [eventMass_weightedCartesian_xor_noise_first, xorChannel_true_mass]
  ac_rfl

/-- Complementing the output bit is the same as complementing the input
signal before XOR with the same independent noise. -/
theorem xorChannel_false_mass (signalRecord : FiniteProbRecord Ω) (signal : Event Ω)
    (noise : FiniteProbRecord Bool) :
    eventMass (xorChannel signalRecord signal noise).atoms (fun bit => !bit) =
      eventMass (xorChannel signalRecord (fun value => !(signal value)) noise).atoms id := by
  calc
    _ = eventMass (signalRecord.product noise).atoms
        (fun pair => !(Bool.xor (signal pair.1) pair.2)) :=
      eventMass_map_labels (signalRecord.product noise).atoms
        (fun pair => Bool.xor (signal pair.1) pair.2) (fun bit => !bit)
    _ = eventMass (signalRecord.product noise).atoms
        (fun pair => Bool.xor (!(signal pair.1)) pair.2) := by
      apply eventMass_congr
      intro pair
      cases signal pair.1 <;> cases pair.2 <;> rfl
    _ = _ := (eventMass_map_labels (signalRecord.product noise).atoms
      (fun pair => Bool.xor (!(signal pair.1)) pair.2) id).symm

/-- Under a prescribed excess false-noise mass, the channel has an exact
affine numerator.  Complementary signal mass is eliminated by normalization,
so the formula remains valid at probabilities zero and one. -/
theorem xorChannel_true_mass_of_bias (signalRecord : FiniteProbRecord Ω) (signal : Event Ω)
    (noise : FiniteProbRecord Bool) (gap : Nat)
    (bias : eventMass noise.atoms (fun bit => !bit) = eventMass noise.atoms id + gap) :
    eventMass (xorChannel signalRecord signal noise).atoms id =
      gap * eventMass signalRecord.atoms signal + eventMass noise.atoms id * signalRecord.den := by
  have partition := eventMass_add_complement signalRecord.atoms signal
  rw [signalRecord.total_mass] at partition
  rw [xorChannel_true_mass, bias, ← partition]
  simp only [Nat.mul_add]
  ac_rfl

/-- A nonzero biased independent channel preserves and reflects equality of
signal probabilities, even for different sample spaces and denominators.
The cancellation is over natural cross-products; no subtraction or selection
of representatives of rational equivalence classes is needed. -/
theorem xorChannel_probVal_equiv_iff_of_bias
    (left : FiniteProbRecord Ω) (leftSignal : Event Ω)
    (right : FiniteProbRecord X) (rightSignal : Event X)
    (noise : FiniteProbRecord Bool) (gap : Nat) (gapPositive : 0 < gap)
    (bias : eventMass noise.atoms (fun bit => !bit) = eventMass noise.atoms id + gap) :
    QProb.Equiv ((xorChannel left leftSignal noise).probVal id)
      ((xorChannel right rightSignal noise).probVal id) ↔
      QProb.Equiv (left.probVal leftSignal) (right.probVal rightSignal) := by
  change eventMass (xorChannel left leftSignal noise).atoms id * (right.den * noise.den) =
    eventMass (xorChannel right rightSignal noise).atoms id * (left.den * noise.den) ↔ _
  rw [xorChannel_true_mass_of_bias left leftSignal noise gap bias,
    xorChannel_true_mass_of_bias right rightSignal noise gap bias]
  constructor
  · intro equivalent
    have multiplied :
        ((gap * eventMass left.atoms leftSignal + eventMass noise.atoms id * left.den) * right.den) * noise.den =
          ((gap * eventMass right.atoms rightSignal + eventMass noise.atoms id * right.den) * left.den) * noise.den := by
      simpa only [Nat.mul_assoc] using equivalent
    have unscaled := Nat.eq_of_mul_eq_mul_right noise.den_pos multiplied
    simp only [Nat.add_mul, Nat.mul_assoc] at unscaled
    have expanded :
        gap * (eventMass left.atoms leftSignal * right.den) +
            eventMass noise.atoms id * (left.den * right.den) =
          gap * (eventMass right.atoms rightSignal * left.den) +
            eventMass noise.atoms id * (left.den * right.den) := by
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using unscaled
    exact Nat.eq_of_mul_eq_mul_left gapPositive (Nat.add_right_cancel expanded)
  · intro equivalent
    change eventMass left.atoms leftSignal * right.den = eventMass right.atoms rightSignal * left.den at equivalent
    have expanded :
        (gap * eventMass left.atoms leftSignal + eventMass noise.atoms id * left.den) * right.den =
          (gap * eventMass right.atoms rightSignal + eventMass noise.atoms id * right.den) * left.den := by
      simp only [Nat.add_mul, Nat.mul_assoc, equivalent]
      ac_rfl
    simpa only [Nat.mul_assoc] using congrArg (fun mass => mass * noise.den) expanded

/-- Balanced independent noise erases every Boolean probability difference.
This records why full support alone is insufficient for a hedge countermodel:
the channel's nonzero bias, not merely its positive atom weights, is essential. -/
theorem xorChannel_probVal_equiv_of_balanced
    (left : FiniteProbRecord Ω) (leftSignal : Event Ω)
    (right : FiniteProbRecord X) (rightSignal : Event X)
    (noise : FiniteProbRecord Bool)
    (balanced : eventMass noise.atoms (fun bit => !bit) = eventMass noise.atoms id) :
    QProb.Equiv ((xorChannel left leftSignal noise).probVal id)
      ((xorChannel right rightSignal noise).probVal id) := by
  change eventMass (xorChannel left leftSignal noise).atoms id * (right.den * noise.den) =
    eventMass (xorChannel right rightSignal noise).atoms id * (left.den * noise.den)
  have bias : eventMass noise.atoms (fun bit => !bit) = eventMass noise.atoms id + 0 := by
    simpa only [Nat.add_zero] using balanced
  rw [xorChannel_true_mass_of_bias left leftSignal noise 0 bias,
    xorChannel_true_mass_of_bias right rightSignal noise 0 bias]
  simp only [Nat.zero_mul, Nat.zero_add]
  ac_rfl

/-- The odd output has positive mass if the independent noise gives
positive mass to both its values, regardless of the input signal's support. -/
theorem xorChannel_true_positive (signalRecord : FiniteProbRecord Ω) (signal : Event Ω)
    (noise : FiniteProbRecord Bool)
    (falsePositive : 0 < eventMass noise.atoms (fun bit => !bit))
    (truePositive : 0 < eventMass noise.atoms id) :
    0 < eventMass (xorChannel signalRecord signal noise).atoms id := by
  rw [xorChannel_true_mass]
  have partition := eventMass_add_complement signalRecord.atoms signal
  rw [signalRecord.total_mass] at partition
  have first := Nat.mul_le_mul_left (eventMass signalRecord.atoms signal) falsePositive
  have second := Nat.mul_le_mul_left (eventMass signalRecord.atoms (fun value => !(signal value))) truePositive
  simp only [Nat.mul_one] at first second
  have nonempty := signalRecord.den_pos
  omega

/-- The even output has the same support guarantee, obtained by complementing
the signal rather than assuming that the signal itself has both values. -/
theorem xorChannel_false_positive (signalRecord : FiniteProbRecord Ω) (signal : Event Ω)
    (noise : FiniteProbRecord Bool)
    (falsePositive : 0 < eventMass noise.atoms (fun bit => !bit))
    (truePositive : 0 < eventMass noise.atoms id) :
    0 < eventMass (xorChannel signalRecord signal noise).atoms (fun bit => !bit) := by
  rw [xorChannel_false_mass]
  exact xorChannel_true_positive signalRecord (fun value => !(signal value)) noise falsePositive truePositive

/-- Biases multiply under independent XOR.  This is the finite family step:
the two input records need not use identical weights or denominators. -/
theorem xorChannel_bias (signalRecord noise : FiniteProbRecord Bool)
    (signalGap noiseGap : Nat)
    (signalBias : eventMass signalRecord.atoms (fun bit => !bit) = eventMass signalRecord.atoms id + signalGap)
    (noiseBias : eventMass noise.atoms (fun bit => !bit) = eventMass noise.atoms id + noiseGap) :
    eventMass (xorChannel signalRecord id noise).atoms (fun bit => !bit) =
      eventMass (xorChannel signalRecord id noise).atoms id + signalGap * noiseGap := by
  rw [xorChannel_false_mass, xorChannel_true_mass, xorChannel_true_mass]
  have doubleComplement : (fun bit : Bool => !(!(id bit))) = id := by funext bit; cases bit <;> rfl
  rw [doubleComplement]
  change eventMass signalRecord.atoms (fun bit => !bit) * eventMass noise.atoms (fun bit => !bit) +
    eventMass signalRecord.atoms id * eventMass noise.atoms id =
      eventMass signalRecord.atoms id * eventMass noise.atoms (fun bit => !bit) +
        eventMass signalRecord.atoms (fun bit => !bit) * eventMass noise.atoms id + signalGap * noiseGap
  rw [signalBias, noiseBias]
  simp only [Nat.add_mul, Nat.mul_add]
  ac_rfl

/-! ## Any finite number of independent biased flips retains nonzero bias -/

/-- A coin whose stay weight exceeds its flip weight by `gap`.
The gap alone ensures a positive denominator; positive flip weight is needed
separately when both Boolean outputs must have support. -/
def biasedFlip (flip gap : Nat) (gapPositive : 0 < gap) : FiniteProbRecord Bool where
  atoms := [(false, flip + gap), (true, flip)]
  den := (flip + gap) + flip
  den_pos := by omega
  total_mass := by simp only [totalMass, Nat.add_zero]

/-- Parity of `count` independent biased flips.  The zero-coin case is the
point mass at false, and recursion uses an actual independent product record. -/
def biasedFlipParity (flip gap : Nat) (gapPositive : 0 < gap) : Nat -> FiniteProbRecord Bool
  | 0 => ⟨[(false, 1)], 1, by decide, rfl⟩
  | count + 1 => xorChannel (biasedFlipParity flip gap gapPositive count) id (biasedFlip flip gap gapPositive)

/-- The natural excess even-parity mass is exactly the product of the coin
biases.  Consequently it cannot vanish for any finite number of flips. -/
theorem biasedFlipParity_bias (flip gap : Nat) (gapPositive : 0 < gap) (count : Nat) :
    eventMass (biasedFlipParity flip gap gapPositive count).atoms (fun bit => !bit) =
      eventMass (biasedFlipParity flip gap gapPositive count).atoms id + gap ^ count := by
  induction count with
  | zero => simp [biasedFlipParity, eventMass]
  | succ count inductionHypothesis =>
      rw [Nat.pow_succ]
      exact xorChannel_bias _ _ (gap ^ count) gap inductionHypothesis
        (by simp [biasedFlip, eventMass, Nat.add_comm])

/-- The common denominator grows by the explicit coin denominator at every
step.  This displays the quantitative attenuation without real-valued limits. -/
theorem biasedFlipParity_den (flip gap : Nat) (gapPositive : 0 < gap) (count : Nat) :
    (biasedFlipParity flip gap gapPositive count).den = ((flip + gap) + flip) ^ count := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      change (biasedFlipParity flip gap gapPositive count).den * ((flip + gap) + flip) = _
      rw [inductionHypothesis, Nat.pow_succ]

/-- Even parity always has positive mass, including the zero-coin case. -/
theorem biasedFlipParity_false_positive (flip gap : Nat) (gapPositive : 0 < gap) (count : Nat) :
    0 < eventMass (biasedFlipParity flip gap gapPositive count).atoms (fun bit => !bit) := by
  rw [biasedFlipParity_bias]
  have excess : 0 < gap ^ count := Nat.pow_pos gapPositive
  omega

/-- With positive flip weight and at least one coin, odd parity has positive
mass too.  No positivity hypothesis on the preceding parity signal is needed. -/
theorem biasedFlipParity_true_positive (flip gap : Nat) (gapPositive : 0 < gap)
    (flipPositive : 0 < flip) (count : Nat) :
    0 < eventMass (biasedFlipParity flip gap gapPositive (count + 1)).atoms id := by
  apply xorChannel_true_positive
  · change 0 < (flip + gap)
    omega
  · exact flipPositive

/-- Positive private flip weights restore support for both Boolean output
values after any nonempty finite sequence of flips, even for a deterministic
or one-sided input signal. -/
theorem xorChannel_biasedFlipParity_positive (signalRecord : FiniteProbRecord Ω) (signal : Event Ω)
    (flip gap : Nat) (gapPositive : 0 < gap) (flipPositive : 0 < flip)
    (count : Nat) (bit : Bool) :
    (xorChannel signalRecord signal (biasedFlipParity flip gap gapPositive (count + 1))).EventPositive
      (singletonEvent bit) := by
  cases bit with
  | false =>
      have eventEqual : singletonEvent false = (fun bit : Bool => !bit) := by
        funext bit
        cases bit <;> rfl
      rw [eventEqual]
      exact xorChannel_false_positive signalRecord signal _
        (biasedFlipParity_false_positive flip gap gapPositive (count + 1))
        (biasedFlipParity_true_positive flip gap gapPositive flipPositive count)
  | true =>
      have eventEqual : singletonEvent true = (id : Bool -> Bool) := by
        funext bit
        cases bit <;> rfl
      rw [eventEqual]
      exact xorChannel_true_positive signalRecord signal _
        (biasedFlipParity_false_positive flip gap gapPositive (count + 1))
        (biasedFlipParity_true_positive flip gap gapPositive flipPositive count)

/-- Finite parity noise preserves every non-equivalence of signal
probabilities.  This is the separation step needed after private noise is
routed to a hedge's outcome parity. -/
theorem xorChannel_biasedFlipParity_not_equiv
    (left : FiniteProbRecord Ω) (leftSignal : Event Ω)
    (right : FiniteProbRecord X) (rightSignal : Event X)
    (flip gap : Nat) (gapPositive : 0 < gap) (count : Nat)
    (separated : Not (QProb.Equiv (left.probVal leftSignal) (right.probVal rightSignal))) :
    Not (QProb.Equiv
      ((xorChannel left leftSignal (biasedFlipParity flip gap gapPositive count)).probVal id)
      ((xorChannel right rightSignal (biasedFlipParity flip gap gapPositive count)).probVal id)) := by
  intro equivalent
  exact separated ((xorChannel_probVal_equiv_iff_of_bias left leftSignal right rightSignal
    (biasedFlipParity flip gap gapPositive count) (gap ^ count) (Nat.pow_pos gapPositive)
    (biasedFlipParity_bias flip gap gapPositive count)).mp equivalent)

end FiniteProbRecord
end Probability
end Thesis
