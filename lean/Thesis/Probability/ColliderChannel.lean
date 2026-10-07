import Thesis.Probability.BooleanNoise

namespace Thesis
namespace Probability

/-!
# A finite positive collider channel and its conditional signal

Let `H` be any Boolean signal, `U` an independent fair bit, and `N` an
independent noise bit.  The collider output is `Z = H xor N xor U`.
Conditioning on `Z = z` makes `U` read out `H xor z` through the same noise
channel.  The fair mask gives either collider value exactly half the mass,
even inside an arbitrary supported context event of the original record.

This is an exact finite construction, not a limiting argument: all priors
are explicit products, and every posterior is normalized with a proved
positive denominator.  The conditional comparison permits different source
spaces, different source denominators, and different context probabilities.
Biased noise preserves a conditional signal gap; balanced noise erases it.

This probability boundary is intended for the incoming-edge/collider steps
of conditional countermodel construction.  It does not assert that arbitrary
mechanism updates realize the channel, preserve observational equality, or
already yield a countermodel for a particular causal graph.  Those SCM and
graph obligations must still be proved at their own boundary.
-/

namespace ColliderChannel

open FiniteProbRecord

/-- The fair parent input is explicitly independent, with two unit atoms. -/
def fairMask : FiniteProbRecord Bool where
  atoms := [(false, 1), (true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl

/-- Source first, private noise second, and fair parent input last. -/
abbrev Input (Ω : Type u) := (Ω × Bool) × Bool

def prior (source : FiniteProbRecord Ω) (noise : FiniteProbRecord Bool) :
    FiniteProbRecord (Input Ω) :=
  (source.product noise).product fairMask

def output (signal : Event Ω) (input : Input Ω) : Bool :=
  Bool.xor (Bool.xor (signal input.1.1) input.1.2) input.2

/-- Retain the actual source context while conditioning on one collider
value.  The context is not inferred from independence of marginal laws. -/
def evidence (signal context : Event Ω) (value : Bool) : Event (Input Ω) :=
  fun input => context input.1.1 && decide (output signal input = value)

/-! ## Natural event masses before normalization -/

/-- For each source atom exactly one fair mask produces the requested
output.  The mask's weight is one, so no subtraction or division is needed. -/
private theorem masked_mass (atoms : List (Ω × Nat)) (signal context : Event Ω) (value : Bool) :
    eventMass (weightedCartesian atoms fairMask.atoms)
      (fun pair => context pair.1 && decide (Bool.xor (signal pair.1) pair.2 = value)) =
      eventMass atoms context := by
  induction atoms with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      rcases atom with ⟨sample, weight⟩
      change eventMass
        (fairMask.atoms.map (fun atom => ((sample, atom.1), weight * atom.2)) ++
          weightedCartesian rest fairMask.atoms) _ = _
      rw [eventMass_append, eventMass_map_weight, inductionHypothesis]
      cases selected : context sample <;> cases bit : signal sample <;> cases value <;>
        simp [fairMask, eventMass, selected, bit]

/-- On the same fibre, the selected mask is `signal xor value`.  This
identity holds for every Boolean output event, not just the true singleton. -/
private theorem masked_joint_mass (atoms : List (Ω × Nat))
    (signal context : Event Ω) (value : Bool) (event : Event Bool) :
    eventMass (weightedCartesian atoms fairMask.atoms)
      (fun pair => (context pair.1 && decide (Bool.xor (signal pair.1) pair.2 = value)) && event pair.2) =
      eventMass atoms (fun sample => context sample && event (Bool.xor (signal sample) value)) := by
  induction atoms with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      rcases atom with ⟨sample, weight⟩
      change eventMass
        (fairMask.atoms.map (fun atom => ((sample, atom.1), weight * atom.2)) ++
          weightedCartesian rest fairMask.atoms) _ = _
      rw [eventMass_append, eventMass_map_weight, inductionHypothesis]
      cases selected : context sample <;> cases bit : signal sample <;> cases value <;>
        cases falseEvent : event false <;> cases trueEvent : event true <;>
        simp [fairMask, eventMass, selected, bit, falseEvent, trueEvent]

/-- Conditioning a source factor can be moved inside its explicit product
at event-mass level.  The other factor may occur anywhere in the event. -/
private theorem product_context_mass (atoms : List (Ω × Nat)) (other : List (X × Nat))
    (context : Event Ω) (event : Event (Ω × X)) :
    eventMass (weightedCartesian atoms other) (fun pair => context pair.1 && event pair) =
      eventMass (weightedCartesian (atoms.filter (fun atom => context atom.1)) other) event := by
  induction atoms with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      rcases atom with ⟨sample, weight⟩
      simp only [weightedCartesian, List.flatMap_cons, eventMass_append, eventMass_map_weight]
      cases selected : context sample with
      | false =>
          simp only [List.filter_cons, selected, Bool.false_eq_true, ↓reduceIte]
          have empty : eventMass other (fun value => false && event (sample, value)) = 0 := by
            simpa only [Bool.false_and] using eventMass_false other
          rw [empty, Nat.mul_zero, Nat.zero_add]
          exact inductionHypothesis
      | true =>
          simp only [List.filter_cons, selected, ↓reduceIte,
            List.flatMap_cons, eventMass_append, eventMass_map_weight]
          have same : eventMass other (fun value => true && event (sample, value)) =
              eventMass other (fun value => event (sample, value)) := by
            apply eventMass_congr
            intro value
            rw [Bool.true_and]
          rw [same]
          exact congrArg (fun mass => weight * eventMass other (fun value => event (sample, value)) + mass)
            inductionHypothesis

/-- The collider event has mass `contextMass * noiseDen`, independently of
the signal and the chosen collider value.  Its prior denominator additionally
contains the fair mask's factor two. -/
theorem evidence_mass (source : FiniteProbRecord Ω) (signal context : Event Ω)
    (noise : FiniteProbRecord Bool) (value : Bool) :
    eventMass (prior source noise).atoms (evidence signal context value) =
      eventMass source.atoms context * noise.den := by
  change eventMass
    (weightedCartesian (weightedCartesian source.atoms noise.atoms) fairMask.atoms)
    (fun pair => context pair.1.1 && decide (Bool.xor (Bool.xor (signal pair.1.1) pair.1.2) pair.2 = value)) = _
  rw [masked_mass (weightedCartesian source.atoms noise.atoms)
    (fun pair => Bool.xor (signal pair.1) pair.2) (fun pair => context pair.1) value]
  have integrate := eventMass_weightedCartesian source.atoms noise.atoms context topEvent
  simpa only [topEvent, Bool.and_true, eventMass_top, noise.total_mass] using integrate

/-- Every supported source context gives a supported collider observation,
even when the source signal or private noise is deterministic. -/
theorem evidence_positive (source : FiniteProbRecord Ω) (signal context : Event Ω)
    (supported : source.EventPositive context) (noise : FiniteProbRecord Bool) (value : Bool) :
    (prior source noise).EventPositive (evidence signal context value) := by
  change 0 < eventMass (prior source noise).atoms (evidence signal context value)
  rw [evidence_mass]
  exact Nat.mul_pos supported noise.den_pos

/-- The true posterior numerator is actually the complete noisy signal
record's event mass.  Retaining arbitrary `event` also covers the false bit. -/
theorem joint_mass (source : FiniteProbRecord Ω) (signal context : Event Ω)
    (supported : source.EventPositive context) (noise : FiniteProbRecord Bool)
    (value : Bool) (event : Event Bool) :
    eventMass (prior source noise).atoms (fun input => evidence signal context value input && event input.2) =
      eventMass ((source.conditionOn context supported).xorChannel
        (fun sample => Bool.xor (signal sample) value) noise).atoms event := by
  change eventMass
    (weightedCartesian (weightedCartesian source.atoms noise.atoms) fairMask.atoms)
    (fun pair => (context pair.1.1 &&
      decide (Bool.xor (Bool.xor (signal pair.1.1) pair.1.2) pair.2 = value)) && event pair.2) = _
  rw [masked_joint_mass (weightedCartesian source.atoms noise.atoms)
    (fun pair => Bool.xor (signal pair.1) pair.2) (fun pair => context pair.1) value event]
  have mapped := eventMass_map_labels
    (weightedCartesian (source.atoms.filter (fun atom => context atom.1)) noise.atoms)
    (fun pair : Ω × Bool => Bool.xor (Bool.xor (signal pair.1) value) pair.2) event
  change _ = eventMass
    ((weightedCartesian (source.atoms.filter (fun atom => context atom.1)) noise.atoms).map
      (fun atom => (Bool.xor (Bool.xor (signal atom.1.1) value) atom.1.2, atom.2))) event
  rw [mapped, ← product_context_mass source.atoms noise.atoms context]
  apply eventMass_congr
  intro pair
  have commute : Bool.xor (Bool.xor (signal pair.1) pair.2) value =
      Bool.xor (Bool.xor (signal pair.1) value) pair.2 := by
    cases signal pair.1 <;> cases pair.2 <;> cases value <;> rfl
  rw [commute]

private theorem noisy_signal_positive (source : FiniteProbRecord Ω) (signal : Event Ω)
    (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (singletonEvent bit)) (bit : Bool) :
    (source.xorChannel signal noise).EventPositive (singletonEvent bit) := by
  have falseMass : eventMass noise.atoms (singletonEvent false) =
      eventMass noise.atoms (fun bit => !bit) :=
    eventMass_congr noise.atoms _ _ (fun bit => by cases bit <;> rfl)
  have trueMass : eventMass noise.atoms (singletonEvent true) = eventMass noise.atoms id :=
    eventMass_congr noise.atoms _ _ (fun bit => by cases bit <;> rfl)
  have falsePositive := noisePositive false
  have truePositive := noisePositive true
  change 0 < eventMass noise.atoms (singletonEvent false) at falsePositive
  change 0 < eventMass noise.atoms (singletonEvent true) at truePositive
  rw [falseMass] at falsePositive
  rw [trueMass] at truePositive
  change 0 < eventMass (source.xorChannel signal noise).atoms (singletonEvent bit)
  cases bit with
  | false =>
      rw [eventMass_congr (source.xorChannel signal noise).atoms (singletonEvent false)
        (fun bit => !bit) (fun bit => by cases bit <;> rfl)]
      exact xorChannel_false_positive source signal noise falsePositive truePositive
  | true =>
      rw [eventMass_congr (source.xorChannel signal noise).atoms (singletonEvent true)
        id (fun bit => by cases bit <;> rfl)]
      exact xorChannel_true_positive source signal noise falsePositive truePositive

/-- Every mask/collider combination has positive mass inside every supported
source context when both noise bits are supported.  No support of either
source-signal value is required, including at deterministic signal endpoints. -/
theorem joint_positive (source : FiniteProbRecord Ω) (signal context : Event Ω)
    (supported : source.EventPositive context) (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (singletonEvent bit)) (value bit : Bool) :
    (prior source noise).EventPositive
      (fun input => evidence signal context value input && singletonEvent bit input.2) := by
  change 0 < eventMass (prior source noise).atoms _
  rw [joint_mass source signal context supported noise value (singletonEvent bit)]
  exact noisy_signal_positive (source.conditionOn context supported)
    (fun sample => Bool.xor (signal sample) value) noise noisePositive bit

/-! ## Actual normalized posterior records and gap preservation -/

/-- The finite posterior of the fair parent input after seeing the collider
and the original source context.  Its positivity witness is constructed. -/
def posterior (source : FiniteProbRecord Ω) (signal context : Event Ω)
    (supported : source.EventPositive context) (noise : FiniteProbRecord Bool) (value : Bool) :
    FiniteProbRecord Bool :=
  ((prior source noise).conditionOn (evidence signal context value)
    (evidence_positive source signal context supported noise value)).map (fun input => input.2)

/-- Exact posterior masses, including its actual conditioning denominator. -/
theorem posterior_eventMass (source : FiniteProbRecord Ω) (signal context : Event Ω)
    (supported : source.EventPositive context) (noise : FiniteProbRecord Bool)
    (value : Bool) (event : Event Bool) :
    eventMass (posterior source signal context supported noise value).atoms event =
      eventMass ((source.conditionOn context supported).xorChannel
        (fun sample => Bool.xor (signal sample) value) noise).atoms event := by
  change eventMass
    (((prior source noise).atoms.filter (fun atom => evidence signal context value atom.1)).map
      (fun atom => (atom.1.2, atom.2))) event = _
  rw [eventMass_map_labels, eventMass_filter_event]
  exact joint_mass source signal context supported noise value event

/-- The denominator does not depend on the signal or the collider value;
different source contexts still have their own, potentially unequal masses. -/
theorem posterior_den (source : FiniteProbRecord Ω) (signal context : Event Ω)
    (supported : source.EventPositive context) (noise : FiniteProbRecord Bool) (value : Bool) :
    (posterior source signal context supported noise value).den =
      eventMass source.atoms context * noise.den :=
  evidence_mass source signal context noise value

/-- The actual posterior has both Boolean values under fully supported
noise, including when the source signal is deterministic inside the context. -/
theorem posterior_positive (source : FiniteProbRecord Ω) (signal context : Event Ω)
    (supported : source.EventPositive context) (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (singletonEvent bit)) (value bit : Bool) :
    (posterior source signal context supported noise value).EventPositive (singletonEvent bit) := by
  change 0 < eventMass (posterior source signal context supported noise value).atoms _
  rw [posterior_eventMass]
  exact noisy_signal_positive (source.conditionOn context supported)
    (fun sample => Bool.xor (signal sample) value) noise noisePositive bit

/-- Full-event equality of the actual posterior and the biased channel of
the conditioned source.  The two normalizing masses are proved identical;
no equality of two different source models' denominators is assumed. -/
theorem posterior_probVal (source : FiniteProbRecord Ω) (signal context : Event Ω)
    (supported : source.EventPositive context) (noise : FiniteProbRecord Bool)
    (value : Bool) (event : Event Bool) :
    QProb.Equiv ((posterior source signal context supported noise value).probVal event)
      (((source.conditionOn context supported).xorChannel
        (fun sample => Bool.xor (signal sample) value) noise).probVal event) := by
  simp only [posterior, FiniteProbRecord.map, probVal, eventMass_map_labels,
    conditionOn, eventMass_filter_event, QProb.Equiv]
  rw [joint_mass source signal context supported noise value event, evidence_mass]
  rfl

/-- Biased noise preserves and reflects a conditional source-signal gap.
Different source spaces, source denominators, and context masses are allowed.
The same selected collider value is used on both sides. -/
theorem posterior_probVal_equiv_iff_of_bias
    (left : FiniteProbRecord Ω) (leftSignal leftContext : Event Ω)
    (leftSupported : left.EventPositive leftContext)
    (right : FiniteProbRecord X) (rightSignal rightContext : Event X)
    (rightSupported : right.EventPositive rightContext)
    (noise : FiniteProbRecord Bool) (value : Bool) (gap : Nat) (positive : 0 < gap)
    (bias : eventMass noise.atoms (fun bit => !bit) = eventMass noise.atoms id + gap) :
    QProb.Equiv ((posterior left leftSignal leftContext leftSupported noise value).probVal id)
      ((posterior right rightSignal rightContext rightSupported noise value).probVal id) ↔
      QProb.Equiv ((left.conditionOn leftContext leftSupported).probVal
        (fun sample => Bool.xor (leftSignal sample) value))
        ((right.conditionOn rightContext rightSupported).probVal
          (fun sample => Bool.xor (rightSignal sample) value)) := by
  have leftLaw := posterior_probVal left leftSignal leftContext leftSupported noise value id
  have rightLaw := posterior_probVal right rightSignal rightContext rightSupported noise value id
  have channel := xorChannel_probVal_equiv_iff_of_bias
    (left.conditionOn leftContext leftSupported) (fun sample => Bool.xor (leftSignal sample) value)
    (right.conditionOn rightContext rightSupported) (fun sample => Bool.xor (rightSignal sample) value)
    noise gap positive bias
  constructor
  · intro equal
    exact channel.mp (QProb.equiv_trans (QProb.equiv_symm leftLaw) (QProb.equiv_trans equal rightLaw))
  · intro equal
    exact QProb.equiv_trans leftLaw (QProb.equiv_trans (channel.mpr equal) (QProb.equiv_symm rightLaw))

/-- A further independent biased readout also preserves the posterior gap.
This is the forward-edge step after the incoming collider: neither channel
needs the same weights or denominator as the other.  Iterated private flips
can be supplied as one accumulated `readoutNoise` record. -/
theorem posterior_readout_probVal_equiv_iff_of_bias
    (left : FiniteProbRecord Ω) (leftSignal leftContext : Event Ω)
    (leftSupported : left.EventPositive leftContext)
    (right : FiniteProbRecord X) (rightSignal rightContext : Event X)
    (rightSupported : right.EventPositive rightContext)
    (noise readoutNoise : FiniteProbRecord Bool) (value : Bool)
    (gap readoutGap : Nat) (positive : 0 < gap) (readoutPositive : 0 < readoutGap)
    (bias : eventMass noise.atoms (fun bit => !bit) = eventMass noise.atoms id + gap)
    (readoutBias : eventMass readoutNoise.atoms (fun bit => !bit) =
      eventMass readoutNoise.atoms id + readoutGap) :
    QProb.Equiv
      (((posterior left leftSignal leftContext leftSupported noise value).xorChannel id readoutNoise).probVal id)
      (((posterior right rightSignal rightContext rightSupported noise value).xorChannel id readoutNoise).probVal id) ↔
      QProb.Equiv ((left.conditionOn leftContext leftSupported).probVal
        (fun sample => Bool.xor (leftSignal sample) value))
        ((right.conditionOn rightContext rightSupported).probVal
          (fun sample => Bool.xor (rightSignal sample) value)) :=
  (xorChannel_probVal_equiv_iff_of_bias
    (posterior left leftSignal leftContext leftSupported noise value) id
    (posterior right rightSignal rightContext rightSupported noise value) id
    readoutNoise readoutGap readoutPositive readoutBias).trans
      (posterior_probVal_equiv_iff_of_bias left leftSignal leftContext leftSupported
        right rightSignal rightContext rightSupported noise value gap positive bias)

/-- Full support alone cannot carry a conditional gap: a balanced channel
erases it for every pair of source contexts, not just in an example. -/
theorem posterior_probVal_equiv_of_balanced
    (left : FiniteProbRecord Ω) (leftSignal leftContext : Event Ω)
    (leftSupported : left.EventPositive leftContext)
    (right : FiniteProbRecord X) (rightSignal rightContext : Event X)
    (rightSupported : right.EventPositive rightContext)
    (noise : FiniteProbRecord Bool) (value : Bool)
    (balanced : eventMass noise.atoms (fun bit => !bit) = eventMass noise.atoms id) :
    QProb.Equiv ((posterior left leftSignal leftContext leftSupported noise value).probVal id)
      ((posterior right rightSignal rightContext rightSupported noise value).probVal id) :=
  QProb.equiv_trans (posterior_probVal left leftSignal leftContext leftSupported noise value id)
    (QProb.equiv_trans
      (xorChannel_probVal_equiv_of_balanced
        (left.conditionOn leftContext leftSupported) (fun sample => Bool.xor (leftSignal sample) value)
        (right.conditionOn rightContext rightSupported) (fun sample => Bool.xor (rightSignal sample) value)
        noise balanced)
      (QProb.equiv_symm (posterior_probVal right rightSignal rightContext rightSupported noise value id)))

end ColliderChannel

end Probability
end Thesis
