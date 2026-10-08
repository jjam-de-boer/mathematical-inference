import Thesis.Probability.ColliderChannel

namespace Thesis
namespace Probability
namespace ColliderChannel

/-!
# Probability transport for an actually realized collider channel

An observed-arrow collider and a shared-latent collider have different typed
SCM mechanisms, but the same finite posterior calculation.  This layer
separates that calculation from graph geometry without assuming that an SCM
is automatically a channel.  A realization must supply the actual prior's
all-event encoding law and pointwise equations for its evidence and readout.
Concrete model modules prove those fields from their installed mechanisms.

The posterior uses the actual record and actual evidence.  Both masses are
transported before division, with each source context's own support and
denominator.  No equal-denominator premise, coupling, choice of latent unit,
or quotient of unsupported evidence is hidden in this interface.
-/

variable {Ω : Type u} {Λ : Type v}

/-- Checked encoding data for one actual finite record, conditioning event,
and parent-bit readout.  The evidence and readout equations hold at every
encoded input, not just at one selected supported atom. -/
structure Realization (source : FiniteProbRecord Ω) (signal context : Event Ω)
    (noise : FiniteProbRecord Bool) (value : Bool) (actual : FiniteProbRecord Λ)
    (actualEvidence : Event Λ) (actualReadout : Λ -> Bool) where
  encode : Input Ω -> Λ
  prior_probVal : forall event : Event Λ,
    QProb.Equiv (actual.probVal event)
      ((prior source noise).probVal (fun input => event (encode input)))
  evidence_encode : forall input,
    actualEvidence (encode input) = evidence signal context value input
  readout_encode : forall input, actualReadout (encode input) = input.2

namespace Realization

variable {source : FiniteProbRecord Ω} {signal context : Event Ω}
  {noise : FiniteProbRecord Bool} {value : Bool} {actual : FiniteProbRecord Λ}
  {actualEvidence : Event Λ} {actualReadout : Λ -> Bool}

theorem evidence_probVal
    (realized : Realization source signal context noise value actual actualEvidence actualReadout) :
    QProb.Equiv (actual.probVal actualEvidence)
      ((prior source noise).probVal (evidence signal context value)) :=
  QProb.equiv_trans (realized.prior_probVal actualEvidence)
    ((prior source noise).probVal_congr _ _ realized.evidence_encode)

theorem joint_probVal
    (realized : Realization source signal context noise value actual actualEvidence actualReadout)
    (event : Event Bool) :
    QProb.Equiv (actual.probVal (fun unit => actualEvidence unit && event (actualReadout unit)))
      ((prior source noise).probVal (fun input => evidence signal context value input && event input.2)) :=
  QProb.equiv_trans (realized.prior_probVal _)
    ((prior source noise).probVal_congr _ _ (fun input => by
      rw [realized.evidence_encode, realized.readout_encode]))

/-- A supported source context supplies actual evidence support through the
proved fair-mask channel law, not through an assumed SCM support property. -/
theorem evidence_positive
    (realized : Realization source signal context noise value actual actualEvidence actualReadout)
    (supported : source.EventPositive context) : actual.EventPositive actualEvidence :=
  (QProb.equiv_num_pos_iff realized.evidence_probVal).mpr
    (ColliderChannel.evidence_positive source signal context supported noise value)

def posterior
    (realized : Realization source signal context noise value actual actualEvidence actualReadout)
    (supported : source.EventPositive context) : FiniteProbRecord Bool :=
  (actual.conditionOn actualEvidence (realized.evidence_positive supported)).map actualReadout

/-- Full-event equality of the actual posterior and the independently
computed channel posterior.  Numerator and denominator are both justified
by the encoding, before their supported quotient is compared. -/
theorem posterior_probVal
    (realized : Realization source signal context noise value actual actualEvidence actualReadout)
    (supported : source.EventPositive context) (event : Event Bool) :
    QProb.Equiv ((realized.posterior supported).probVal event)
      ((ColliderChannel.posterior source signal context supported noise value).probVal event) := by
  let actualPositive := realized.evidence_positive supported
  let channel := prior source noise
  let channelEvidence := evidence signal context value
  let channelPositive := ColliderChannel.evidence_positive source signal context supported noise value
  have actualMap := (actual.conditionOn actualEvidence actualPositive).map_probVal actualReadout event
  have actualRatio := actual.conditionOn_probVal actualEvidence (fun unit => event (actualReadout unit)) actualPositive
  have channelMap := (channel.conditionOn channelEvidence channelPositive).map_probVal (fun input => input.2) event
  have channelRatio := channel.conditionOn_probVal channelEvidence (fun input => event input.2) channelPositive
  have ratios := QProb.div_congr (realized.joint_probVal event) realized.evidence_probVal actualPositive channelPositive
  exact QProb.equiv_trans actualMap (QProb.equiv_trans actualRatio
    (QProb.equiv_trans ratios (QProb.equiv_symm (QProb.equiv_trans channelMap channelRatio))))

theorem posterior_positive
    (realized : Realization source signal context noise value actual actualEvidence actualReadout)
    (supported : source.EventPositive context)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit)) (bit : Bool) :
    (realized.posterior supported).EventPositive (FiniteProbRecord.singletonEvent bit) :=
  (QProb.equiv_num_pos_iff (realized.posterior_probVal supported (FiniteProbRecord.singletonEvent bit))).mpr
    (ColliderChannel.posterior_positive source signal context supported noise noisePositive value bit)

/-- Bias reflects the original contextual source gap through two separately
realized actual posteriors.  Both source and actual carriers may differ. -/
theorem posterior_probVal_equiv_iff_of_bias
    {Ω' : Type u'} {Λ' : Type v'}
    {rightSource : FiniteProbRecord Ω'} {rightSignal rightContext : Event Ω'}
    {rightActual : FiniteProbRecord Λ'} {rightEvidence : Event Λ'} {rightReadout : Λ' -> Bool}
    (left : Realization source signal context noise value actual actualEvidence actualReadout)
    (right : Realization rightSource rightSignal rightContext noise value rightActual rightEvidence rightReadout)
    (leftSupported : source.EventPositive context) (rightSupported : rightSource.EventPositive rightContext)
    (gap : Nat) (positive : 0 < gap)
    (bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass noise.atoms id + gap) :
    QProb.Equiv ((left.posterior leftSupported).probVal id) ((right.posterior rightSupported).probVal id) ↔
      QProb.Equiv
        ((source.conditionOn context leftSupported).probVal (fun old => Bool.xor (signal old) value))
        ((rightSource.conditionOn rightContext rightSupported).probVal (fun old => Bool.xor (rightSignal old) value)) := by
  have leftLaw := left.posterior_probVal leftSupported id
  have rightLaw := right.posterior_probVal rightSupported id
  have channel := ColliderChannel.posterior_probVal_equiv_iff_of_bias source signal context leftSupported
    rightSource rightSignal rightContext rightSupported noise value gap positive bias
  constructor
  · intro equal
    exact channel.mp (QProb.equiv_trans (QProb.equiv_symm leftLaw) (QProb.equiv_trans equal rightLaw))
  · intro equal
    exact QProb.equiv_trans leftLaw (QProb.equiv_trans (channel.mpr equal) (QProb.equiv_symm rightLaw))

end Realization
end ColliderChannel
end Probability
end Thesis
