import Thesis.CausalTransport.SharedResponseConditionalValues
import Thesis.Probability.Distros.PartialMomentConditionalBounds

namespace Thesis.Causality.SharedResponse.ConditionalRange

open Probability Probability.Distros

/-!
# Exact attained conditional ranges in the shared-root native class

Every fitted original model supplies a compatible response-table law, and
every compatible response law has an actual native realization. Both maps
preserve the evidence and joint event, hence the supported conditional value.
The partial-moment fractional optimizer can therefore return genuine native
endpoint models and construct every rational value between them.

The class is the complete-bidirected projection class already used by the
shared-root classifier. Hidden topology, finite hidden alphabets and rational
denominators remain unrestricted within that class. The result is not an
optimizer for arbitrary independent-root graphs. Positive evidence is required
only in models contributing conditional values; other fitted models may have
null evidence, and the existing evidence report remains separate.
-/

variable (S : ObservedSignature.{0})
variable (observed : FiniteProbRecord S.Assignment)
variable (intervention : HardIntervention S) (evidence event : Event S.Assignment)

def tableEvent (event : Event S.Assignment) : Event (Table S) :=
  fun table => event (eval S intervention.value table)

private theorem value_preserved (law : FiniteProbRecord (Table S))
    (original : ProjectedHiddenDAGModel (graph S))
    (same : ∀ test, QProb.Equiv (law.probVal (tableEvent S intervention test))
      (original.model.interventionalValue intervention test))
    (lawPositive : law.EventPositive (tableEvent S intervention evidence))
    (nativePositive : (original.model.interventionalDist intervention).EventPositive evidence) :
    QProb.Equiv
      ((law.conditionOn (tableEvent S intervention evidence) lawPositive).probVal (tableEvent S intervention event))
      (ConditionalValue.value S intervention evidence event original nativePositive) :=
  QProb.equiv_trans (law.conditionOn_probVal _ _ lawPositive)
    (QProb.equiv_trans
      (QProb.div_congr (same (fun sample => evidence sample && event sample)) (same evidence) lawPositive nativePositive)
      (QProb.equiv_symm ((original.model.interventionalDist intervention).conditionOn_probVal evidence event nativePositive)))

/-- Coverage of arbitrary fitted originals uses their actual response laws.
No literal zero-cell retention premise is imposed on those input laws. -/
def lawOfSupportedModel (reference : EvidenceSupport.SupportedModel S observed intervention evidence) :
    (supportedProblem S observed).ConditionalLaw (tableEvent S intervention evidence) := by
  let law : Distro (Table S) := ⟨lawOfNative S reference.model.model⟩
  have admissible := (supportedProblem_law_iff S observed law).mpr
    (lawOfNative_fits S observed reference.model reference.fits)
  exact ⟨law, admissible.1, admissible.2,
    (QProb.equiv_num_pos_iff (lawOfNative_interventionalValue S reference.model.model intervention evidence)).mpr reference.positive⟩

theorem lawOfSupportedModel_value (reference : EvidenceSupport.SupportedModel S observed intervention evidence) :
    QProb.Equiv ((lawOfSupportedModel S observed intervention evidence reference).value (tableEvent S intervention event))
      (ConditionalValue.supportedValue S observed intervention evidence event reference) :=
  value_preserved S intervention evidence event _ reference.model
    (lawOfNative_interventionalValue S reference.model.model intervention) _ _

/-- A returned law constructs an actual fitted original-domain model. Its
positive evidence is transported before any conditional is formed. -/
def modelOfLaw (law : (supportedProblem S observed).ConditionalLaw (tableEvent S intervention evidence)) :
    EvidenceSupport.SupportedModel S observed intervention evidence where
  model := asProjectedModel S law.distro.record
  fits := nativeFits_of_fits S observed law.distro.record
    ((supportedProblem_moments_iff_fits S observed law.distro).mp law.moments)
  positive := (QProb.equiv_num_pos_iff (nativeModel_interventionalValue S law.distro.record intervention evidence)).mpr law.positive

theorem modelOfLaw_value (law : (supportedProblem S observed).ConditionalLaw (tableEvent S intervention evidence)) :
    QProb.Equiv (ConditionalValue.supportedValue S observed intervention evidence event
      (modelOfLaw S observed intervention evidence law)) (law.value (tableEvent S intervention event)) :=
  QProb.equiv_symm (value_preserved S intervention evidence event law.distro.record (asProjectedModel S law.distro.record)
    (fun test => QProb.equiv_symm (nativeModel_interventionalValue S law.distro.record intervention test)) _ _)

/-- Universal bounds over every supported fitted original, actual endpoint
models, and constructive attainment of every rational intermediate value. -/
structure SharpRange where
  lower : EvidenceSupport.SupportedModel S observed intervention evidence
  upper : EvidenceSupport.SupportedModel S observed intervention evidence
  bounds : ∀ original : EvidenceSupport.SupportedModel S observed intervention evidence,
    QProb.LE (ConditionalValue.supportedValue S observed intervention evidence event lower)
      (ConditionalValue.supportedValue S observed intervention evidence event original) ∧
    QProb.LE (ConditionalValue.supportedValue S observed intervention evidence event original)
      (ConditionalValue.supportedValue S observed intervention evidence event upper)
  pointBetween : ∀ value : QProb,
    QProb.LE (ConditionalValue.supportedValue S observed intervention evidence event lower) value →
    QProb.LE value (ConditionalValue.supportedValue S observed intervention evidence event upper) →
    {original : EvidenceSupport.SupportedModel S observed intervention evidence //
      QProb.Equiv (ConditionalValue.supportedValue S observed intervention evidence event original) value}

/-- Compute the conditional interval from one actual positive reference.
The reference supplies nonemptiness; it does not supply an endpoint, coverage
certificate, denominator bound or optimization oracle. -/
def ofReference (reference : EvidenceSupport.SupportedModel S observed intervention evidence) :
    SharpRange S observed intervention evidence event := by
  let sharp := (supportedProblem S observed).conditionalRange (tableEvent S intervention evidence)
    (tableEvent S intervention event) (lawOfSupportedModel S observed intervention evidence reference)
  let lower := modelOfLaw S observed intervention evidence sharp.lower
  let upper := modelOfLaw S observed intervention evidence sharp.upper
  have lowerValue := modelOfLaw_value S observed intervention evidence event sharp.lower
  have upperValue := modelOfLaw_value S observed intervention evidence event sharp.upper
  refine ⟨lower, upper, ?_, ?_⟩
  · intro original
    have bounded := sharp.bounds (lawOfSupportedModel S observed intervention evidence original)
    have actual := lawOfSupportedModel_value S observed intervention evidence event original
    exact ⟨QProb.le_congr (QProb.equiv_symm lowerValue) actual bounded.1,
      QProb.le_congr actual (QProb.equiv_symm upperValue) bounded.2⟩
  · intro value lowerBound upperBound
    let attained := sharp.pointBetween value
      (QProb.le_congr lowerValue (QProb.equiv_refl _) lowerBound)
      (QProb.le_congr (QProb.equiv_refl _) upperValue upperBound)
    exact ⟨modelOfLaw S observed intervention evidence attained.val,
      QProb.equiv_trans (modelOfLaw_value S observed intervention evidence event attained.val) attained.property⟩

variable {S observed intervention evidence event}

theorem SharpRange.attainable_iff_bounds (sharp : SharpRange S observed intervention evidence event) (value : QProb) :
    (∃ original : EvidenceSupport.SupportedModel S observed intervention evidence,
      QProb.Equiv (ConditionalValue.supportedValue S observed intervention evidence event original) value) ↔
      QProb.LE (ConditionalValue.supportedValue S observed intervention evidence event sharp.lower) value ∧
      QProb.LE value (ConditionalValue.supportedValue S observed intervention evidence event sharp.upper) := by
  constructor
  · rintro ⟨original, same⟩
    have bounded := sharp.bounds original
    exact ⟨QProb.le_congr (QProb.equiv_refl _) same bounded.1, QProb.le_congr same (QProb.equiv_refl _) bounded.2⟩
  · rintro ⟨lower, upper⟩
    let attained := sharp.pointBetween value lower upper
    exact ⟨attained.val, attained.property⟩

/-- Agreement among all supported models is exactly endpoint coincidence.
The range already supplies supported model existence, avoiding vacuity. -/
theorem SharpRange.identified_iff (sharp : SharpRange S observed intervention evidence event) :
    ConditionalValue.PointIdentified S observed intervention evidence event ↔
      QProb.Equiv (ConditionalValue.supportedValue S observed intervention evidence event sharp.lower)
        (ConditionalValue.supportedValue S observed intervention evidence event sharp.upper) := by
  constructor
  · intro identified
    exact identified.2 sharp.lower.model sharp.upper.model sharp.lower.fits sharp.upper.fits sharp.lower.positive sharp.upper.positive
  · intro same
    refine ⟨⟨sharp.lower.model, sharp.lower.fits, sharp.lower.positive⟩, ?_⟩
    intro left right leftFits rightFits leftPositive rightPositive
    have collapse (original : EvidenceSupport.SupportedModel S observed intervention evidence) :
        QProb.Equiv (ConditionalValue.supportedValue S observed intervention evidence event original)
          (ConditionalValue.supportedValue S observed intervention evidence event sharp.lower) :=
      (QProb.toSignedRatio_equiv_iff _ _).mp (SignedRatio.equiv_of_le_of_le
        ((SignedRatio.toSignedRatio_le_iff _ _).mpr
          (QProb.le_congr (QProb.equiv_refl _) (QProb.equiv_symm same) (sharp.bounds original).2))
        ((SignedRatio.toSignedRatio_le_iff _ _).mpr (sharp.bounds original).1))
    exact QProb.equiv_trans (collapse ⟨left, leftFits, leftPositive⟩)
      (QProb.equiv_symm (collapse ⟨right, rightFits, rightPositive⟩))

end Thesis.Causality.SharedResponse.ConditionalRange
