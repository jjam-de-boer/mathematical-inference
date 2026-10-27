import Thesis.CausalTransport.SharedResponseConditionalSolver
import Thesis.Examples.SharedResponseEvidenceSupport

namespace Thesis.Causality.Examples.SharedResponseConditionalValues

open Probability Probability.Distros Causality.SharedResponse

/-!
# Supported conditional values and independent evidence reports

The factual three-valued fixture has a declared null evidence value. Its
value report excludes all supported models while retaining native compatibility.
The binary bow fixture exercises two different supported-value answers:

* Its causal evidence is mixed across fitted models, yet conditioning the
  top event gives the same attained value one wherever evidence is positive.
* Top evidence is always supported, but the outcome after a null factual
  action has genuinely different supported conditional values.
* Complementing that outcome gives a reference value one and a negative
  lower contrast endpoint, exercising the other ambiguity branch.

Bounds in these regressions are supplied and proved analytically. No closed
optimizer query is executed or trusted. In particular, the null endpoint in
the mixed-support example is never used to assign a conditional value.
-/

namespace Unary

open SharedResponseLinearBounds.Unary

def nullValues := ConditionalValue.reportOfSupport signature observed (HardIntervention.empty signature) two one
  SharedResponseEvidenceSupport.Unary.nullReport

theorem unsupported_value_case : nullValues.kind = .unsupported :=
  (nullValues.unsupported_iff_support SharedResponseEvidenceSupport.Unary.nullReport).mpr
    SharedResponseEvidenceSupport.Unary.null_report_case

theorem no_supported_native_model :
    ∀ original, NativeFits signature observed original →
      ¬ (original.model.interventionalDist (HardIntervention.empty signature)).EventPositive two :=
  nullValues.unsupported_iff.mp unsupported_value_case

end Unary

namespace Bow

open BinaryBow
open SharedResponseLinearBounds.Bow (observed)
open SharedResponseSupportedBounds.Bow (nativeCertificate endpointCompatible endpoint_effect effectEvent)

def mixedReference : EvidenceSupport.SupportedModel signature observed (intervention true) (fun values => values y) where
  model := nativeCertificate.upperModel
  fits := nativeCertificate.upper_fits
  positive := (QProb.equiv_num_pos_iff
    ((QProb.toSignedRatio_equiv_iff _ QProb.one).mp nativeCertificate.upper_attained)).mpr Nat.zero_lt_one

def commonProposed := ConditionalValue.supportedValue signature observed (intervention true)
  (fun values => values y) topEvent mixedReference

private theorem common_proposed_one : QProb.Equiv commonProposed QProb.one :=
  (mixedReference.model.model.interventionalDist (intervention true)).conditionOn_normalization
    (fun values => values y) mixedReference.positive

private theorem common_response_zero (table : Table signature) :
    ConditionalValue.contrastResponse signature (intervention true) (fun values => values y) topEvent commonProposed table = 0 := by
  have numerator : commonProposed.num = commonProposed.den := by
    simpa only [QProb.Equiv, QProb.one, Nat.mul_one, Nat.one_mul] using common_proposed_one
  unfold ConditionalValue.contrastResponse FiniteProbRecord.conditionalContrast
  rw [numerator]
  cases selected : (eval signature (intervention true).value table) y <;>
    simp only [selected, topEvent, Bool.and_true, Bool.false_eq_true, if_true, if_false,
      Int.mul_zero, Int.mul_one, Int.sub_self]

private theorem common_mean_zero (law : Distro (Table signature)) :
    SignedRatio.Equiv (ConditionalValue.lawContrastMean signature (intervention true)
      (fun values => values y) topEvent commonProposed law.record) SignedRatio.zero := by
  refine SignedRatio.equiv_trans (law.rationalExpectation_congr _ (fun _ => SignedRatio.zero) ?_)
    (law.rationalExpectation_constant SignedRatio.zero)
  intro table
  change SignedRatio.Equiv ⟨_, 1, Nat.zero_lt_one⟩ SignedRatio.zero
  rw [common_response_zero]
  exact SignedRatio.equiv_refl _

/-- The null and positive response laws both attain zero contrast. Their
evidence behavior differs, but the supported target value is the same. -/
def commonCertificate : (supportedProblem signature observed).SharpBounds
    (ConditionalValue.contrastResponse signature (intervention true) (fun values => values y) topEvent commonProposed) where
  lower := SignedRatio.zero
  upper := SignedRatio.zero
  lowerLaw := endpointCompatible false
  upperLaw := endpointCompatible true
  lower_attained := common_mean_zero _
  upper_attained := common_mean_zero _
  bounds := by
    intro law _support _moments
    have zero := common_mean_zero law
    exact ⟨(SignedRatio.le_congr (SignedRatio.equiv_refl _) zero).mpr (SignedRatio.le_refl _),
      (SignedRatio.le_congr zero (SignedRatio.equiv_refl _)).mpr (SignedRatio.le_refl _)⟩

def commonReport := ConditionalValue.ofBounds mixedReference commonCertificate

theorem common_report_identified : commonReport.kind = .identified := by
  simp only [commonReport, ConditionalValue.ofBounds, commonCertificate,
    dif_pos (SignedRatio.equiv_refl SignedRatio.zero), ConditionalValue.Report.kind]

theorem mixed_support_and_identified_values :
    SharedResponseEvidenceSupport.Bow.report.kind = .mixed ∧
      ConditionalValue.PointIdentified signature observed (intervention true) (fun values => values y) topEvent :=
  ⟨SharedResponseEvidenceSupport.Bow.mixed_report_case, commonReport.identified_iff.mp common_report_identified⟩

def ambiguityReference : EvidenceSupport.SupportedModel signature observed (intervention true) topEvent where
  model := nativeCertificate.lowerModel
  fits := nativeCertificate.lower_fits
  positive := (QProb.equiv_num_pos_iff
    (nativeCertificate.lowerModel.model.interventionalDist (intervention true)).normalization).mpr Nat.zero_lt_one

def ambiguityProposed := ConditionalValue.supportedValue signature observed (intervention true)
  topEvent (fun values => values y) ambiguityReference

private theorem ambiguity_proposed_zero : QProb.Equiv ambiguityProposed QProb.zero := by
  have conditional := (ambiguityReference.model.model.interventionalDist (intervention true)).conditionOn_probVal
    topEvent (fun values => values y) ambiguityReference.positive
  have denominatorOne := (ambiguityReference.model.model.interventionalDist (intervention true)).normalization
  have numerator := (QProb.toSignedRatio_equiv_iff _ QProb.zero).mp nativeCertificate.lower_attained
  have jointSame : QProb.Equiv
      ((ambiguityReference.model.model.interventionalDist (intervention true)).probVal
        (fun sample => topEvent sample && sample y))
      (ambiguityReference.model.model.interventionalValue (intervention true) (fun values => values y)) := by
    simpa only [topEvent, Bool.true_and] using QProb.equiv_refl
      (ambiguityReference.model.model.interventionalValue (intervention true) (fun values => values y))
  exact QProb.equiv_trans conditional
    (QProb.equiv_trans (QProb.div_equiv_of_den_equiv_one _
      ((ambiguityReference.model.model.interventionalDist (intervention true)).probVal topEvent)
      ambiguityReference.positive denominatorOne)
      (QProb.equiv_trans jointSame numerator))

private theorem ambiguity_mean_scaled (law : Distro (Table signature)) :
    SignedRatio.Equiv (ConditionalValue.lawContrastMean signature (intervention true)
      topEvent (fun values => values y) ambiguityProposed law.record)
      (SignedRatio.scaleInt (ambiguityProposed.den : Int) (law.record.probVal effectEvent).toSignedRatio) := by
  have numeratorZero := (QProb.equiv_num_zero_iff ambiguity_proposed_zero).mpr rfl
  refine SignedRatio.equiv_trans (law.rationalExpectation_congr _
    (fun table => SignedRatio.scaleInt (ambiguityProposed.den : Int) (integerResponse (eventResponse effectEvent) table)) ?_)
    (SignedRatio.equiv_trans (law.rationalExpectation_mul_left _ _)
      (SignedRatio.scaleInt_congr _ (eventResponse_expectation law effectEvent)))
  intro table
  cases selected : (eval signature (intervention true).value table) y <;>
    simp only [integerResponse, ConditionalValue.contrastResponse, FiniteProbRecord.conditionalContrast,
      topEvent, Bool.true_and, numeratorZero, Int.natCast_zero, Int.sub_zero,
      eventResponse, effectEvent, selected, Bool.false_eq_true, if_true, if_false,
      SignedRatio.scaleInt, SignedRatio.mul, SignedRatio.Equiv, Nat.one_mul, Int.natCast_one,
      Int.mul_one, Int.mul_zero]

/-- Scale the elementary event bounds by the reference denominator. The
two old endpoint laws still attain the exact contrast endpoints. -/
def ambiguityCertificate : (supportedProblem signature observed).SharpBounds
    (ConditionalValue.contrastResponse signature (intervention true) topEvent (fun values => values y) ambiguityProposed) where
  lower := SignedRatio.zero
  upper := SignedRatio.scaleInt (ambiguityProposed.den : Int) SignedRatio.one
  lowerLaw := endpointCompatible false
  upperLaw := endpointCompatible true
  lower_attained := SignedRatio.equiv_trans (ambiguity_mean_scaled _)
    (SignedRatio.equiv_trans (SignedRatio.scaleInt_congr _ (QProb.toSignedRatio_congr (endpoint_effect false)))
      (SignedRatio.scaleInt_zero _))
  upper_attained := SignedRatio.equiv_trans (ambiguity_mean_scaled _)
    (SignedRatio.scaleInt_congr _ (QProb.toSignedRatio_congr (endpoint_effect true)))
  bounds := by
    intro law _support _moments
    have positive : 0 < (ambiguityProposed.den : Int) := by have h := ambiguityProposed.den_pos; omega
    have lower := (SignedRatio.scaleInt_le_iff _ positive SignedRatio.zero (law.record.probVal effectEvent).toSignedRatio).mpr
      ((SignedRatio.toSignedRatio_le_iff QProb.zero _).mpr (law.record.probVal_nonneg effectEvent))
    have upper := (SignedRatio.scaleInt_le_iff _ positive (law.record.probVal effectEvent).toSignedRatio SignedRatio.one).mpr
      ((SignedRatio.toSignedRatio_le_iff _ QProb.one).mpr (law.record.probVal_le_one effectEvent))
    exact ⟨(SignedRatio.le_congr (SignedRatio.scaleInt_zero _) (SignedRatio.equiv_symm (ambiguity_mean_scaled law))).mp lower,
      (SignedRatio.le_congr (SignedRatio.equiv_symm (ambiguity_mean_scaled law)) (SignedRatio.equiv_refl _)).mp upper⟩

def ambiguousReport := ConditionalValue.ofBounds ambiguityReference ambiguityCertificate

theorem ambiguous_report_case : ambiguousReport.kind = .ambiguous := by
  have lowerZero : SignedRatio.Equiv ambiguityCertificate.lower SignedRatio.zero := SignedRatio.equiv_refl _
  have upperNonzero : ¬ SignedRatio.Equiv ambiguityCertificate.upper SignedRatio.zero := by
    intro zero
    have numerator := (SignedRatio.equiv_zero_iff _).mp zero
    change (ambiguityProposed.den : Int) * 1 = 0 at numerator
    have positive := ambiguityProposed.den_pos
    omega
  simp only [ambiguousReport, ConditionalValue.ofBounds, dif_pos lowerZero, dif_neg upperNonzero,
    ConditionalValue.Report.kind]

theorem not_conditionally_identified :
    ¬ ConditionalValue.PointIdentified signature observed (intervention true) topEvent (fun values => values y) := by
  intro identified
  have kind := ambiguousReport.identified_iff.mpr identified
  rw [ambiguous_report_case] at kind
  cases kind

/-- Use the same null-action query with the complementary target. The old
reference has outcome probability zero, so this supported target has value
one. Its contrast is the negative of the preceding example's contrast. -/
def negativeEvent : Event signature.Assignment := complement (fun values => values y)

def negativeProposed := ConditionalValue.supportedValue signature observed (intervention true)
  topEvent negativeEvent ambiguityReference

private theorem negative_proposed_parts : negativeProposed.num = negativeProposed.den := by
  let conditioned := (ambiguityReference.model.model.interventionalDist (intervention true)).conditionOn
    topEvent ambiguityReference.positive
  have originalZero := (QProb.equiv_num_zero_iff ambiguity_proposed_zero).mpr rfl
  change FiniteProbRecord.eventMass conditioned.atoms (fun values => values y) = 0 at originalZero
  have partition := FiniteProbRecord.eventMass_add_complement conditioned.atoms (fun values => values y)
  have total := conditioned.total_mass
  change FiniteProbRecord.eventMass conditioned.atoms (complement (fun values => values y)) = conditioned.den
  rw [originalZero, Nat.zero_add, total] at partition
  exact partition

private theorem negative_response_eq_neg (table : Table signature) :
    ConditionalValue.contrastResponse signature (intervention true) topEvent negativeEvent negativeProposed table =
      -(ConditionalValue.contrastResponse signature (intervention true) topEvent (fun values => values y) ambiguityProposed table) := by
  have numeratorZero := (QProb.equiv_num_zero_iff ambiguity_proposed_zero).mpr rfl
  have sameDenominator : negativeProposed.den = ambiguityProposed.den := rfl
  unfold ConditionalValue.contrastResponse FiniteProbRecord.conditionalContrast
  rw [negative_proposed_parts, sameDenominator, numeratorZero]
  cases selected : (eval signature (intervention true).value table) y <;>
    simp only [topEvent, negativeEvent, complement, selected, Bool.true_and, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, if_true, if_false, Int.natCast_zero, Int.mul_zero, Int.mul_one,
      Int.sub_zero, Int.sub_self, Int.zero_sub, Int.neg_zero]

private theorem negative_mean (law : Distro (Table signature)) :
    SignedRatio.Equiv (ConditionalValue.lawContrastMean signature (intervention true)
      topEvent negativeEvent negativeProposed law.record)
      (SignedRatio.neg (ConditionalValue.lawContrastMean signature (intervention true)
        topEvent (fun values => values y) ambiguityProposed law.record)) := by
  refine SignedRatio.equiv_trans (law.rationalExpectation_congr _
    (fun table => SignedRatio.neg (integerResponse
      (ConditionalValue.contrastResponse signature (intervention true) topEvent (fun values => values y) ambiguityProposed) table)) ?_)
    (law.rationalExpectation_neg _)
  intro table
  change SignedRatio.Equiv ⟨_, 1, Nat.zero_lt_one⟩ (SignedRatio.neg ⟨_, 1, Nat.zero_lt_one⟩)
  rw [negative_response_eq_neg]
  exact SignedRatio.equiv_refl _

/-- Negation reverses the attained endpoints and swaps their actual fitted
laws. The negative endpoint is not a signed probability: only the auxiliary
contrast is signed, and every witness remains an ordinary probability model. -/
def negativeCertificate : (supportedProblem signature observed).SharpBounds
    (ConditionalValue.contrastResponse signature (intervention true) topEvent negativeEvent negativeProposed) where
  lower := SignedRatio.neg ambiguityCertificate.upper
  upper := SignedRatio.neg ambiguityCertificate.lower
  lowerLaw := ambiguityCertificate.upperLaw
  upperLaw := ambiguityCertificate.lowerLaw
  lower_attained := SignedRatio.equiv_trans (negative_mean _) (SignedRatio.neg_congr ambiguityCertificate.upper_attained)
  upper_attained := SignedRatio.equiv_trans (negative_mean _) (SignedRatio.neg_congr ambiguityCertificate.lower_attained)
  bounds := by
    intro law support moments
    have bounded := ambiguityCertificate.bounds law support moments
    have lower := (SignedRatio.neg_le_neg_iff _ _).mpr bounded.2
    have upper := (SignedRatio.neg_le_neg_iff _ _).mpr bounded.1
    exact ⟨(SignedRatio.le_congr (SignedRatio.equiv_refl _) (SignedRatio.equiv_symm (negative_mean law))).mp lower,
      (SignedRatio.le_congr (SignedRatio.equiv_symm (negative_mean law)) (SignedRatio.equiv_refl _)).mp upper⟩

def negativeReport := ConditionalValue.ofBounds ambiguityReference negativeCertificate

theorem negative_lower_endpoint_negative : negativeCertificate.lower.num < 0 := by
  change -((ambiguityProposed.den : Int) * 1) < 0
  have positive := ambiguityProposed.den_pos
  omega

/-- This forces the nonzero-lower-endpoint branch. The existing regression
instead had zero lower contrast and a nonzero upper endpoint. -/
theorem negative_report_case : negativeReport.kind = .ambiguous := by
  have lowerNonzero : ¬ SignedRatio.Equiv negativeCertificate.lower SignedRatio.zero :=
    fun zero => (Int.ne_of_lt negative_lower_endpoint_negative) ((SignedRatio.equiv_zero_iff _).mp zero)
  simp only [negativeReport, ConditionalValue.ofBounds, dif_neg lowerNonzero, ConditionalValue.Report.kind]

theorem complementary_target_not_identified :
    ¬ ConditionalValue.PointIdentified signature observed (intervention true) topEvent negativeEvent := by
  intro identified
  have kind := negativeReport.identified_iff.mpr identified
  rw [negative_report_case] at kind
  cases kind

end Bow

/-- The public decision is explicit and handles the entire result, including
incompatibility and null evidence. No concrete optimizer is normalized here. -/
example (S : ObservedSignature.{0}) (observed : FiniteProbRecord S.Assignment)
    (intervention : HardIntervention S) (evidence event : Event S.Assignment) :
    Decidable (ConditionalValue.PointIdentified S observed intervention evidence event) :=
  (ConditionalValue.solve S observed intervention evidence event).identificationDecision

end Thesis.Causality.Examples.SharedResponseConditionalValues
