import Thesis.CausalTransport.SharedResponseEvidenceSupport
import Thesis.Examples.SharedResponseSupportedBounds

namespace Thesis.Causality.Examples.SharedResponseEvidenceSupport

open Probability Causality.SharedResponse

/-!
# Native evidence reports with positive, null and mixed support

The three-valued factual fixture keeps its duplicate outcomes, zero weights
and unreduced denominator. Its observed positive event is supported in every
fitted model, while its declared null value has null factual evidence in
every fitted model. Factual equality supplies the exact bound certificates.

The bow fixture instead forces an observationally null action. Its two
already-proved endpoint models give null and positive causal evidence while
fitting the same observed law. This exercises the mixed branch and confirms
that finding one null model does not discard the positive witness.

These regressions route supplied mathematical certificates; they do not
execute a closed optimizer query or assign a conditional value at null
evidence. The final symbolic application checks the actual solver interface.
-/

namespace Unary

open SharedResponseLinearBounds.Unary

/-- On a factual event, observational fitting fixes the whole interval. The
chosen original model attains both endpoints without changing its record. -/
def factualCertificate (evidence : Event signature.Assignment) :
    SharpBounds signature observed (HardIntervention.empty signature) evidence where
  lower := (observed.probVal evidence).toSignedRatio
  upper := (observed.probVal evidence).toSignedRatio
  lowerModel := original
  upperModel := original
  lower_fits := original_fits
  upper_fits := original_fits
  lower_attained := QProb.toSignedRatio_congr (original_fits evidence)
  upper_attained := QProb.toSignedRatio_congr (original_fits evidence)
  bounds := by
    intro fittedModel fitted
    have same := QProb.toSignedRatio_congr (fitted evidence)
    exact ⟨(SignedRatio.le_congr (SignedRatio.equiv_refl _) same).mpr (SignedRatio.le_refl _),
      (SignedRatio.le_congr same (SignedRatio.equiv_refl _)).mpr (SignedRatio.le_refl _)⟩

def positiveReport := EvidenceSupport.ofBounds (factualCertificate one)
def nullReport := EvidenceSupport.ofBounds (factualCertificate two)

private theorem original_one_positive :
    (original.model.interventionalDist (HardIntervention.empty signature)).EventPositive one :=
  (QProb.equiv_num_pos_iff (original_fits one)).mpr (by decide +kernel)

private theorem original_two_null :
    ¬ (original.model.interventionalDist (HardIntervention.empty signature)).EventPositive two := by
  have zero := (QProb.equiv_num_zero_iff (original_fits two)).mpr observed_two_null
  exact fun positive => (Nat.ne_of_gt positive) zero

theorem positive_report_case :
    positiveReport.kind = .allSupported := by
  simp only [positiveReport, EvidenceSupport.ofBounds, factualCertificate, dif_pos original_one_positive,
    EvidenceSupport.Report.kind]

theorem null_report_case :
    nullReport.kind = .unsupported := by
  simp only [nullReport, EvidenceSupport.ofBounds, factualCertificate, dif_neg original_two_null,
    EvidenceSupport.Report.kind]

/-- The positive answer ranges over every fitted original native model,
not only the concrete fixture used to attain the endpoints. -/
theorem positive_throughout_native_class :
    ∀ fittedModel, NativeFits signature observed fittedModel →
      (fittedModel.model.interventionalDist (HardIntervention.empty signature)).EventPositive one :=
  positiveReport.allSupported_iff.mp positive_report_case

/-- A retained declared value may have zero probability throughout the
factual class. The result proves nullness without forming a conditional. -/
theorem null_throughout_native_class :
    ∀ fittedModel, NativeFits signature observed fittedModel →
      (fittedModel.model.interventionalValue (HardIntervention.empty signature) two).num = 0 :=
  nullReport.unsupported_iff.mp null_report_case

theorem null_report_still_compatible : ∃ fittedModel, NativeFits signature observed fittedModel :=
  nullReport.compatible

end Unary

namespace Bow

open BinaryBow
open SharedResponseLinearBounds.Bow (observed)
open SharedResponseSupportedBounds.Bow (nativeCertificate endpointCompatible endpointLaw endpoint_effect)

def report := EvidenceSupport.ofBounds nativeCertificate

private theorem endpoint_value (offFactual : Bool) :
    QProb.Equiv
      ((supportedFittedModel signature observed (endpointCompatible offFactual)).model.interventionalValue
        (intervention true) (fun values => values y))
      (if offFactual then QProb.one else QProb.zero) :=
  QProb.equiv_trans (nativeModel_interventionalValue signature (endpointLaw offFactual)
    (intervention true) (fun values => values y)) (endpoint_effect offFactual)

/-- The evidence is the outcome event under the forced action; factual
support is not substituted for support in that intervention distribution. -/
theorem mixed_report_case :
    report.kind = .mixed := by
  have upperPositive : (nativeCertificate.upperModel.model.interventionalDist (intervention true)).EventPositive
      (fun values => values y) :=
    (QProb.equiv_num_pos_iff (endpoint_value true)).mpr (by decide +kernel)
  have lowerZero := (QProb.equiv_num_zero_iff (endpoint_value false)).mpr (by decide +kernel)
  have lowerNull : ¬ (nativeCertificate.lowerModel.model.interventionalDist (intervention true)).EventPositive
      (fun values => values y) := fun positive => (Nat.ne_of_gt positive) lowerZero
  simp only [report, EvidenceSupport.ofBounds, dif_pos upperPositive, dif_neg lowerNull, EvidenceSupport.Report.kind]

theorem actual_null_and_positive_models :
    (∃ fittedModel, NativeFits signature observed fittedModel ∧
      (fittedModel.model.interventionalValue (intervention true) (fun values => values y)).num = 0) ∧
    (∃ fittedModel, NativeFits signature observed fittedModel ∧
      (fittedModel.model.interventionalDist (intervention true)).EventPositive (fun values => values y)) :=
  report.mixed_iff.mp mixed_report_case

/-- A mixed-support answer is compatible even though one endpoint cannot
supply the evidence proof required by a future conditional comparison. -/
theorem routed_result_compatible :
    (EvidenceSupport.ofBoundResult (.bounded nativeCertificate)).isCompatible = true :=
  rfl

end Bow

/-- This application uses the actual filtered entry point symbolically.
Its compatibility theorem needs no closed optimizer normalization. -/
example (S : ObservedSignature.{0}) (observed : FiniteProbRecord S.Assignment)
    (intervention : HardIntervention S) (evidence : Event S.Assignment) :
    (EvidenceSupport.solve S observed intervention evidence).isCompatible = true ↔
      ∃ original, NativeFits S observed original :=
  (EvidenceSupport.solve S observed intervention evidence).compatible_iff

end Thesis.Causality.Examples.SharedResponseEvidenceSupport
