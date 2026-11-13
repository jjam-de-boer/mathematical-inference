import Thesis.CausalTransport.SharedResponseConditionalRangeSolver
import Thesis.Examples.SharedResponseConditionalValues
import Thesis.Probability.FiniteProbabilityValueEscape

namespace Thesis.Causality.Examples.SharedResponseConditionalRanges

open Probability Probability.Distros Causality.SharedResponse

/-!
# Native conditional intervals, mixed support and null evidence

The bow's null factual action permits every rational outcome probability
after forcing that action. Here this is recovered from the computed native
conditional-range constructor: explicit fitted endpoints establish its whole
interval, and its lifting method returns an actual original model for every
intermediate rational value. No closed optimizer query is normalized.

A second query has proper causal evidence and mixed support across fitted
models. Its supported conditional interval collapses to one, while the null
models remain represented by the independent evidence report. The unary
three-valued fixture checks that null evidence yields no conditional range.
-/

namespace Bow

open BinaryBow
open SharedResponseLinearBounds.Bow (observed)
open SharedResponseSupportedBounds.Bow (endpointCompatible)

def endpointLaw (upper : Bool) : (supportedProblem signature observed).ConditionalLaw
    (ConditionalRange.tableEvent signature (intervention true) topEvent) where
  distro := (endpointCompatible upper).distro
  support := (endpointCompatible upper).support
  moments := (endpointCompatible upper).moments
  positive := by cases upper <;> decide +kernel

def endpoint (upper : Bool) : EvidenceSupport.SupportedModel signature observed (intervention true) topEvent :=
  ConditionalRange.modelOfLaw signature observed (intervention true) topEvent (endpointLaw upper)

theorem endpoint_value (upper : Bool) :
    QProb.Equiv (ConditionalValue.supportedValue signature observed (intervention true) topEvent
      (fun sample => sample y) (endpoint upper)) (if upper then QProb.one else QProb.zero) :=
  QProb.equiv_trans (ConditionalRange.modelOfLaw_value signature observed (intervention true) topEvent
    (fun sample => sample y) (endpointLaw upper)) (by cases upper <;> decide +kernel)

def computed : ConditionalRange.SharpRange signature observed (intervention true) topEvent (fun sample => sample y) :=
  ConditionalRange.ofReference signature observed (intervention true) topEvent (fun sample => sample y) (endpoint false)

theorem full_interval (sharp : ConditionalRange.SharpRange signature observed (intervention true) topEvent (fun sample => sample y)) :
    QProb.Equiv (ConditionalValue.supportedValue signature observed (intervention true) topEvent (fun sample => sample y) sharp.lower) QProb.zero ∧
    QProb.Equiv (ConditionalValue.supportedValue signature observed (intervention true) topEvent (fun sample => sample y) sharp.upper) QProb.one := by
  have lower := QProb.le_congr (QProb.equiv_refl _) (endpoint_value false) (sharp.bounds (endpoint false)).1
  have upper := QProb.le_congr (endpoint_value true) (QProb.equiv_refl _) (sharp.bounds (endpoint true)).2
  have upperUnit := ((sharp.upper.model.model.interventionalDist (intervention true)).conditionOn
    topEvent sharp.upper.positive).probVal_le_one (fun sample => sample y)
  exact ⟨(QProb.toSignedRatio_equiv_iff _ _).mp (SignedRatio.equiv_of_le_of_le
    ((SignedRatio.toSignedRatio_le_iff _ _).mpr lower) ((SignedRatio.toSignedRatio_le_iff _ _).mpr (QProb.zero_le _))),
    (QProb.toSignedRatio_equiv_iff _ _).mp (SignedRatio.equiv_of_le_of_le
      ((SignedRatio.toSignedRatio_le_iff _ _).mpr upperUnit)
      ((SignedRatio.toSignedRatio_le_iff _ _).mpr upper))⟩

/-- This is original-model data for every rational value, not only a proof
of membership in a numerical relaxation or a fixed denominator catalogue. -/
def realizingNative (value : QProb) (bounded : QProb.LE value QProb.one) :
    {original : EvidenceSupport.SupportedModel signature observed (intervention true) topEvent //
      QProb.Equiv (ConditionalValue.supportedValue signature observed (intervention true) topEvent (fun sample => sample y) original) value} :=
  computed.pointBetween value
    (QProb.le_congr (QProb.equiv_symm (full_interval computed).1) (QProb.equiv_refl _) (QProb.zero_le _))
    (QProb.le_congr (QProb.equiv_refl _) (QProb.equiv_symm (full_interval computed).2) bounded)

/-- No finite list of fully weighted fitted models captures all attainable
values, even at this single fixed observed law. This does not rule out finite
parameterized templates, endpoint methods, or a decision procedure that needs
only feasibility and disagreement witnesses rather than every target value. -/
def outsideFiniteModelCatalogue
    (catalogue : List (EvidenceSupport.SupportedModel signature observed (intervention true) topEvent)) :
    {original : EvidenceSupport.SupportedModel signature observed (intervention true) topEvent //
      ∀ listed ∈ catalogue, ¬ QProb.Equiv
        (ConditionalValue.supportedValue signature observed (intervention true) topEvent (fun sample => sample y) original)
        (ConditionalValue.supportedValue signature observed (intervention true) topEvent (fun sample => sample y) listed)} := by
  let response := ConditionalValue.supportedValue signature observed (intervention true) topEvent (fun sample => sample y)
  let escaped := QProb.outsideFiniteCatalogue (catalogue.map response)
  let realized := realizingNative escaped.val escaped.property.1
  refine ⟨realized.val, ?_⟩
  intro listed member same
  exact escaped.property.2 (response listed) (List.mem_map.mpr ⟨listed, member, rfl⟩)
    (QProb.equiv_trans (QProb.equiv_symm realized.property) same)

def mixedRange := ConditionalRange.ofReference signature observed (intervention true) (fun sample => sample y)
  topEvent SharedResponseConditionalValues.Bow.mixedReference

theorem mixed_support_and_singleton_range :
    SharedResponseEvidenceSupport.Bow.report.kind = .mixed ∧
      QProb.Equiv (ConditionalValue.supportedValue signature observed (intervention true) (fun sample => sample y) topEvent mixedRange.lower)
        (ConditionalValue.supportedValue signature observed (intervention true) (fun sample => sample y) topEvent mixedRange.upper) :=
  ⟨SharedResponseEvidenceSupport.Bow.mixed_report_case,
    mixedRange.identified_iff.mp SharedResponseConditionalValues.Bow.mixed_support_and_identified_values.2⟩

end Bow

namespace Unary

open SharedResponseLinearBounds.Unary

def nullReport := ConditionalRange.reportOfSupport signature observed (HardIntervention.empty signature) two one
  SharedResponseEvidenceSupport.Unary.nullReport

theorem no_conditional_range : nullReport.kind ≠ .bounded := by
  intro bounded
  obtain ⟨original, fitted, positive⟩ := nullReport.bounded_iff.mp bounded
  exact SharedResponseConditionalValues.Unary.no_supported_native_model original fitted positive

end Unary

end Thesis.Causality.Examples.SharedResponseConditionalRanges
