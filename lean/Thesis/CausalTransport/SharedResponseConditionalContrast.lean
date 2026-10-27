import Thesis.Probability.FiniteConditionalContrastPreservation
import Thesis.CausalTransport.SharedResponseSupportedProblem

namespace Thesis.Causality.SharedResponse.ConditionalValue

open Probability Probability.Distros

/-!
# The conditional contrast on response laws and original native models

Pull the integer response back along the actual hard-intervention execution.
Native coverage preserves the evidence and joint-event probabilities, so it
preserves contrast vanishing even at null evidence. The original model's
supported conditional is compared only after its support has been proved.

Only vanishing is needed for conditional-value classification. In particular,
no fractional optimization, positive support cutoff or equality of raw atom
presentations is required. The constructive linear optimizer continues to
consume ordinary integer responses against nonnegative rational laws.
-/

variable (S : ObservedSignature.{0})

def contrastResponse (intervention : HardIntervention S) (evidence event : Event S.Assignment)
    (value : QProb) (table : Table S) : Int :=
  FiniteProbRecord.conditionalContrast evidence event value (eval S intervention.value table)

def lawContrastMean (intervention : HardIntervention S) (evidence event : Event S.Assignment)
    (value : QProb) (law : FiniteProbRecord (Table S)) : SignedRatio :=
  (⟨law⟩ : Distro (Table S)).rationalExpectation (integerResponse (contrastResponse S intervention evidence event value))

def contrastMean (intervention : HardIntervention S) (evidence event : Event S.Assignment)
    (value : QProb) (original : ProjectedHiddenDAGModel (graph S)) : SignedRatio :=
  (original.model.interventionalDist intervention).rationalMean
    (integerResponse (FiniteProbRecord.conditionalContrast evidence event value))

/-- Conditional values are proof-carrying: there is no value at null evidence. -/
def value (intervention : HardIntervention S) (evidence event : Event S.Assignment)
    (original : ProjectedHiddenDAGModel (graph S))
    (positive : (original.model.interventionalDist intervention).EventPositive evidence) : QProb :=
  ((original.model.interventionalDist intervention).conditionOn evidence positive).probVal event

theorem contrastMean_zero_iff (intervention : HardIntervention S) (evidence event : Event S.Assignment)
    (proposed : QProb) (original : ProjectedHiddenDAGModel (graph S))
    (positive : (original.model.interventionalDist intervention).EventPositive evidence) :
    SignedRatio.Equiv (contrastMean S intervention evidence event proposed original) SignedRatio.zero ↔
      QProb.Equiv (value S intervention evidence event original positive) proposed :=
  (original.model.interventionalDist intervention).rationalMean_conditionalContrast_zero_iff
    evidence event proposed positive

/-- A nonzero native contrast supplies the support needed by a later
disagreement witness. Null-evidence models cannot be false counterexamples. -/
theorem positive_of_contrastMean_nonzero (intervention : HardIntervention S) (evidence event : Event S.Assignment)
    (proposed : QProb) (original : ProjectedHiddenDAGModel (graph S))
    (nonzero : ¬ SignedRatio.Equiv (contrastMean S intervention evidence event proposed original) SignedRatio.zero) :
    (original.model.interventionalDist intervention).EventPositive evidence :=
  (original.model.interventionalDist intervention).eventPositive_of_conditionalContrast_mean_ne_zero
    evidence event proposed nonzero

private theorem mean_zero_iff_of_events (intervention : HardIntervention S)
    (evidence event : Event S.Assignment) (proposed : QProb) (law : FiniteProbRecord (Table S))
    (original : ProjectedHiddenDAGModel (graph S))
    (same : ∀ test, QProb.Equiv (law.probVal (fun table => test (eval S intervention.value table)))
      (original.model.interventionalValue intervention test)) :
    SignedRatio.Equiv (lawContrastMean S intervention evidence event proposed law) SignedRatio.zero ↔
      SignedRatio.Equiv (contrastMean S intervention evidence event proposed original) SignedRatio.zero := by
  have preserved := FiniteProbRecord.conditionalContrast_mean_zero_iff_of_probVal
    (law.map (eval S intervention.value)) (original.model.interventionalDist intervention)
    evidence event evidence event proposed
    (QProb.equiv_trans (law.map_probVal _ evidence) (same evidence))
    (QProb.equiv_trans (law.map_probVal _ (fun sample => evidence sample && event sample))
      (same (fun sample => evidence sample && event sample)))
  rw [FiniteProbRecord.rationalMean_map] at preserved
  exact preserved

/-- Every compatible response law has a native realization with the same
contrast-zero predicate, including laws with null intervention evidence. -/
theorem asProjectedModel_contrast_zero_iff (intervention : HardIntervention S)
    (evidence event : Event S.Assignment) (proposed : QProb) (law : FiniteProbRecord (Table S)) :
    SignedRatio.Equiv (lawContrastMean S intervention evidence event proposed law) SignedRatio.zero ↔
      SignedRatio.Equiv (contrastMean S intervention evidence event proposed (asProjectedModel S law)) SignedRatio.zero :=
  mean_zero_iff_of_events S intervention evidence event proposed law (asProjectedModel S law)
    (fun test => QProb.equiv_symm (nativeModel_interventionalValue S law intervention test))

/-- The reverse coverage direction applies to every fitted original model,
with its actual finite hidden sources and rational weights. -/
theorem lawOfNative_contrast_zero_iff (intervention : HardIntervention S)
    (evidence event : Event S.Assignment) (proposed : QProb)
    (original : ProjectedHiddenDAGModel (graph S)) :
    SignedRatio.Equiv (lawContrastMean S intervention evidence event proposed (lawOfNative S original.model)) SignedRatio.zero ↔
      SignedRatio.Equiv (contrastMean S intervention evidence event proposed original) SignedRatio.zero :=
  mean_zero_iff_of_events S intervention evidence event proposed (lawOfNative S original.model) original
    (lawOfNative_interventionalValue S original.model intervention)

end Thesis.Causality.SharedResponse.ConditionalValue
