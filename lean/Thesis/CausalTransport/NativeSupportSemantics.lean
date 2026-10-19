import Thesis.CausalTransport.HiddenDAGSemantics
import Thesis.Causality.ProbabilityStatusSupport
import Thesis.Probability.FiniteRecordSupport

namespace Thesis.Causality

open Probability

/-!
# Native causal support agreement and all expression-support obligations

Two original native models may have different hidden graphs, source weights
and numerical probabilities while agreeing on positivity of every observed
event under every hard intervention. This relation preserves the exact
undefined/zero/positive status of the entire current nonnegative expression
language. It also transports the complete native derivation-support tree,
including all marginal substitutions and positive-only weighted branches.

Only support is transported. Each target witness is rebuilt using the new
model's actual evaluated value, never an old value that may have changed.
Later template reweighting and finite profile coverage construct this relation
for actual models; it is not an externally assumed causal soundness law.
-/

variable {S : ObservedSignature.{0}} {P Q R : FiniteLatentProjection S}

def CausalSupportAgreement (left : FiniteHiddenDAGSCM S P) (right : FiniteHiddenDAGSCM S Q) : Prop :=
  ∀ intervention event, (left.interventionalDist intervention).EventPositive event ↔
    (right.interventionalDist intervention).EventPositive event

namespace CausalSupportAgreement

variable {left : FiniteHiddenDAGSCM S P} {right : FiniteHiddenDAGSCM S Q} {third : FiniteHiddenDAGSCM S R}

theorem refl (model : FiniteHiddenDAGSCM S P) : CausalSupportAgreement model model := fun _ _ => Iff.rfl
theorem symm (same : CausalSupportAgreement left right) : CausalSupportAgreement right left := fun intervention event => (same intervention event).symm
theorem trans (first : CausalSupportAgreement left right) (second : CausalSupportAgreement right third) :
    CausalSupportAgreement left third := fun intervention event => (first intervention event).trans (second intervention event)

theorem observational_support (same : CausalSupportAgreement left right) :
    left.observationalDist.support = right.observationalDist.support := by
  funext reference
  apply Bool.eq_iff_iff.mpr
  simp only [FiniteProbRecord.support, decide_eq_true_eq]
  exact same (HardIntervention.empty S) (FiniteProbRecord.singletonEvent reference)

theorem kernel_eventPositive_iff (same : CausalSupportAgreement left right) (kernel : Kernel S)
    (reference : S.Assignment) (event : Event S.Assignment) :
    (left.kernelDistribution kernel reference).EventPositive event ↔
      (right.kernelDistribution kernel reference).EventPositive event := by
  cases active : kernel.hasAction with
  | false =>
      simp only [FiniteHiddenDAGSCM.kernelDistribution, active, Bool.false_eq_true, if_false]
      exact same (HardIntervention.empty S) event
  | true =>
      simp only [FiniteHiddenDAGSCM.kernelDistribution, active, if_true]
      exact same { value := kernel.intervention reference } event

theorem kernel_status (same : CausalSupportAgreement left right) (kernel : Kernel S) (reference : S.Assignment) :
    ProbabilityResult.status (left.kernelDenote kernel reference) = ProbabilityResult.status (right.kernelDenote kernel reference) := by
  simp only [FiniteHiddenDAGSCM.kernelDenote, ProbabilityResult.status_divide, ProbabilityResult.status]
  have numerator := ProbabilityResult.valueStatus_eq_of_num_pos_iff _ _
    (same.kernel_eventPositive_iff kernel reference (kernel.numeratorEvent reference))
  have denominator := ProbabilityResult.valueStatus_eq_of_num_pos_iff _ _
    (same.kernel_eventPositive_iff kernel reference (kernel.conditionEvent reference))
  rw [numerator, denominator]

/-- Exact status, not merely a sufficient support test. Strict products and
strict sums retain undefined branches; only weighted multiplication may skip
a factor when its own left weight is a defined zero. -/
theorem term_status (same : CausalSupportAgreement left right) (term : ProbabilityTerm S) : ∀ reference,
    ProbabilityResult.status (left.termDenote term reference) = ProbabilityResult.status (right.termDenote term reference) := by
  intro reference
  induction term generalizing reference with
  | zero => rfl
  | kernel kernel => exact same.kernel_status kernel reference
  | marginalize nodes inner ih =>
      simp only [FiniteHiddenDAGSCM.termDenote, ProbabilityResult.status_sum, List.map_map]
      apply congrArg ProbabilityResult.Status.sum
      apply List.map_congr_left
      intro variant _listed
      exact ih variant
  | evaluateAt fixed inner ih => exact ih fixed
  | add first second firstIH secondIH =>
      simp only [FiniteHiddenDAGSCM.termDenote, ProbabilityResult.status_add, firstIH reference, secondIH reference]
  | multiply first second firstIH secondIH =>
      simp only [FiniteHiddenDAGSCM.termDenote, ProbabilityResult.status_multiply, firstIH reference, secondIH reference]
  | weightedMultiply weight factor weightIH factorIH =>
      simp only [FiniteHiddenDAGSCM.termDenote, ProbabilityResult.status_weightedMultiply, weightIH reference, factorIH reference]
  | divide numerator denominator numeratorIH denominatorIH =>
      simp only [FiniteHiddenDAGSCM.termDenote, ProbabilityResult.status_divide, numeratorIH reference, denominatorIH reference]

def termSupportedToRight (same : CausalSupportAgreement left right) (term : ProbabilityTerm S) (reference : S.Assignment)
    (supported : left.TermSupportedAt term reference) : right.TermSupportedAt term reference :=
  ProbabilityResult.supportedOfIsSome _ (by
    rw [← ProbabilityResult.status_isDefined, ← same.term_status term reference, ProbabilityResult.status_isDefined]
    exact ProbabilityResult.supported_isSome supported)

def positiveSupportedToLeft (same : CausalSupportAgreement left right) (term : ProbabilityTerm S) (reference : S.Assignment)
    (positive : ProbabilityResult.PositiveSupportedValue (right.termDenote term reference)) :
    ProbabilityResult.PositiveSupportedValue (left.termDenote term reference) :=
  ProbabilityResult.positiveSupportedOfStatus _ (by
    rw [same.term_status term reference]
    exact ProbabilityResult.positiveSupported_status positive)

/-- Transport *all* recursively used support, rather than checking only the
printed endpoints. Positive branch evidence is moved backwards before using
the old factor-support function, then the factor's support is rebuilt forwards. -/
def localSupportToRight (same : CausalSupportAgreement left right) {G : ObservedGraph S}
    {first second : ProbabilityTerm S} (derivation : DoCalculusDerivation G first second) (reference : S.Assignment)
    (supported : HiddenDAGLocalDerivationSupport left reference derivation) :
    HiddenDAGLocalDerivationSupport right reference derivation := by
  induction derivation generalizing reference with
  | refl => exact ⟨same.termSupportedToRight _ _ supported.1, same.termSupportedToRight _ _ supported.2.1, ()⟩
  | symm inner ih => exact ⟨same.termSupportedToRight _ _ supported.1, same.termSupportedToRight _ _ supported.2.1, ih supported.2.2⟩
  | trans first second firstIH secondIH =>
      exact ⟨same.termSupportedToRight _ _ supported.1, same.termSupportedToRight _ _ supported.2.1,
        firstIH supported.2.2.1, secondIH supported.2.2.2⟩
  | doRule => exact ⟨same.termSupportedToRight _ _ supported.1, same.termSupportedToRight _ _ supported.2.1, ()⟩
  | marginalization => exact ⟨same.termSupportedToRight _ _ supported.1, same.termSupportedToRight _ _ supported.2.1, ()⟩
  | conditioning => exact ⟨same.termSupportedToRight _ _ supported.1, same.termSupportedToRight _ _ supported.2.1, ()⟩
  | chain => exact ⟨same.termSupportedToRight _ _ supported.1, same.termSupportedToRight _ _ supported.2.1, ()⟩
  | weightedChain => exact ⟨same.termSupportedToRight _ _ supported.1, same.termSupportedToRight _ _ supported.2.1, ()⟩
  | multiplyComm => exact ⟨same.termSupportedToRight _ _ supported.1, same.termSupportedToRight _ _ supported.2.1, ()⟩
  | multiplyAssoc => exact ⟨same.termSupportedToRight _ _ supported.1, same.termSupportedToRight _ _ supported.2.1, ()⟩
  | marginalizeCongr nodes inner ih =>
      exact ⟨same.termSupportedToRight _ _ supported.1, same.termSupportedToRight _ _ supported.2.1,
        fun variant member => ih (supported.2.2 variant member)⟩
  | evaluateAtCongr fixed inner ih => exact ⟨same.termSupportedToRight _ _ supported.1, same.termSupportedToRight _ _ supported.2.1, ih supported.2.2⟩
  | addCongr first second firstIH secondIH =>
      exact ⟨same.termSupportedToRight _ _ supported.1, same.termSupportedToRight _ _ supported.2.1,
        firstIH supported.2.2.1, secondIH supported.2.2.2⟩
  | multiplyCongr first second firstIH secondIH =>
      exact ⟨same.termSupportedToRight _ _ supported.1, same.termSupportedToRight _ _ supported.2.1,
        firstIH supported.2.2.1, secondIH supported.2.2.2⟩
  | @weightedMultiplyCongr weight _ _ _ first second firstIH secondIH =>
      exact ⟨same.termSupportedToRight _ _ supported.1, same.termSupportedToRight _ _ supported.2.1,
        firstIH supported.2.2.1, fun positive => secondIH (supported.2.2.2 (same.positiveSupportedToLeft weight reference positive))⟩
  | divideCongr numerator denominator numeratorIH denominatorIH =>
      exact ⟨same.termSupportedToRight _ _ supported.1, same.termSupportedToRight _ _ supported.2.1,
        numeratorIH supported.2.2.1, denominatorIH supported.2.2.2⟩
  | eqCongr _hfirst _hsecond inner ih => exact ⟨same.termSupportedToRight _ _ supported.1, same.termSupportedToRight _ _ supported.2.1, ih supported.2.2⟩

end CausalSupportAgreement
end Thesis.Causality
