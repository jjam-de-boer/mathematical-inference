import Thesis.CausalTransport.HiddenDAGPolynomialEvidence
import Thesis.Examples.HiddenDAGCollapse

namespace Thesis
namespace Causality
namespace Examples
namespace HiddenDAGPolynomialEvidence

open Probability HiddenDAGCollapse

/-!
# Observed-data certificates on the native hidden-relay template

Setting `X = false` gives `Y = U`, while factual `Z = U`. A recorded observed
probability `P(Z = true) = 1/2` therefore pins down the intervention probability
on this template. The checker establishes its two bounds by polynomial
identity against the compiled data equation; no assumed identity between the
two causal probabilities is supplied.

The same accepted certificate is used for every replacement source law that
fits the data. A deterministic-false replacement is also constructed: it does
not fit the half-probability observation and cannot inherit that bound without
the required hypothesis. These are fixed-mechanism examples, not a graph-level
identifiability result. Signed targets and an automatically complete observed
table are checked separately below.
-/

def half : QProb := ⟨1, 2, by decide⟩
def observedQuery : NativeProbabilityQuery signature := ⟨HardIntervention.empty signature, fun assignment => assignment z⟩
def targetQuery : NativeProbabilityQuery signature := ⟨forceXFalse, fun assignment => assignment y⟩
def equations : Fin 1 → NativeProbabilityEquation signature := fun _ => ⟨observedQuery, half⟩
def target : NativePolynomialExpression signature := .probability targetQuery
def dataIndex : Fin (projection.hiddenDAG.count + 1) := ⟨5, by decide⟩
def lowerCertificate : model.ExpressionBoundCertificate 1 :=
  ⟨[], [⟨dataIndex, RationalPolynomial.constant SignedRatio.one⟩]⟩
def upperCertificate : model.ExpressionBoundCertificate 1 :=
  ⟨[], [⟨dataIndex, RationalPolynomial.constant ⟨-1, 1, by decide⟩⟩]⟩

theorem original_fits : model.SatisfiesProbabilityEquations equations := by decide +kernel
theorem lower_checked : model.checkExpressionLower equations target half.toSignedRatio lowerCertificate = true := by decide +kernel
theorem upper_checked : model.checkExpressionUpper equations target half.toSignedRatio upperCertificate = true := by decide +kernel

/-- Reusing the fitted-half certificate cannot certify a different bound:
the target expression and reference constant are part of the checked identity,
not ignored metadata attached to an otherwise accepted data constraint. -/
theorem incorrect_bound_rejected : model.checkExpressionLower equations target ⟨3, 4, by decide⟩ lowerCertificate = false := by
  decide +kernel

theorem original_bounds : SignedRatio.LE half.toSignedRatio (model.expressionValue target) ∧
    SignedRatio.LE (model.expressionValue target) half.toSignedRatio :=
  ⟨model.checkExpressionLower_sound equations target _ lowerCertificate lower_checked original_fits,
    model.checkExpressionUpper_sound equations target _ upperCertificate upper_checked original_fits⟩

/-- Fitting is tested on the replacement law, not transported from the
fixture. The polynomial certificate itself need only be checked once. -/
theorem every_fitted_source_law_bounds (law : FiniteProduct.IndependentLaw model.Noise)
    (fits : (model.withSourceLaw law).SatisfiesProbabilityEquations equations) :
    SignedRatio.LE half.toSignedRatio ((model.withSourceLaw law).expressionValue target) ∧
      SignedRatio.LE ((model.withSourceLaw law).expressionValue target) half.toSignedRatio :=
  ⟨model.checkExpressionLower_sound_forSourceLaw equations target half.toSignedRatio lowerCertificate lower_checked law fits,
    model.checkExpressionUpper_sound_forSourceLaw equations target half.toSignedRatio upperCertificate upper_checked law fits⟩

/-- Negative expression values are auxiliary signed rationals, not negative
source weights. This certificate exercises multiplication by a signed constant. -/
def negativeTarget : NativePolynomialExpression signature := .mul (.constant ⟨-1, 1, by decide⟩) target
def negativeHalf : SignedRatio := ⟨-1, 2, by decide⟩
theorem negative_lower_checked : model.checkExpressionLower equations negativeTarget negativeHalf upperCertificate = true := by decide +kernel
theorem negative_upper_checked : model.checkExpressionUpper equations negativeTarget negativeHalf lowerCertificate = true := by decide +kernel
theorem negative_actual_bounds : SignedRatio.LE negativeHalf (model.expressionValue negativeTarget) ∧
    SignedRatio.LE (model.expressionValue negativeTarget) negativeHalf :=
  ⟨model.checkExpressionLower_sound equations negativeTarget _ upperCertificate negative_lower_checked original_fits,
    model.checkExpressionUpper_sound equations negativeTarget _ lowerCertificate negative_upper_checked original_fits⟩

theorem complete_observation_fits : model.SatisfiesProbabilityEquations
    (FiniteHiddenDAGSCM.observationalEquations signature model.observationalDist) :=
  (model.satisfies_observationalEquations_iff model.observationalDist).mpr (fun _ => QProb.equiv_refl _)

def falseBit : FiniteProbRecord Bool := ⟨[(false, 1)], 1, by decide, rfl⟩
def falseLaw : FiniteProduct.IndependentLaw model.Noise where
  factor := fun _ => falseBit
  prior := FiniteProduct.record 5 (fun _ => Bool) (fun _ => falseBit)
  product_law := FiniteProduct.record_rectangular_probVal 5 (fun _ => Bool) (fun _ => falseBit)
theorem replacement_does_not_fit : ¬ (model.withSourceLaw falseLaw).SatisfiesProbabilityEquations equations := by
  intro fits
  exact (by decide +kernel : ¬ QProb.Equiv ((model.withSourceLaw falseLaw).interventionalValue observedQuery.intervention observedQuery.event) half)
    (fits ⟨0, by decide⟩)

end HiddenDAGPolynomialEvidence
end Examples
end Causality
end Thesis
