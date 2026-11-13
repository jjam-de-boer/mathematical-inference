import Thesis.Causality.DerivationLinearization
import Thesis.CausalTransport.NativeDerivationSupportCheck

namespace Thesis.Causality

open Probability

/-!
# Exact native support for elementary rewrite paths

A whole derivation may have unsupported intermediate expressions despite
supported endpoints. An *elementary* step has no hidden transitivity, and
its native support is exactly support of its two complete endpoint terms.
The frame proof below retains strict sums, fixed-reference substitution and
the positive-only factor obligation of weighted multiplication.

Consequently a finite elementary path can be checked by visiting all its
vertices. This is not a finite-state quotient of numerical terms, nor a
decision that some unbounded path exists. Reinterpretation reconstructs the
old recursive support tree; no new causal soundness law is assumed here.
-/

variable {S : ObservedSignature} {P : FiniteLatentProjection S} {G : ObservedGraph S}

namespace HiddenDAGLocalDerivationSupport

/-- Expose endpoints through the indexed support recursor. Its outer product
does not reduce on an unknown derivation, so callers must not project it by
assuming that the compiler has already inspected the hidden constructor. -/
noncomputable def endpoints (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation G left right)
    (supported : HiddenDAGLocalDerivationSupport model reference derivation) :
    model.TermSupportedAt left reference × model.TermSupportedAt right reference := by
  cases derivation <;> exact ⟨supported.1, supported.2.1⟩

end HiddenDAGLocalDerivationSupport

namespace ProbabilityTermFrame

/-- Lift an endpoint-exact inner step. The hypothesis is available at every
reference because a marginal frame must inspect every actual substitution,
not merely the outer reference. All support data use the model's own values. -/
noncomputable def liftSupportOfEndpoints (frame : ProbabilityTermFrame S)
    (model : FiniteHiddenDAGSCM S P) {left right : ProbabilityTerm S}
    (inner : DoCalculusDerivation G left right)
    (supply : ∀ reference, model.TermSupportedAt left reference → model.TermSupportedAt right reference →
      HiddenDAGLocalDerivationSupport model reference inner)
    (reference : S.Assignment)
    (leftSupported : model.TermSupportedAt (frame.fill left) reference)
    (rightSupported : model.TermSupportedAt (frame.fill right) reference) :
    HiddenDAGLocalDerivationSupport model reference (frame.lift inner) := by
  cases frame with
  | marginalize nodes =>
      refine ⟨leftSupported, rightSupported, fun variant member => ?_⟩
      exact supply variant
        (ProbabilityResult.supported_map_of_mem_sum _ _ variant member leftSupported)
        (ProbabilityResult.supported_map_of_mem_sum _ _ variant member rightSupported)
  | evaluateAt fixed => exact ⟨leftSupported, rightSupported, supply fixed leftSupported rightSupported⟩
  | addLeft fixed =>
      exact ⟨leftSupported, rightSupported,
        supply reference (ProbabilityResult.supported_left_of_add leftSupported) (ProbabilityResult.supported_left_of_add rightSupported),
        ProbabilityResult.supported_right_of_add leftSupported, ProbabilityResult.supported_right_of_add leftSupported, ()⟩
  | addRight fixed =>
      exact ⟨leftSupported, rightSupported,
        ⟨ProbabilityResult.supported_left_of_add leftSupported, ProbabilityResult.supported_left_of_add leftSupported, ()⟩,
        supply reference (ProbabilityResult.supported_right_of_add leftSupported) (ProbabilityResult.supported_right_of_add rightSupported)⟩
  | multiplyLeft fixed =>
      exact ⟨leftSupported, rightSupported,
        supply reference (ProbabilityResult.supported_left_of_multiply leftSupported) (ProbabilityResult.supported_left_of_multiply rightSupported),
        ProbabilityResult.supported_right_of_multiply leftSupported, ProbabilityResult.supported_right_of_multiply leftSupported, ()⟩
  | multiplyRight fixed =>
      exact ⟨leftSupported, rightSupported,
        ⟨ProbabilityResult.supported_left_of_multiply leftSupported, ProbabilityResult.supported_left_of_multiply leftSupported, ()⟩,
        supply reference (ProbabilityResult.supported_right_of_multiply leftSupported) (ProbabilityResult.supported_right_of_multiply rightSupported)⟩
  | weightedLeft fixed =>
      refine ⟨leftSupported, rightSupported,
        supply reference (ProbabilityResult.supported_weight_of_weightedMultiply leftSupported)
          (ProbabilityResult.supported_weight_of_weightedMultiply rightSupported), fun positive => ?_⟩
      let factor := ProbabilityResult.supported_factor_of_weightedMultiply positive leftSupported
      exact ⟨factor, factor, ()⟩
  | weightedRight fixed =>
      let weight := ProbabilityResult.supported_weight_of_weightedMultiply leftSupported
      exact ⟨leftSupported, rightSupported, ⟨weight, weight, ()⟩,
        fun positive => supply reference
          (ProbabilityResult.supported_factor_of_weightedMultiply positive leftSupported)
          (ProbabilityResult.supported_factor_of_weightedMultiply positive rightSupported)⟩
  | divideLeft fixed =>
      exact ⟨leftSupported, rightSupported,
        supply reference (ProbabilityResult.supported_numerator_of_divide leftSupported) (ProbabilityResult.supported_numerator_of_divide rightSupported),
        ProbabilityResult.supported_denominator_of_divide leftSupported, ProbabilityResult.supported_denominator_of_divide leftSupported, ()⟩
  | divideRight fixed =>
      exact ⟨leftSupported, rightSupported,
        ⟨ProbabilityResult.supported_numerator_of_divide leftSupported, ProbabilityResult.supported_numerator_of_divide leftSupported, ()⟩,
        supply reference (ProbabilityResult.supported_denominator_of_divide leftSupported) (ProbabilityResult.supported_denominator_of_divide rightSupported)⟩

end ProbabilityTermFrame

namespace DoCalculusRewriteStep

/-- One atomic leaf, however deeply framed or reversed, needs no support
beyond its complete endpoints. This statement is not true of arbitrary
transitivity trees and is deliberately restricted to `RewriteStep`. -/
noncomputable def supportOfEndpoints {left right : ProbabilityTerm S}
    (step : DoCalculusRewriteStep G left right) (model : FiniteHiddenDAGSCM S P)
    (reference : S.Assignment) (leftSupported : model.TermSupportedAt left reference)
    (rightSupported : model.TermSupportedAt right reference) :
    HiddenDAGLocalDerivationSupport model reference step.toDerivation := by
  induction step generalizing reference with
  | atom leaf => cases leaf <;> exact ⟨leftSupported, rightSupported, ()⟩
  | symm inner ih => exact ⟨leftSupported, rightSupported, ih reference rightSupported leftSupported⟩
  | under frame inner ih => exact frame.liftSupportOfEndpoints model inner.toDerivation ih reference leftSupported rightSupported

theorem check_eq_endpoints {left right : ProbabilityTerm S}
    (step : DoCalculusRewriteStep G left right) (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment) :
    HiddenDAGLocalDerivationSupport.check model reference step.toDerivation =
      ((model.termDenote left reference).isSome && (model.termDenote right reference).isSome) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro accepted
    have witnesses := HiddenDAGLocalDerivationSupport.endpoints model reference step.toDerivation
      (HiddenDAGLocalDerivationSupport.ofCheck model reference step.toDerivation accepted)
    exact Bool.and_eq_true_iff.mpr ⟨ProbabilityResult.supported_isSome witnesses.1, ProbabilityResult.supported_isSome witnesses.2⟩
  · intro endpoints
    have both := Bool.and_eq_true_iff.mp endpoints
    exact HiddenDAGLocalDerivationSupport.check_of_supported model reference step.toDerivation
      (step.supportOfEndpoints model reference (ProbabilityResult.supportedOfIsSome _ both.1) (ProbabilityResult.supportedOfIsSome _ both.2))

end DoCalculusRewriteStep

namespace DoCalculusRewritePath

/-- A linear scan of the actual path, retaining the vertex even for an empty
chain. No endpoint equality or support-pattern equality substitutes for a
checked equation. The existence of some passing path is a separate question. -/
def checkVertices (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    {left right : ProbabilityTerm S} : DoCalculusRewritePath G left right → Bool
  | .nil term => (model.termDenote term reference).isSome
  | @cons _ _ _ first _ _ _ tail => (model.termDenote first reference).isSome && tail.checkVertices model reference

noncomputable def supportOfCheckVertices (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    {left right : ProbabilityTerm S} (path : DoCalculusRewritePath G left right)
    (accepted : path.checkVertices model reference = true) : path.AllVertices (fun term => model.TermSupportedAt term reference) := by
  induction path with
  | nil term => exact ProbabilityResult.supportedOfIsSome _ accepted
  | cons step tail ih =>
      have both := Bool.and_eq_true_iff.mp accepted
      exact ⟨ProbabilityResult.supportedOfIsSome _ both.1, ih both.2⟩

theorem checkVertices_of_supported (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    {left right : ProbabilityTerm S} (path : DoCalculusRewritePath G left right)
    (supported : path.AllVertices (fun term => model.TermSupportedAt term reference)) :
    path.checkVertices model reference = true := by
  induction path with
  | nil term => exact ProbabilityResult.supported_isSome supported
  | cons step tail ih => exact Bool.and_eq_true_iff.mpr ⟨ProbabilityResult.supported_isSome supported.1, ih supported.2⟩

/-- Rebuild the complete old support tree, including framed branch checks,
from the values at the actual finite path vertices. No semantic law is added. -/
noncomputable def toDerivation_support (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    {left right : ProbabilityTerm S} (path : DoCalculusRewritePath G left right)
    (supported : path.AllVertices (fun term => model.TermSupportedAt term reference)) :
    HiddenDAGLocalDerivationSupport model reference path.toDerivation := by
  induction path with
  | nil term => exact ⟨supported, supported, ()⟩
  | cons step tail ih =>
      exact ⟨supported.1, AllVertices.last tail supported.2,
        step.supportOfEndpoints model reference supported.1 (AllVertices.first tail supported.2), ih supported.2⟩

/-- Read every actual vertex value back from the reconstructed support tree.
The converse needs no causal soundness: transitivity already retains its
intermediate endpoints, and an empty path retains its source value. -/
noncomputable def supportedVertices_of_toDerivation (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    {left right : ProbabilityTerm S} (path : DoCalculusRewritePath G left right)
    (supported : HiddenDAGLocalDerivationSupport model reference path.toDerivation) :
    path.AllVertices (fun term => model.TermSupportedAt term reference) := by
  induction path with
  | nil term => exact supported.1
  | cons step tail ih => exact ⟨supported.1, ih supported.2.2.2⟩

/-- The vertex scan and the established recursive checker agree exactly for
these finite elementary paths. This is not an existence test over all paths. -/
theorem checkVertices_eq_toDerivation (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    {left right : ProbabilityTerm S} (path : DoCalculusRewritePath G left right) :
    path.checkVertices model reference = HiddenDAGLocalDerivationSupport.check model reference path.toDerivation := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro accepted
    exact HiddenDAGLocalDerivationSupport.check_of_supported model reference _
      (path.toDerivation_support model reference (path.supportOfCheckVertices model reference accepted))
  · intro accepted
    exact path.checkVertices_of_supported model reference
      (path.supportedVertices_of_toDerivation model reference
        (HiddenDAGLocalDerivationSupport.ofCheck model reference _ accepted))

end DoCalculusRewritePath
end Thesis.Causality
