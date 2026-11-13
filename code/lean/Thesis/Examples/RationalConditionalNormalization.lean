import Thesis.Probability.Distros.RationalConditionalNormalization
import Thesis.Probability.Distros.RationalSimplex

namespace Thesis.Probability.Examples.RationalConditionalNormalization

open Distros.RationalLinear Conditional

/-!
# Proper evidence, a nonconstant outcome, and no null-evidence completion

Three equiprobable cells have evidence on the first two and outcome on the
first. The evidence is genuinely neither null nor certain, and its conditional
outcome has probability one half. Normalizing and decoding keep that value.
The last theorem excludes every normalized witness for zero evidence; it does
not assign a default fraction when the original conditioner is unsupported.
-/

def weights (_ : Fin 3) : SignedRatio := ⟨1, 3, by decide⟩
def denominator (i : Fin 3) : Int := if i.val < 2 then 1 else 0
def numerator (i : Fin 3) : Int := if i.val = 0 then 1 else 0

def source : SupportedAssignment (simplexRows 3) denominator where
  values := weights
  feasible := (satisfies_simplex_iff 3 weights).mpr ⟨by decide +kernel, by decide +kernel⟩
  positive := by decide +kernel
  bounded := by decide +kernel

def normalized := source.normalize
def half : SignedRatio := ⟨1, 2, by decide⟩

theorem proper_evidence : SignedRatio.Equiv source.evidence ⟨2, 3, by decide⟩ := by
  decide +kernel

theorem scale_three_halves : SignedRatio.Equiv normalized.scale ⟨3, 2, by decide⟩ := by
  decide +kernel

theorem original_conditional_half : SignedRatio.Equiv (source.conditionalValue numerator) half := by
  decide +kernel

theorem normalized_objective_half : SignedRatio.Equiv (dot 3 numerator normalized.masses) half :=
  SignedRatio.equiv_trans (source.normalize_response numerator) original_conditional_half

theorem decoded_conditional_half : SignedRatio.Equiv (normalized.toSupported.conditionalValue numerator) half :=
  SignedRatio.equiv_trans (normalized.toSupported_response numerator) normalized_objective_half

theorem no_zero_evidence : ¬ Nonempty (NormalizedAssignment (simplexRows 3) (fun _ => 0)) := by
  rintro ⟨point⟩
  exact point.zero_denominator_impossible

end Thesis.Probability.Examples.RationalConditionalNormalization
