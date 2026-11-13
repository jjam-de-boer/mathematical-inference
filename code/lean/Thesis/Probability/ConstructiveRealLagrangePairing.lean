import Thesis.Probability.ConstructiveRealEntropyGlobalOptimality

namespace Thesis.Probability.Distros.RationalEntropyProblem
open ConstructiveReal
open RationalLinear

/-- Pairing an affine multiplier equation with a direction is exactly the
sum of its normalization and original-row pairings. No sign, independence,
or zero-row-direction assumption is used in this finite Fubini identity. -/
theorem LagrangeCoefficients.pairing {problem : RationalEntropyProblem variables} {gradient : Fin variables → ConstructiveReal}
    (certificate : problem.LagrangeCoefficients gradient) (directions : Fin variables → ConstructiveReal) :
    Equiv (FiniteLinear.pair variables gradient directions)
      (add (mul certificate.offset (realDot variables (fun _ => 1) directions))
        (FiniteLinear.pair problem.rows.length certificate.coefficient
          (fun row => realRationalDot variables (problem.rows[row.val]).coefficients directions))) := by
  let matrix := fun row : Fin problem.rows.length => fun column => ofSignedRatio ((problem.rows[row.val]).coefficients column)
  let score := fun column => realRationalDot problem.rows.length (fun row => (problem.rows[row.val]).coefficients column) certificate.coefficient
  have scorePair : Equiv (FiniteLinear.pair variables score directions)
      (FiniteLinear.pair problem.rows.length certificate.coefficient
        (fun row => realRationalDot variables (problem.rows[row.val]).coefficients directions)) :=
    equiv_trans (FiniteLinear.pair_congr variables _ _ directions directions (fun column =>
      equiv_trans (realRationalDot_pair problem.rows.length _ certificate.coefficient) (FiniteLinear.pair_comm _ _ _)) (fun _ => equiv_refl _))
      (equiv_trans (FiniteLinear.combination_pair problem.rows.length variables matrix certificate.coefficient directions)
        (FiniteLinear.pair_congr problem.rows.length certificate.coefficient certificate.coefficient _ _
          (fun _ => equiv_refl _) (fun row => equiv_symm (realRationalDot_pair variables (problem.rows[row.val]).coefficients directions))))
  have constantPair : Equiv (FiniteLinear.pair variables (fun _ => certificate.offset) directions)
      (mul certificate.offset (realDot variables (fun _ => 1) directions)) :=
    equiv_trans (FiniteLinear.pair_congr variables _ (fun _ => mul certificate.offset one) directions directions
      (fun _ => equiv_symm (mul_one certificate.offset)) (fun _ => equiv_refl _))
      (equiv_trans (FiniteLinear.pair_scale_first variables certificate.offset (fun _ => one) directions)
        (mul_congr (equiv_refl _) (equiv_symm (FiniteLinear.realDot_pair variables (fun _ => 1) directions))))
  exact equiv_trans (FiniteLinear.pair_congr variables _ _ directions directions certificate.represents (fun _ => equiv_refl _))
    (equiv_trans (FiniteLinear.pair_add_first variables (fun _ => certificate.offset) score directions) (add_congr constantPair scorePair))

/-- Normalized feasible differences cancel the affine normalization term;
only original expectation-row pairings remain. -/
theorem LagrangeCoefficients.pairing_normalized {problem : RationalEntropyProblem variables} {gradient : Fin variables → ConstructiveReal}
    (certificate : problem.LagrangeCoefficients gradient) (directions : Fin variables → ConstructiveReal)
    (normalized : Equiv (realDot variables (fun _ => 1) directions) zero) :
    Equiv (FiniteLinear.pair variables gradient directions)
      (FiniteLinear.pair problem.rows.length certificate.coefficient
        (fun row => realRationalDot variables (problem.rows[row.val]).coefficients directions)) :=
  equiv_trans (certificate.pairing directions)
    (equiv_trans (add_congr (equiv_trans (mul_congr (equiv_refl _) normalized) (mul_zero _)) (equiv_refl _)) (zero_add _))

end Thesis.Probability.Distros.RationalEntropyProblem
