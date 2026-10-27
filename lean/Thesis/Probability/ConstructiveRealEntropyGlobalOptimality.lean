import Thesis.Probability.ConstructiveRealGibbsInequality
import Thesis.Probability.ConstructiveRealEqualityConstraints
import Thesis.Probability.ConstructiveRealEntropyMultipliers

namespace Thesis.Probability.Distros.RationalEntropyProblem
open ConstructiveReal
open RationalLinear

/-- Affine gradient coefficients annihilate every direction preserving
normalization and the original rational row expectations. -/
theorem LagrangeCoefficients.annihilates {problem : RationalEntropyProblem variables} {gradient : Fin variables → ConstructiveReal}
    (certificate : problem.LagrangeCoefficients gradient) (directions : Fin variables → ConstructiveReal)
    (normalized : Equiv (realDot variables (fun _ => 1) directions) zero)
    (fixed : ∀ row : Fin problem.rows.length,
      Equiv (realRationalDot variables (problem.rows[row.val]).coefficients directions) zero) :
    Equiv (FiniteLinear.pair variables gradient directions) zero := by
  let matrix := fun row : Fin problem.rows.length => fun column => ofSignedRatio ((problem.rows[row.val]).coefficients column)
  let score := fun column => realRationalDot problem.rows.length (fun row => (problem.rows[row.val]).coefficients column) certificate.coefficient
  have scorePair : Equiv (FiniteLinear.pair variables score directions) zero := by
    have rewritten : Equiv (FiniteLinear.pair variables score directions)
        (FiniteLinear.pair variables (fun column => FiniteLinear.pair problem.rows.length certificate.coefficient (fun row => matrix row column)) directions) :=
      FiniteLinear.pair_congr variables _ _ directions directions (fun column =>
        equiv_trans (realRationalDot_pair problem.rows.length _ certificate.coefficient) (FiniteLinear.pair_comm _ _ _)) (fun _ => equiv_refl _)
    have rowsZero (row : Fin problem.rows.length) : Equiv (FiniteLinear.pair variables (matrix row) directions) zero :=
      equiv_trans (equiv_symm (realRationalDot_pair variables (problem.rows[row.val]).coefficients directions)) (fixed row)
    exact equiv_trans rewritten (equiv_trans (FiniteLinear.combination_pair problem.rows.length variables matrix certificate.coefficient directions)
      (equiv_trans (FiniteLinear.pair_congr problem.rows.length certificate.coefficient certificate.coefficient _ (fun _ => zero)
        (fun _ => equiv_refl _) rowsZero) (FiniteLinear.pair_zero_second _ _)))
  have expanded : Equiv (FiniteLinear.pair variables gradient directions)
      (FiniteLinear.pair variables (fun column => add certificate.offset (score column)) directions) :=
    FiniteLinear.pair_congr variables _ _ directions directions certificate.represents (fun _ => equiv_refl _)
  exact equiv_trans expanded (equiv_trans (FiniteLinear.pair_add_first variables (fun _ => certificate.offset) score directions)
    (equiv_trans (add_congr (FiniteLinear.pair_constant_kernel variables certificate.offset directions normalized) scorePair) (zero_add zero)))

/-- Fixed expectations and the affine multiplier equation force exactly
constant cross entropy, including for boundary competing laws. -/
theorem RealLaw.crossEntropy_eq_of_coefficients {problem : RationalEntropyProblem variables} (reference observed : problem.RealLaw)
    (lower : Fin variables → PositiveRatio) (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference.mass i).value)
    (certificate : problem.LagrangeCoefficients (fun i => entropyBitGradient (reference.mass i).value (lower i) (positive i)))
    (fixed : ∀ row ∈ problem.rows,
      Equiv (realRationalDot variables row.coefficients (fun i => (observed.mass i).value))
        (realRationalDot variables row.coefficients (fun i => (reference.mass i).value))) :
    Equiv (realCrossEntropySum observed.mass reference.mass lower positive) reference.entropy := by
  let directions := fun i => sub (observed.mass i).value (reference.mass i).value
  have normalized : Equiv (realDot variables (fun _ => 1) directions) zero :=
    equiv_trans (realDot_sub_values variables (fun _ => 1) _ _)
      (equiv_trans (add_congr observed.normalized (neg_congr reference.normalized)) ((sub_equiv_zero_iff one one).mpr (equiv_refl one)))
  have rowsZero (row : Fin problem.rows.length) : Equiv (realRationalDot variables (problem.rows[row.val]).coefficients directions) zero :=
    equiv_trans (realRationalDot_sub_values variables (problem.rows[row.val]).coefficients _ _)
      ((sub_equiv_zero_iff _ _).mpr (fixed _ (List.getElem_mem row.isLt)))
  have slope := equiv_trans (FiniteLinear.pair_comm variables directions _)
    (certificate.annihilates directions normalized rowsZero)
  exact equiv_trans (equiv_symm (realEntropy_tangent_eq_crossEntropy observed.mass reference.mass observed.normalized reference.normalized lower positive))
    (equiv_trans (add_congr (equiv_refl _) slope) (add_zero _))

/-- On fixed expectations, KL is exactly the entropy gap to the positive
log-linear reference. Zero competing coordinates retain the continuous
convention from the global KL theorem. -/
theorem RealLaw.relativeEntropy_eq_gap_of_coefficients {problem : RationalEntropyProblem variables} (reference observed : problem.RealLaw)
    (lower : Fin variables → PositiveRatio) (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference.mass i).value)
    (certificate : problem.LagrangeCoefficients (fun i => entropyBitGradient (reference.mass i).value (lower i) (positive i)))
    (fixed : ∀ row ∈ problem.rows,
      Equiv (realRationalDot variables row.coefficients (fun i => (observed.mass i).value))
        (realRationalDot variables row.coefficients (fun i => (reference.mass i).value))) :
    Equiv (realRelativeEntropySum observed.mass reference.mass lower positive) (sub reference.entropy observed.entropy) :=
  equiv_trans (realRelativeEntropySum_decomposition observed.mass reference.mass lower positive)
    (add_congr (reference.crossEntropy_eq_of_coefficients observed lower positive certificate fixed) (equiv_refl _))

/-- Global sufficiency now follows directly from Gibbs: the declared fixed
rows make cross entropy equal the reference entropy. Paired rational rows
below discharge this expectation condition, rather than assuming the result. -/
theorem RealLaw.maximal_of_fixed_rows_coefficients {problem : RationalEntropyProblem variables} (reference : problem.RealLaw)
    (lower : Fin variables → PositiveRatio) (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference.mass i).value)
    (certificate : problem.LagrangeCoefficients (fun i => entropyBitGradient (reference.mass i).value (lower i) (positive i)))
    (fixed : ∀ observed : problem.RealLaw, ∀ row ∈ problem.rows,
      Equiv (realRationalDot variables row.coefficients (fun i => (observed.mass i).value))
        (realRationalDot variables row.coefficients (fun i => (reference.mass i).value))) : reference.Maximal := by
  intro observed
  exact (le_congr (equiv_refl _) (reference.crossEntropy_eq_of_coefficients observed lower positive certificate (fixed observed))).mp
    (realEntropySum_le_crossEntropy observed.mass reference.mass observed.normalized reference.normalized lower positive)

/-- Sufficient global Lagrange optimality for fixed rational expectations.
All competing laws, including those on a boundary face, are quantified. -/
theorem equalities_maximal_of_coefficients (nonempty : 0 < variables) (features : List (RationalConstraint variables))
    (reference : (equalities variables nonempty features).RealLaw) (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference.mass i).value)
    (certificate : (equalities variables nonempty features).LagrangeCoefficients
      (fun i => entropyBitGradient (reference.mass i).value (lower i) (positive i))) : reference.Maximal :=
  reference.maximal_of_fixed_rows_coefficients lower positive certificate (fun observed row member =>
    equiv_trans (equalities_allRows_exact nonempty features observed row member)
      (equiv_symm (equalities_allRows_exact nonempty features reference row member)))

/-- Necessary and sufficient positive-interior multiplier criterion, with
actual finite rational expectation constraints. The necessary direction
constructs the coefficients by elimination and assumes no rank condition. -/
theorem equalities_maximal_iff_coefficients (nonempty : 0 < variables) (features : List (RationalConstraint variables))
    (reference : (equalities variables nonempty features).RealLaw) (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference.mass i).value) :
    reference.Maximal ↔ Nonempty ((equalities variables nonempty features).LagrangeCoefficients
      (fun i => entropyBitGradient (reference.mass i).value (lower i) (positive i))) :=
  ⟨fun maximal => ⟨reference.lagrangeMultipliers maximal lower positive⟩,
    fun ⟨certificate⟩ => equalities_maximal_of_coefficients nonempty features reference lower positive certificate⟩

/-- The converse unit conversion acts on actual coefficient data, including
the normalization coefficient. It uses the proved reciprocal calibration. -/
def RealLaw.coefficientsToBits {problem : RationalEntropyProblem variables} (reference : problem.RealLaw)
    (lower : Fin variables → PositiveRatio) (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference.mass i).value)
    (certificate : problem.LagrangeCoefficients (fun i => entropyNaturalGradient (reference.mass i).value (lower i) (positive i))) :
    problem.LagrangeCoefficients (fun i => entropyBitGradient (reference.mass i).value (lower i) (positive i)) := by
  apply certificate.scale RationalLogSecant.limit _
  intro i
  exact equiv_trans (mul_congr (equiv_symm (entropyGradient_units _ _ _)) (equiv_refl _))
    (equiv_trans (mul_assoc _ _ _) (equiv_trans (mul_congr (equiv_refl _)
      (equiv_trans (mul_comm _ _) coefficient_mul_lnTwo)) (mul_one _)))

theorem equalities_maximal_of_natural_coefficients (nonempty : 0 < variables) (features : List (RationalConstraint variables))
    (reference : (equalities variables nonempty features).RealLaw) (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference.mass i).value)
    (certificate : (equalities variables nonempty features).LagrangeCoefficients
      (fun i => entropyNaturalGradient (reference.mass i).value (lower i) (positive i))) : reference.Maximal :=
  equalities_maximal_of_coefficients nonempty features reference lower positive (reference.coefficientsToBits lower positive certificate)

theorem equalities_maximal_iff_natural_coefficients (nonempty : 0 < variables) (features : List (RationalConstraint variables))
    (reference : (equalities variables nonempty features).RealLaw) (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference.mass i).value) :
    reference.Maximal ↔ Nonempty ((equalities variables nonempty features).LagrangeCoefficients
      (fun i => entropyNaturalGradient (reference.mass i).value (lower i) (positive i))) :=
  ⟨fun maximal => ⟨reference.naturalLagrangeMultipliers maximal lower positive⟩,
    fun ⟨certificate⟩ => equalities_maximal_of_natural_coefficients nonempty features reference lower positive certificate⟩

end Thesis.Probability.Distros.RationalEntropyProblem
