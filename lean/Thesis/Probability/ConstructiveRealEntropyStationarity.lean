import Thesis.Probability.ConstructiveRealAffineSimplex
import Thesis.Probability.ConstructiveDerivativeExtremum
import Thesis.Probability.ConstructiveRealRationalEntropyOptimizer

namespace Thesis.Probability.Distros.RationalEntropyProblem
open ConstructiveReal

/-- Directions in the kernel of normalization and all supplied rational
constraint rows. For equality-constrained problems these are precisely the
linear tangent conditions. For interval problems this is a necessary
stationarity subspace, not the full signed KKT condition. -/
def ConstraintKernel (problem : RationalEntropyProblem variables) (directions : Fin variables → ConstructiveReal) : Prop :=
  Equiv (RationalLinear.realDot variables (fun _ => 1) directions) zero ∧
  ∀ row ∈ problem.rows, Equiv (RationalLinear.realDot variables row.clear.coefficients directions) zero

/-- A positive feasible point admits an explicitly computed two-sided
feasible affine path along every kernel direction. Original rational rows
remain exact; no tolerance is substituted for equality or feasibility. -/
def RealLaw.tangentLine {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (directions : Fin variables → ConstructiveReal) (tangent : problem.ConstraintKernel directions)
    (lower : Fin variables → PositiveRatio) (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (law.mass i).value)
    (parameter : ConstructiveReal)
    (close : Within (affinePositiveRadius (fun i => (law.mass i).value) directions lower).toQProb zero parameter) : problem.RealLaw := by
  let values := fun i => affineCoordinate (law.mass i).value (directions i) parameter
  have inside := RationalLinear.affine_simplex_positive_near (fun i => (law.mass i).value) directions lower positive
    law.normalized tangent.1 parameter close
  have nonnegative (i : Fin variables) : LE zero (values i) := entropyPositiveNonnegative (lower i).half _ (inside i)
  have normalized := equiv_trans (RationalLinear.realDot_affineCoordinate_fixed variables (fun _ => 1)
    (fun i => (law.mass i).value) directions tangent.1 parameter) law.normalized
  apply RealLaw.ofVector problem values (RationalLinear.real_simplex_of_nonnegative values nonnegative normalized)
  intro row member
  have original := (row.clear_real_iff (fun i => (law.mass i).value)).mpr (law.valid row member)
  have evaluation := RationalLinear.realDot_affineCoordinate_fixed variables row.clear.coefficients
    (fun i => (law.mass i).value) directions (tangent.2 row member) parameter
  exact (row.clear_real_iff values).mp ((le_congr evaluation (equiv_refl _)).mpr original)

private theorem tangentLine_entropy {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (directions : Fin variables → ConstructiveReal) (tangent : problem.ConstraintKernel directions)
    (lower : Fin variables → PositiveRatio) (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (law.mass i).value)
    (parameter : ConstructiveReal)
    (close : Within (affinePositiveRadius (fun i => (law.mass i).value) directions lower).toQProb zero parameter) :
    Equiv (law.tangentLine directions tangent lower positive parameter close).entropy
      (entropyLine (fun i => (law.mass i).value) directions (fun i => (lower i).half) parameter
        (RationalLinear.affine_simplex_positive_near _ _ lower positive law.normalized tangent.1 parameter close)) := equiv_refl _

private theorem entropyLine_zero {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (directions : Fin variables → ConstructiveReal) (lower : Fin variables → PositiveRatio)
    (inside : entropyLineDomain (fun i => (law.mass i).value) directions lower zero) :
    Equiv (entropyLine (fun i => (law.mass i).value) directions lower zero inside) law.entropy := by
  unfold entropyLine RealLaw.entropy realEntropySum
  simp only [List.map_map]
  exact listSum_map_congr (List.finRange variables) _ _ (fun i _ =>
    realEntropyTerm_congr (affineCoordinate_zero _ _) _ (law.mass i).nonnegative _ (law.mass i).bounded)

/-- Necessary entropy stationarity at a certified positive maximum. The
neighborhood and row preservation are constructed above, so the conclusion
does not assume that all small perturbations happen to be feasible. Rows
may be redundant and directions analytic; arbitrary real comparisons and
row-rank assumptions are unnecessary for this kernel form. This is the
annihilation step toward multipliers, not a multiplier-existence theorem. -/
theorem RealLaw.maximum_stationary {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (maximal : law.Maximal) (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (law.mass i).value)
    (directions : Fin variables → ConstructiveReal) (tangent : problem.ConstraintKernel directions) :
    Equiv (listSum ((List.finRange variables).map (fun i =>
      mul (directions i) (entropyBitGradient (law.mass i).value (lower i) (positive i))))) zero := by
  let masses := fun i => (law.mass i).value
  have inside (i : Fin variables) : entropyPositiveDomain (lower i).half (masses i) :=
    ⟨positive_half_lower (masses i) (masses i) (lower i) (positive i) (within_refl _ _), (law.mass i).bounded⟩
  let derivative := entropyLine_hasDerivativeWithinAt masses directions (fun i => (lower i).half) inside
  let radius := affinePositiveRadius masses directions lower
  have admitted := RationalLinear.affine_simplex_positive_near masses directions lower positive law.normalized tangent.1
  have maximum (parameter : ConstructiveReal) (supplied : entropyLineDomain masses directions (fun i => (lower i).half) parameter)
      (close : Within radius.toQProb zero parameter) :
      LE (entropyLine masses directions (fun i => (lower i).half) parameter supplied)
        (entropyLine masses directions (fun i => (lower i).half) zero (entropyLineDomain_zero masses directions _ inside)) := by
    have upper := maximal (law.tangentLine directions tangent lower positive parameter close)
    exact (le_congr (tangentLine_entropy law directions tangent lower positive parameter close)
      (equiv_symm (entropyLine_zero law directions _ _))).mp upper
  have stationary := derivative.slope_zero_of_local_maximum radius admitted maximum
  have same := listSum_map_congr (List.finRange variables) _ _ (fun i _ =>
    mul_congr (equiv_refl (directions i)) (neg_congr (add_congr
      (positiveLog2_congr (equiv_refl (masses i)) (lower i).half (lower i) (inside i).1 (positive i))
      (equiv_refl RationalLogSecant.limit))))
  exact equiv_trans (equiv_symm same) stationary

/-- The same necessary condition in natural units. `ln(2)` converts the
entire bit-unit gradient, so no multiplier calibration factor is omitted. -/
theorem RealLaw.maximum_stationary_natural {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (maximal : law.Maximal) (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (law.mass i).value)
    (directions : Fin variables → ConstructiveReal) (tangent : problem.ConstraintKernel directions) :
    Equiv (listSum ((List.finRange variables).map (fun i =>
      mul (directions i) (entropyNaturalGradient (law.mass i).value (lower i) (positive i))))) zero :=
  equiv_trans (equiv_symm (entropyFirstVariation_units _ (fun i => (law.mass i).value) directions lower positive))
    (equiv_trans (mul_congr (law.maximum_stationary maximal lower positive directions tangent) (equiv_refl lnTwo)) (zero_mul lnTwo))

end Thesis.Probability.Distros.RationalEntropyProblem
