import Thesis.Examples.ConstructiveEntropyOptimizer
import Thesis.Probability.ConstructiveRealFaceMultipliers
import Thesis.Probability.ConstructiveRealEntropyPartitionIdentity

namespace Thesis.Examples.EntropyMeanHalfGibbs
open Probability Probability.Distros ConstructiveReal
open RationalEntropyProblem

private abbrev problem := EntropyMeanHalf.problem
private def i0 : Fin problem.cells.length := ⟨0, by decide +kernel⟩
private def i1 : Fin problem.cells.length := ⟨1, by decide +kernel⟩
private def i2 : Fin problem.cells.length := ⟨2, by decide +kernel⟩
/-- The same ideal law previously enclosed by the original rational
certificate, transferred without changing its coordinates or constraints. -/
def ideal : problem.analyticProblem.RealLaw := ConstructiveEntropyOptimizer.meanHalfIdeal.toRationalLaw
private theorem maximal : ideal.Maximal := fun other =>
  problem.idealEntropyLaw_maximal EntropyMeanHalf.anchor (PartialMomentProblem.RationalLaw.toMomentLaw other)
private theorem anchorPositive : EntropyMeanHalf.anchor.distro.GridPositive problem.entropyGrid := by
  change ∀ value ∈ [0, 1, 2], 0 < (EntropyMeanHalf.anchor.distro.pmf value).num
  decide +kernel
private def anchorLower := EntropyMeanHalf.anchor.positiveFloors anchorPositive
def lower (i : Fin problem.cells.length) := interiorLower problem.cells.length (anchorLower i)
theorem positive (i : Fin problem.cells.length) : LE (ofSignedRatio (lower i).toSignedRatio) (ideal.mass i).value :=
  ideal.maximum_positive EntropyMeanHalf.anchor.toReal.toRationalLaw maximal anchorLower
    (EntropyMeanHalf.anchor.positiveFloors_le anchorPositive) i

/-- These multipliers are constructed from the actual positive maximum.
Redundant original rows remain present; no parameter solution is assumed. -/
opaque multipliers : problem.analyticProblem.LagrangeCoefficients
    (fun i => entropyNaturalGradient (ideal.mass i).value (lower i) (positive i)) :=
  ideal.naturalLagrangeMultipliers maximal lower positive

theorem gibbs (i : Fin problem.cells.length) : Equiv (ideal.mass i).value
    (mul (neg (multipliers.score i)).exp multipliers.partitionInverse) :=
  gibbsForm_of_coefficients ideal lower positive multipliers i

/-- The old exactly feasible rational certificate also encloses this
multiplier-described ideal entropy. It does not assert a rational optimum. -/
theorem certificate_bounds :
    LE (ofSignedRatio (⟨2599, 2000, by decide⟩ : QProb).toSignedRatio) ideal.entropy ∧
      LE ideal.entropy (ofSignedRatio (⟨2601, 2000, by decide⟩ : QProb).toSignedRatio) := by
  have lowerBound := ExactLog.interpret_mono EntropyMeanHalf.certificate.lower_bound
  have interpreted := (le_congr (ExactLog.interpret_ofSignedRatio _)
    (equiv_symm EntropyMeanHalf.anchor.toReal_entropy)).mp lowerBound
  exact ⟨le_trans interpreted (problem.idealEntropyLaw_maximal EntropyMeanHalf.anchor _),
    EntropyMeanHalf.certificate.real_global_bound ConstructiveEntropyOptimizer.meanHalfIdeal⟩

/-- Every original response row is affine on the three ordered outcomes,
including both copies of the redundant constant constraint. -/
private theorem row_affine : ∀ r : Fin problem.analyticProblem.rows.length,
    SignedRatio.Equiv
      (SignedRatio.add (problem.analyticProblem.rows[r.val].coefficients i0) (problem.analyticProblem.rows[r.val].coefficients i2))
      (SignedRatio.add (problem.analyticProblem.rows[r.val].coefficients i1) (problem.analyticProblem.rows[r.val].coefficients i1)) := by
  decide +kernel

/-- The computed multipliers therefore give a geometric progression of
unnormalized weights, irrespective of their nonuniqueness on redundant rows. -/
theorem score_affine : Equiv (add (multipliers.score i0) (multipliers.score i2))
    (add (multipliers.score i1) (multipliers.score i1)) := by
  let count := problem.analyticProblem.rows.length
  let coefficients := fun (i : Fin problem.cells.length) (r : Fin count) => ofSignedRatio (problem.analyticProblem.rows[r.val].coefficients i)
  have evaluate (i : Fin problem.cells.length) : Equiv (multipliers.score i)
      (FiniteLinear.pair count (coefficients i) multipliers.coefficient) :=
    RationalLinear.realRationalDot_pair count _ multipliers.coefficient
  have combined (r : Fin count) : Equiv (add (coefficients i0 r) (coefficients i2 r))
      (add (coefficients i1 r) (coefficients i1 r)) :=
    equiv_trans (ofSignedRatio_add _ _) (equiv_trans ((ofSignedRatio_equiv_iff _ _).mpr (row_affine r))
      (equiv_symm (ofSignedRatio_add _ _)))
  exact equiv_trans (add_congr (evaluate i0) (evaluate i2))
    (equiv_trans (equiv_symm (FiniteLinear.pair_add_first count _ _ multipliers.coefficient))
      (equiv_trans (FiniteLinear.pair_congr count _ _ multipliers.coefficient multipliers.coefficient combined (fun _ => equiv_refl _))
        (equiv_trans (FiniteLinear.pair_add_first count _ _ multipliers.coefficient)
          (add_congr (equiv_symm (evaluate i1)) (equiv_symm (evaluate i1))))))

private abbrev Expression := RationalPolynomial.Expression 3
private def first : Expression := .coordinate 0
private def middle : Expression := .coordinate 1
private def last : Expression := .coordinate 2
private theorem common_product (a b c : ConstructiveReal) :
    Equiv (mul (mul a c) (mul b c)) (mul (mul a b) (mul c c)) :=
  RationalPolynomial.Expression.equalityCheck_sound_real
    (.mul (.mul first last) (.mul middle last)) (.mul (.mul first middle) (.mul last last))
    (by decide +kernel) (fun i => if i = 0 then a else if i = 1 then b else c)

/-- The attained mean-half optimum satisfies p0*p2=p1². This follows from
its proved multiplier form, rather than assuming a rational geometric law. -/
theorem geometric : Equiv (mul (ideal.mass i0).value (ideal.mass i2).value)
    (mul (ideal.mass i1).value (ideal.mass i1).value) := by
  have weights : Equiv (mul (neg (multipliers.score i0)).exp (neg (multipliers.score i2)).exp)
      (mul (neg (multipliers.score i1)).exp (neg (multipliers.score i1)).exp) :=
    equiv_trans (equiv_symm (exp_add _ _)) (equiv_trans (exp_congr (equiv_symm (neg_add _ _)))
      (equiv_trans (exp_congr (neg_congr score_affine)) (equiv_trans (exp_congr (neg_add _ _)) (exp_add _ _))))
  exact equiv_trans (mul_congr (gibbs i0) (gibbs i2))
    (equiv_trans (common_product _ _ _) (equiv_trans (mul_congr weights (equiv_refl _))
      (equiv_trans (equiv_symm (common_product _ _ _)) (equiv_symm (mul_congr (gibbs i1) (gibbs i1))))))

/-- The existing exactly feasible rational approximation sequence converges
to this same multiplier-described ideal, with its already proved effective
coordinate bound. The rational solver retains all original constraints. -/
theorem approximations_converge (radius : PositiveRatio) (n : Nat)
    (later : radius.half.half.entropyGapPrecision.den ≤ n) (i : Fin problem.cells.length) :
    Within radius.toQProb ((problem.entropyApproximations EntropyMeanHalf.anchor n).law.toReal.mass i).value
      (ideal.mass i).value :=
  problem.idealEntropyLaw_coordinate_converges EntropyMeanHalf.anchor radius n later i

example (row : Fin problem.analyticProblem.rows.length) (precision : PositiveRatio) :
    LE (ofSignedRatio ((multipliers.coefficient row).enclose precision).lower) (multipliers.coefficient row) ∧
      LE (multipliers.coefficient row) (ofSignedRatio ((multipliers.coefficient row).enclose precision).upper) :=
  (multipliers.coefficient row).enclosure_bounds precision

end Thesis.Examples.EntropyMeanHalfGibbs
