import Thesis.Probability.ConstructiveRealInverseVariation
import Thesis.Probability.ConstructiveRealSquareBounds
import Thesis.Probability.ConstructiveRealDistanceAlgebra

namespace Thesis.Probability.ConstructiveReal

/-- Computable reciprocal Taylor error on a positive half-line. -/
def inverseRadiusError (lower radius : PositiveRatio) : QProb :=
  QProb.mul (QProb.mul radius.toQProb radius.toQProb) (QProb.ofNat (lower.den ^ 3))

private theorem rational_product (a b : QProb) :
    Equiv (mul (ofSignedRatio a.toSignedRatio) (ofSignedRatio b.toSignedRatio)) (ofSignedRatio (QProb.mul a b).toSignedRatio) := by
  rw [QProb.toSignedRatio_mul]
  exact ofSignedRatio_mul _ _

private theorem inverse_kernel_bound (x y : ConstructiveReal) (lower : PositiveRatio)
    (boundedX : LE (ofSignedRatio lower.toSignedRatio) x) (boundedY : LE (ofSignedRatio lower.toSignedRatio) y) :
    LE (mul (mul (x.positiveInverse lower boundedX) (x.positiveInverse lower boundedX)) (y.positiveInverse lower boundedY))
      (ofSignedRatio (QProb.ofNat (lower.den ^ 3)).toSignedRatio) := by
  let ix := x.positiveInverse lower boundedX
  let iy := y.positiveInverse lower boundedY
  let n := QProb.ofNat lower.den
  let nr := ofSignedRatio n.toSignedRatio
  have positiveN : LE zero nr :=
    (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr (QProb.zero_le n))
  have squared := square_le_square (x.positiveInverse_nonnegative lower boundedX) (x.positiveInverse_upper lower boundedX)
  have multiplied := mul_le_mul squared (y.positiveInverse_upper lower boundedY) (square_nonnegative ix) positiveN
  have natural : QProb.Equiv (QProb.mul (QProb.mul n n) n) (QProb.ofNat (lower.den ^ 3)) := by
    simp only [n, QProb.Equiv, QProb.mul, QProb.ofNat, Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_one]
  have collected : Equiv (mul (mul nr nr) nr) (ofSignedRatio (QProb.ofNat (lower.den ^ 3)).toSignedRatio) :=
    equiv_trans (mul_congr (rational_product n n) (equiv_refl nr))
      (equiv_trans (rational_product (QProb.mul n n) n) ((ofSignedRatio_equiv_iff _ _).mpr (QProb.toSignedRatio_congr natural)))
  exact (le_congr (equiv_refl _) collected).mp multiplied

theorem inverseQuadraticError_nonnegative (x y : ConstructiveReal) (lower : PositiveRatio)
    (boundedX : LE (ofSignedRatio lower.toSignedRatio) x) (boundedY : LE (ofSignedRatio lower.toSignedRatio) y) :
    LE zero (inverseQuadraticError x y lower boundedX boundedY) :=
  mul_nonnegative (square_nonnegative _) (mul_nonnegative (square_nonnegative _) (y.positiveInverse_nonnegative lower boundedY))

/-- The exact reciprocal remainder is at most `radius² * lower.den³`.
The estimate includes zero increments and uses no arbitrary real sign test. -/
theorem inverseQuadraticError_bound (x y : ConstructiveReal) (lower radius : PositiveRatio)
    (boundedX : LE (ofSignedRatio lower.toSignedRatio) x) (boundedY : LE (ofSignedRatio lower.toSignedRatio) y)
    (close : Within radius.toQProb x y) :
    LE (inverseQuadraticError x y lower boundedX boundedY) (ofSignedRatio (inverseRadiusError lower radius).toSignedRatio) := by
  have positive : LE zero (ofSignedRatio (QProb.ofNat (lower.den ^ 3)).toSignedRatio) :=
    (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr (QProb.zero_le _))
  have compared := mul_le_mul (within_square close) (inverse_kernel_bound x y lower boundedX boundedY)
    (square_nonnegative _) positive
  exact (le_congr (equiv_refl _) (rational_product (QProb.mul radius.toQProb radius.toQProb) (QProb.ofNat (lower.den ^ 3)))).mp compared

/-- Quantitative reciprocal first variation on its explicit positive domain.
This supplies a real derivative estimate with a rational, computed error. -/
theorem positiveInverse_first_variation (x y : ConstructiveReal) (lower radius : PositiveRatio)
    (boundedX : LE (ofSignedRatio lower.toSignedRatio) x) (boundedY : LE (ofSignedRatio lower.toSignedRatio) y)
    (close : Within radius.toQProb x y) :
    Within (inverseRadiusError lower radius) (y.positiveInverse lower boundedY) (inverseLinear x y lower boundedX) := by
  let error := inverseRadiusError lower radius
  let remainder := inverseQuadraticError x y lower boundedX boundedY
  have positive := inverseQuadraticError_nonnegative x y lower boundedX boundedY
  have bounded := inverseQuadraticError_bound x y lower radius boundedX boundedY close
  have errorPositive : LE zero (ofSignedRatio error.toSignedRatio) :=
    (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr (QProb.zero_le error))
  have near : Within error remainder zero :=
    ⟨(le_congr (equiv_refl _) (zero_add _)).mpr bounded,
      (le_congr (zero_add zero) (equiv_refl _)).mp (add_le_add positive errorPositive)⟩
  have translated := (within_add_left_iff error (inverseLinear x y lower boundedX) _ _).mpr near
  exact (within_congr (equiv_symm (positiveInverse_first_variation_identity x y lower boundedX boundedY)) (add_zero _)).mp translated

end Thesis.Probability.ConstructiveReal
