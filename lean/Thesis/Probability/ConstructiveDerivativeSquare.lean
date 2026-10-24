import Thesis.Probability.ConstructiveDerivative
import Thesis.Probability.ConstructiveRealSquareBounds
import Thesis.Probability.ConstructiveRealDistanceAlgebra
import Thesis.Probability.ConstructiveRealPolynomialExpression

namespace Thesis.Probability.ConstructiveReal

private abbrev Expr := RationalPolynomial.Expression 2
private def pointVar : Expr := .coordinate 0
private def nearbyVar : Expr := .coordinate 1
private def incrementVar : Expr := .sub nearbyVar pointVar
private def squareLeft : Expr := .mul nearbyVar nearbyVar
private def squareRight : Expr :=
  .add (.add (.mul pointVar pointVar) (.mul incrementVar (.add pointVar pointVar))) (.mul incrementVar incrementVar)

private theorem square_linear_identity (point nearby : ConstructiveReal) :
    Equiv (mul nearby nearby)
      (add (add (mul point point) (mul (sub nearby point) (add point point))) (mul (sub nearby point) (sub nearby point))) :=
  RationalPolynomial.Expression.equalityCheck_sound_real squareLeft squareRight (by decide +kernel)
    (fun index => if index.val = 0 then point else nearby)

private theorem within_zero_of_nonnegative {error : QProb} {value : ConstructiveReal}
    (positive : LE zero value) (bounded : LE value (ofSignedRatio error.toSignedRatio)) : Within error value zero := by
  have errorPositive : LE zero (ofSignedRatio error.toSignedRatio) :=
    (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr (QProb.zero_le error))
  exact ⟨(le_congr (equiv_refl _) (zero_add _)).mpr bounded,
    (le_congr (zero_add zero) (equiv_refl _)).mp (add_le_add positive errorPositive)⟩

/-- Squaring has an exact quadratic remainder, controlled by the square of
any supplied rational distance radius. No real sign is decided. -/
theorem square_first_variation (point nearby : ConstructiveReal) (radius : PositiveRatio)
    (close : Within radius.toQProb point nearby) :
    Within (QProb.mul radius.toQProb radius.toQProb) (mul nearby nearby)
      (add (mul point point) (mul (sub nearby point) (add point point))) := by
  have increment := within_zero_of_nonnegative (square_nonnegative (sub nearby point)) (within_square close)
  have translated := (within_add_left_iff _ (add (mul point point) (mul (sub nearby point) (add point point))) _ _).mpr increment
  exact (within_congr (equiv_symm (square_linear_identity point nearby)) (add_zero _)).mp translated

/-- The square derivative is `point + point`, with the input tolerance itself
serving as a modulus for the exact quadratic remainder. -/
def square_hasDerivativeAt (point : ConstructiveReal) : HasDerivativeAt (fun y => mul y y) point (add point point) where
  modulus epsilon := epsilon
  remainder epsilon radius small nearby close :=
    within_mono (square_first_variation point nearby radius close) (QProb.mul_le_mul small (QProb.le_refl _))

end Thesis.Probability.ConstructiveReal
