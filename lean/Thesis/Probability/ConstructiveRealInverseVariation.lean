import Thesis.Probability.ConstructiveRealReciprocal
import Thesis.Probability.ConstructiveRealPolynomialExpression

namespace Thesis.Probability.ConstructiveReal

/-- Exact reciprocal difference on explicitly positive real domains. The
lower-bound witnesses may differ; multiplication by each computed inverse
is justified by its proved inverse equation. -/
theorem positiveInverse_difference (x y : ConstructiveReal) (lowerX lowerY : PositiveRatio)
    (boundedX : LE (ofSignedRatio lowerX.toSignedRatio) x) (boundedY : LE (ofSignedRatio lowerY.toSignedRatio) y) :
    Equiv (sub (x.positiveInverse lowerX boundedX) (y.positiveInverse lowerY boundedY))
      (mul (sub y x) (mul (x.positiveInverse lowerX boundedX) (y.positiveInverse lowerY boundedY))) := by
  let ix := x.positiveInverse lowerX boundedX
  let iy := y.positiveInverse lowerY boundedY
  have left : Equiv (mul y (mul ix iy)) ix :=
    equiv_trans (mul_comm _ _) (equiv_trans (mul_assoc _ _ _)
      (equiv_trans (mul_congr (equiv_refl _) (equiv_trans (mul_comm _ _) (mul_positiveInverse y lowerY boundedY))) (mul_one _)))
  have right : Equiv (mul x (mul ix iy)) iy :=
    equiv_trans (equiv_symm (mul_assoc _ _ _))
      (equiv_trans (mul_congr (mul_positiveInverse x lowerX boundedX) (equiv_refl _)) (one_mul _))
  exact equiv_symm (equiv_trans (sub_mul _ _ _) (add_congr left (neg_congr right)))

private abbrev Expr := RationalPolynomial.Expression 3
private def aVar : Expr := .coordinate 0
private def bVar : Expr := .coordinate 1
private def hVar : Expr := .coordinate 2
private def aSquare : Expr := .mul aVar aVar
private def linearVar : Expr := .add aVar (.mul hVar (.sub (.constant SignedRatio.zero) aSquare))
private def errorVar : Expr := .mul (.mul hVar hVar) (.mul aSquare bVar)
private def residualVar : Expr :=
  .mul (.sub (.mul hVar (.mul aVar bVar)) (.sub aVar bVar)) (.sub (.constant SignedRatio.one) (.mul hVar aVar))
private def taylorRight : Expr := .add (.add linearVar errorVar) residualVar

private theorem inverse_taylor_identity (a b h : ConstructiveReal)
    (difference : Equiv (mul h (mul a b)) (sub a b)) :
    Equiv b (add (add a (mul h (neg (mul a a)))) (mul (mul h h) (mul (mul a a) b))) := by
  have identity := RationalPolynomial.Expression.equalityCheck_sound_real bVar taylorRight (by decide +kernel)
    (fun index => match index.val with | 0 => a | 1 => b | _ => h)
  have vanished : Equiv (mul (sub (mul h (mul a b)) (sub a b)) (sub one (mul h a))) zero :=
    equiv_trans (mul_congr ((sub_equiv_zero_iff _ _).mpr difference) (equiv_refl _)) (zero_mul _)
  have negative : Equiv (sub zero (mul a a)) (neg (mul a a)) := zero_add _
  exact equiv_trans identity (equiv_trans
    (add_congr (add_congr (add_congr (equiv_refl _) (mul_congr (equiv_refl _) negative)) (equiv_refl _)) vanished)
    (add_zero _))

/-- Reciprocal linear approximation, with its negative square slope. -/
def inverseLinear (x y : ConstructiveReal) (lower : PositiveRatio)
    (boundedX : LE (ofSignedRatio lower.toSignedRatio) x) : ConstructiveReal :=
  let ix := x.positiveInverse lower boundedX
  add ix (mul (sub y x) (neg (mul ix ix)))

/-- Exact quadratic reciprocal remainder on a positive half-line. -/
def inverseQuadraticError (x y : ConstructiveReal) (lower : PositiveRatio)
    (boundedX : LE (ofSignedRatio lower.toSignedRatio) x) (boundedY : LE (ofSignedRatio lower.toSignedRatio) y) : ConstructiveReal :=
  let ix := x.positiveInverse lower boundedX
  let iy := y.positiveInverse lower boundedY
  mul (mul (sub y x) (sub y x)) (mul (mul ix ix) iy)

/-- The reciprocal has an exact quadratic first-order remainder. It follows
from inverse algebra, with neither a derivative nor a zero/sign decision on
the real increment assumed. -/
theorem positiveInverse_first_variation_identity (x y : ConstructiveReal) (lower : PositiveRatio)
    (boundedX : LE (ofSignedRatio lower.toSignedRatio) x) (boundedY : LE (ofSignedRatio lower.toSignedRatio) y) :
    Equiv (y.positiveInverse lower boundedY)
      (add (inverseLinear x y lower boundedX) (inverseQuadraticError x y lower boundedX boundedY)) :=
  inverse_taylor_identity _ _ _ (equiv_symm (positiveInverse_difference x y lower lower boundedX boundedY))

end Thesis.Probability.ConstructiveReal
