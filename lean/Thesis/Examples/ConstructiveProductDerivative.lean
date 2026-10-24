import Thesis.Probability.ConstructiveDerivativeProduct
import Thesis.Probability.ConstructiveDerivativeUniqueness
import Thesis.Probability.ConstructiveRealExpDerivative

namespace Thesis.Examples.ConstructiveProductDerivative
open Probability ConstructiveReal

private def x : RationalPolynomial.Expression 2 := .coordinate 0
private def y : RationalPolynomial.Expression 2 := .coordinate 1
private def left : RationalPolynomial.Expression 2 := .mul (.add x y) (.sub x y)
private def right : RationalPolynomial.Expression 2 := .sub (.mul x x) (.mul y y)

/-- The accepted identity applies to arbitrary analytic real values, rather
than a finite collection of numerical test assignments. -/
example (values : Fin 2 → ConstructiveReal) : Equiv (left.evaluateReal values) (right.evaluateReal values) :=
  RationalPolynomial.Expression.equalityCheck_sound_real left right (by decide +kernel) values
example : RationalPolynomial.Expression.equalityCheck left (.add (.mul x x) (.mul y y)) = false := by decide +kernel

private def unreduced : RationalPolynomial.Expression 0 := .constant ⟨2, 4, by decide⟩
private def reduced : RationalPolynomial.Expression 0 := .constant ⟨1, 2, by decide⟩
example (values : Fin 0 → ConstructiveReal) : Equiv (unreduced.evaluateReal values) (reduced.evaluateReal values) :=
  RationalPolynomial.Expression.equalityCheck_sound_real unreduced reduced (by decide +kernel) values

example (point : ConstructiveReal) : HasDerivativeAt (fun y => mul y y) point (add point point) := square_hasDerivativeAt point

example (f g : ConstructiveReal → ConstructiveReal) (point sf sg : ConstructiveReal)
    (first : HasDerivativeAt f point sf) (second : HasDerivativeAt g point sg) :
    HasDerivativeAt (fun y => mul (f y) (g y)) point (add (mul sf (g point)) (mul (f point) sg)) := first.mul second

/-- Product differentiation agrees with the independently proved exact
quadratic square remainder. -/
example (point : ConstructiveReal) : Equiv (add (mul one point) (mul point one)) (add point point) :=
  ((HasDerivativeAt.identity point).mul (HasDerivativeAt.identity point)).unique (square_hasDerivativeAt point)

/-- Composition with the constructed exponential uses the expected Leibniz
formula; no exponential addition law is assumed. -/
example (point : ConstructiveReal) : HasDerivativeAt (fun y => mul y y.exp) point (add point.exp (mul point point.exp)) :=
  ((HasDerivativeAt.identity point).mul (exp_hasDerivativeAt point)).slope_congr
    (add_congr (one_mul _) (equiv_refl _))

example (point : ConstructiveReal) : HasDerivativeAt (fun y => mul y zero) point zero :=
  ((HasDerivativeAt.identity point).mul (HasDerivativeAt.constant point zero)).slope_congr
    (equiv_trans (add_congr (mul_zero _) (mul_zero _)) (zero_add zero))

example (point : ConstructiveReal) : HasDerivativeAt (fun y => mul (neg y) y) point (add (neg point) (neg point)) :=
  ((HasDerivativeAt.identity point).neg.mul (HasDerivativeAt.identity point)).slope_congr
    (add_congr (equiv_trans (neg_mul one point) (neg_congr (one_mul point))) (mul_one _))

end Thesis.Examples.ConstructiveProductDerivative
