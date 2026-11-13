import Thesis.Probability.ConstructiveRealMultiplication

namespace Thesis.Probability.RegularRationalApproximation

private theorem error_below (approximation : RegularRationalApproximation) (first second left right : PositiveRatio)
    (before : PositiveRatio.LE first left) (after : PositiveRatio.LE second right) :
    QProb.LE (SignedRatio.sub (approximation.value first) (approximation.value second)).magnitude
      (QProb.add left.toQProb right.toQProb) :=
  QProb.le_trans (approximation.error_bound first second) (QProb.add_le_add before after)

/-- Different nesting schedules for three regular rational factors converge
to the same value. The proof supplies a fixed explicit cross-error bound. -/
theorem product_assoc (a b c : RegularRationalApproximation) :
    ConstructiveReal.Equiv ((a.product b).product c).limit (a.product (b.product c)).limit := by
  let factor := (a.magnitudeBound + b.magnitudeBound) * c.magnitudeBound + a.magnitudeBound * b.magnitudeBound
  apply limit_equiv_of_error_bound _ _ factor
  intro left right
  let outerLeft := productPrecision (a.product b) c left
  let innerLeft := productPrecision a b outerLeft
  let outerRight := productPrecision a (b.product c) right
  let innerRight := productPrecision b c outerRight
  let error := QProb.add left.toQProb right.toQProb
  let sizeA := QProb.ofNat a.magnitudeBound
  let sizeB := QProb.ofNat b.magnitudeBound
  let sizeC := QProb.ofNat c.magnitudeBound
  have firstLeft : PositiveRatio.LE innerLeft left :=
    PositiveRatio.le_trans (productPrecision_le a b outerLeft) (productPrecision_le (a.product b) c left)
  have secondRight : PositiveRatio.LE innerRight right :=
    PositiveRatio.le_trans (productPrecision_le b c outerRight) (productPrecision_le a (b.product c) right)
  have errorA := error_below a innerLeft outerRight left right firstLeft (productPrecision_le a (b.product c) right)
  have errorB := error_below b innerLeft innerRight left right firstLeft secondRight
  have errorC := error_below c outerLeft innerRight left right (productPrecision_le (a.product b) c left) secondRight
  have boundBLeft := b.magnitude_bounded innerLeft (productPrecision_le_one a b outerLeft)
  have boundARight := a.magnitude_bounded outerRight (productPrecision_le_one a (b.product c) right)
  have boundBRight := b.magnitude_bounded innerRight (productPrecision_le_one b c outerRight)
  have boundCLeft := c.magnitude_bounded outerLeft (productPrecision_le_one (a.product b) c left)
  let innerError := QProb.add (QProb.mul error sizeB) (QProb.mul sizeA error)
  have inner := SignedRatio.product_error_bound
    (a.value innerLeft) (b.value innerLeft) (a.value outerRight) (b.value innerRight)
    error error sizeA sizeB errorA errorB boundARight boundBLeft
  have sizeAB : QProb.LE (SignedRatio.mul (a.value outerRight) (b.value innerRight)).magnitude (QProb.mul sizeA sizeB) :=
    QProb.le_congr (QProb.equiv_symm (SignedRatio.magnitude_mul _ _)) (QProb.equiv_refl _)
      (QProb.mul_le_mul boundARight boundBRight)
  have outer := SignedRatio.product_error_bound
    (SignedRatio.mul (a.value innerLeft) (b.value innerLeft)) (c.value outerLeft)
    (SignedRatio.mul (a.value outerRight) (b.value innerRight)) (c.value innerRight)
    innerError error (QProb.mul sizeA sizeB) sizeC inner errorC sizeAB boundCLeft
  have regrouped : QProb.Equiv
      (QProb.add (QProb.mul innerError sizeC) (QProb.mul (QProb.mul sizeA sizeB) error))
      (QProb.mul (QProb.ofNat factor) error) := by
    simp only [innerError, sizeA, sizeB, sizeC, factor, QProb.Equiv, QProb.add, QProb.mul, QProb.ofNat,
      Nat.mul_one, Nat.one_mul, Nat.add_mul]
    ac_rfl
  have sameDifference : SignedRatio.Equiv
      (SignedRatio.sub
        (SignedRatio.mul (SignedRatio.mul (a.value innerLeft) (b.value innerLeft)) (c.value outerLeft))
        (SignedRatio.mul (a.value outerRight) (SignedRatio.mul (b.value innerRight) (c.value innerRight))))
      (SignedRatio.sub
        (SignedRatio.mul (SignedRatio.mul (a.value innerLeft) (b.value innerLeft)) (c.value outerLeft))
        (SignedRatio.mul (SignedRatio.mul (a.value outerRight) (b.value innerRight)) (c.value innerRight))) :=
    SignedRatio.add_congr (SignedRatio.equiv_refl _)
      (SignedRatio.neg_congr (SignedRatio.equiv_symm (SignedRatio.mul_assoc _ _ _)))
  exact QProb.le_congr (QProb.equiv_symm (SignedRatio.magnitude_congr sameDifference)) regrouped outer

end Thesis.Probability.RegularRationalApproximation

namespace Thesis.Probability.ConstructiveReal

/-- Multiplication is associative on arbitrary coherent real presentations. -/
theorem mul_assoc (x y z : ConstructiveReal) : Equiv (mul (mul x y) z) (mul x (mul y z)) := by
  have left : Equiv (mul (mul x y) z)
      (((x.rationalApproximation.product y.rationalApproximation).product z.rationalApproximation).limit) :=
    RegularRationalApproximation.product_congr _ _ _ _ (rationalApproximation_limit (mul x y)) (equiv_refl _)
  have right : Equiv (x.rationalApproximation.product (y.rationalApproximation.product z.rationalApproximation)).limit
      (mul x (mul y z)) :=
    RegularRationalApproximation.product_congr _ _ _ _ (equiv_refl _) (equiv_symm (rationalApproximation_limit (mul y z)))
  exact equiv_trans left (equiv_trans (RegularRationalApproximation.product_assoc _ _ _) right)

end Thesis.Probability.ConstructiveReal
