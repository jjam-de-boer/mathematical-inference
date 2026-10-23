import Thesis.Probability.ConstructiveRealAssociativity
import Thesis.Probability.ConstructiveRealAdditionLimits

namespace Thesis.Probability.RegularRationalApproximation

private theorem error_below (approximation : RegularRationalApproximation) (first second left right : PositiveRatio)
    (before : PositiveRatio.LE first left) (after : PositiveRatio.LE second right) :
    QProb.LE (SignedRatio.sub (approximation.value first) (approximation.value second)).magnitude
      (QProb.add left.toQProb right.toQProb) :=
  QProb.le_trans (approximation.error_bound first second) (QProb.add_le_add before after)

/-- Rational distributivity and a fixed cross-error bound identify the two
limit constructions, despite their different refinement schedules. -/
theorem product_add (a b c : RegularRationalApproximation) :
    ConstructiveReal.Equiv (a.product (b.add c)).limit ((a.product b).add (a.product c)).limit := by
  let factor := b.magnitudeBound + c.magnitudeBound + 2 * a.magnitudeBound
  apply limit_equiv_of_error_bound _ _ factor
  intro left right
  let before := productPrecision a (b.add c) left
  let afterB := productPrecision a b right.half
  let afterC := productPrecision a c right.half
  let error := QProb.add left.toQProb right.toQProb
  let sizeA := QProb.ofNat a.magnitudeBound
  let sizeB := QProb.ofNat b.magnitudeBound
  let sizeC := QProb.ofNat c.magnitudeBound
  have firstLeft := productPrecision_le a (b.add c) left
  have secondLeft : PositiveRatio.LE before.half left := PositiveRatio.le_trans before.half_le firstLeft
  have rightB : PositiveRatio.LE afterB right := PositiveRatio.le_trans (productPrecision_le a b right.half) right.half_le
  have rightC : PositiveRatio.LE afterC right := PositiveRatio.le_trans (productPrecision_le a c right.half) right.half_le
  have errorAB := error_below a before afterB left right firstLeft rightB
  have errorAC := error_below a before afterC left right firstLeft rightC
  have errorB := error_below b before.half afterB left right secondLeft rightB
  have errorC := error_below c before.half afterC left right secondLeft rightC
  have leftSmall : PositiveRatio.LE before.half PositiveRatio.one :=
    PositiveRatio.le_trans before.half_le (productPrecision_le_one a (b.add c) left)
  have firstProduct := SignedRatio.product_error_bound
    (a.value before) (b.value before.half) (a.value afterB) (b.value afterB)
    error error sizeA sizeB errorAB errorB
    (a.magnitude_bounded afterB (productPrecision_le_one a b right.half)) (b.magnitude_bounded _ leftSmall)
  have secondProduct := SignedRatio.product_error_bound
    (a.value before) (c.value before.half) (a.value afterC) (c.value afterC)
    error error sizeA sizeC errorAC errorC
    (a.magnitude_bounded afterC (productPrecision_le_one a c right.half)) (c.magnitude_bounded _ leftSmall)
  have sameDifference : SignedRatio.Equiv
      (SignedRatio.sub (SignedRatio.mul (a.value before) (SignedRatio.add (b.value before.half) (c.value before.half)))
        (SignedRatio.add (SignedRatio.mul (a.value afterB) (b.value afterB)) (SignedRatio.mul (a.value afterC) (c.value afterC))))
      (SignedRatio.add
        (SignedRatio.sub (SignedRatio.mul (a.value before) (b.value before.half)) (SignedRatio.mul (a.value afterB) (b.value afterB)))
        (SignedRatio.sub (SignedRatio.mul (a.value before) (c.value before.half)) (SignedRatio.mul (a.value afterC) (c.value afterC)))) :=
    SignedRatio.equiv_trans (SignedRatio.add_congr (SignedRatio.mul_add _ _ _) (SignedRatio.equiv_refl _))
      (SignedRatio.sub_add_sub _ _ _ _)
  have triangle := SignedRatio.magnitude_add
    (SignedRatio.sub (SignedRatio.mul (a.value before) (b.value before.half)) (SignedRatio.mul (a.value afterB) (b.value afterB)))
    (SignedRatio.sub (SignedRatio.mul (a.value before) (c.value before.half)) (SignedRatio.mul (a.value afterC) (c.value afterC)))
  have estimated := QProb.le_trans triangle (QProb.add_le_add firstProduct secondProduct)
  have regrouped : QProb.Equiv
      (QProb.add (QProb.add (QProb.mul error sizeB) (QProb.mul sizeA error))
        (QProb.add (QProb.mul error sizeC) (QProb.mul sizeA error)))
      (QProb.mul (QProb.ofNat factor) error) := by
    simp only [sizeA, sizeB, sizeC, factor, QProb.Equiv, QProb.add, QProb.mul, QProb.ofNat,
      Nat.mul_one, Nat.one_mul, Nat.two_mul, Nat.add_mul]
    ac_rfl
  exact QProb.le_congr (QProb.equiv_symm (SignedRatio.magnitude_congr sameDifference)) regrouped estimated

end Thesis.Probability.RegularRationalApproximation

namespace Thesis.Probability.ConstructiveReal

/-- General real multiplication distributes over real addition. -/
theorem mul_add (x y z : ConstructiveReal) : Equiv (mul x (add y z)) (add (mul x y) (mul x z)) := by
  let a := x.rationalApproximation
  let b := y.rationalApproximation
  let c := z.rationalApproximation
  have sumSame : Equiv (add y z) (b.add c).limit := equiv_symm
    (equiv_trans (RegularRationalApproximation.add_limit b c)
      (add_congr (rationalApproximation_limit y) (rationalApproximation_limit z)))
  have raw : Equiv (mul x (add y z)) (a.product (b.add c)).limit :=
    RegularRationalApproximation.product_congr _ _ _ _ (equiv_refl _)
      (equiv_trans (rationalApproximation_limit (add y z)) sumSame)
  exact equiv_trans raw (equiv_trans (RegularRationalApproximation.product_add a b c)
    (RegularRationalApproximation.add_limit (a.product b) (a.product c)))

theorem add_mul (x y z : ConstructiveReal) : Equiv (mul (add x y) z) (add (mul x z) (mul y z)) :=
  equiv_trans (mul_comm _ _) (equiv_trans (mul_add z x y) (add_congr (mul_comm _ _) (mul_comm _ _)))

end Thesis.Probability.ConstructiveReal
