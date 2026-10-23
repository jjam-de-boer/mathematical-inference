import Thesis.Probability.RegularRationalAlgebra

namespace Thesis.Probability.ConstructiveReal

/-- Multiplication is constructed from a regular net of rational products,
with precision scaled by proved bounds on both inputs. -/
def mul (x y : ConstructiveReal) : ConstructiveReal :=
  (x.rationalApproximation.product y.rationalApproximation).limit

theorem mul_comm (x y : ConstructiveReal) : Equiv (mul x y) (mul y x) :=
  RegularRationalApproximation.product_comm x.rationalApproximation y.rationalApproximation

theorem mul_congr {x x' y y' : ConstructiveReal} (first : Equiv x x') (second : Equiv y y') :
    Equiv (mul x y) (mul x' y') := by
  have alignedFirst := equiv_trans (rationalApproximation_limit x)
    (equiv_trans first (equiv_symm (rationalApproximation_limit x')))
  have alignedSecond := equiv_trans (rationalApproximation_limit y)
    (equiv_trans second (equiv_symm (rationalApproximation_limit y')))
  exact RegularRationalApproximation.product_congr _ _ _ _ alignedFirst alignedSecond

theorem mul_zero (x : ConstructiveReal) : Equiv (mul x zero) zero := by
  have compared : Equiv (mul x zero) zero.rationalApproximation.limit := by
    apply RegularRationalApproximation.limit_congr
    intro precision
    exact SignedRatio.mul_zero _
  exact equiv_trans compared (rationalApproximation_limit zero)

theorem zero_mul (x : ConstructiveReal) : Equiv (mul zero x) zero := equiv_trans (mul_comm _ _) (mul_zero x)

theorem mul_one (x : ConstructiveReal) : Equiv (mul x one) x := by
  have compared : Equiv (mul x one) x.rationalApproximation.limit := by
    apply RegularRationalApproximation.limit_equiv_of_error_bound _ _ 1
    intro left right
    let precision := RegularRationalApproximation.productPrecision x.rationalApproximation one.rationalApproximation left
    have bounded := QProb.le_trans (x.rationalApproximation.error_bound precision right)
      (QProb.add_le_add (RegularRationalApproximation.productPrecision_le _ _ left) (QProb.le_refl right.toQProb))
    have same : SignedRatio.Equiv
        (SignedRatio.sub (SignedRatio.mul (x.rationalApproximation.value precision) SignedRatio.one) (x.rationalApproximation.value right))
        (SignedRatio.sub (x.rationalApproximation.value precision) (x.rationalApproximation.value right)) :=
      SignedRatio.add_congr (SignedRatio.mul_one _) (SignedRatio.equiv_refl _)
    exact QProb.le_congr (QProb.equiv_symm (SignedRatio.magnitude_congr same))
      (QProb.equiv_symm (QProb.one_mul _)) bounded
  exact equiv_trans compared (rationalApproximation_limit x)

theorem one_mul (x : ConstructiveReal) : Equiv (mul one x) x := equiv_trans (mul_comm _ _) (mul_one x)

/-- The constructed real product agrees with exact signed rational arithmetic. -/
theorem ofSignedRatio_mul (a b : SignedRatio) :
    Equiv (mul (ofSignedRatio a) (ofSignedRatio b)) (ofSignedRatio (SignedRatio.mul a b)) := by
  apply RegularRationalApproximation.limit_unique
  intro precision
  constructor
  · apply (ofSignedRatio_le_iff _ _).mpr
    change SignedRatio.LE (SignedRatio.sub (SignedRatio.mul a b) precision.toSignedRatio) (SignedRatio.mul a b)
    exact (SignedRatio.sub_le_iff_le_add _ _ _).mpr
      (SignedRatio.le_add_of_nonnegative _ _ precision.signed_nonnegative)
  · apply (ofSignedRatio_le_iff _ _).mpr
    exact SignedRatio.le_add_of_nonnegative _ _ precision.signed_nonnegative

/-- Every requested rational product approximant has a proved enclosure of
the constructed real product. This includes products of two general inputs. -/
theorem mul_approximation_bounds (x y : ConstructiveReal) (precision : PositiveRatio) :
    let approximation := x.rationalApproximation.product y.rationalApproximation
    LE (ofSignedRatio (SignedRatio.sub (approximation.value precision) precision.toSignedRatio)) (mul x y) ∧
    LE (mul x y) (ofSignedRatio (SignedRatio.add (approximation.value precision) precision.toSignedRatio)) :=
  (x.rationalApproximation.product y.rationalApproximation).approximation_bounds precision

end Thesis.Probability.ConstructiveReal
