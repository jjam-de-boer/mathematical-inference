import Thesis.Probability.ConstructiveRealLimits
import Thesis.Probability.ConstructiveRealDistance

namespace Thesis.Probability.RegularRationalApproximation

theorem error_bound (approximation : RegularRationalApproximation) (first second : PositiveRatio) :
    QProb.LE (SignedRatio.sub (approximation.value first) (approximation.value second)).magnitude
      (QProb.add first.toQProb second.toQProb) := by
  apply (SignedRatio.magnitude_sub_le_iff _ _ _).mpr
  rw [QProb.toSignedRatio_add]
  constructor
  · exact approximation.regular first second
  · exact (SignedRatio.le_congr (SignedRatio.equiv_refl _)
      (SignedRatio.add_congr (SignedRatio.equiv_refl _) (SignedRatio.add_comm _ _))).mp
      (approximation.regular second first)

/-- A computed integer bound on all approximants requested at precision ≤ 1. -/
def magnitudeBound (approximation : RegularRationalApproximation) : Nat := (approximation.value PositiveRatio.one).num.natAbs + 2

theorem magnitude_bounded (approximation : RegularRationalApproximation) (precision : PositiveRatio)
    (small : PositiveRatio.LE precision PositiveRatio.one) :
    QProb.LE (approximation.value precision).magnitude (QProb.ofNat approximation.magnitudeBound) := by
  let center := approximation.value PositiveRatio.one
  have centerBound : QProb.LE center.magnitude (QProb.ofNat center.num.natAbs) := by
    simpa only [QProb.LE, SignedRatio.magnitude, QProb.ofNat, Nat.mul_one] using
      (Nat.le_mul_of_pos_right center.num.natAbs center.den_pos)
  have errors : QProb.LE (QProb.add precision.toQProb PositiveRatio.one.toQProb) (QProb.ofNat 2) :=
    QProb.add_le_add small (QProb.le_refl QProb.one)
  have error := QProb.le_trans (approximation.error_bound precision PositiveRatio.one) errors
  have triangle := QProb.le_congr
    (SignedRatio.magnitude_congr (SignedRatio.sub_add_cancel (approximation.value precision) center)) (QProb.equiv_refl _)
    (SignedRatio.magnitude_add (SignedRatio.sub (approximation.value precision) center) center)
  have bounded := QProb.le_trans triangle (QProb.add_le_add error centerBound)
  have reordered : QProb.Equiv (QProb.add (QProb.ofNat 2) (QProb.ofNat center.num.natAbs))
      (QProb.ofNat approximation.magnitudeBound) := by
    simp only [QProb.Equiv, QProb.add, QProb.ofNat, Nat.mul_one, magnitudeBound, center]
    omega
  exact QProb.le_congr (QProb.equiv_refl _) reordered bounded

def productPrecision (first second : RegularRationalApproximation) (precision : PositiveRatio) : PositiveRatio :=
  (precision.divideNat (first.magnitudeBound + second.magnitudeBound) (by dsimp [magnitudeBound]; omega)).capOne

theorem productPrecision_le (first second : RegularRationalApproximation) (precision : PositiveRatio) :
    PositiveRatio.LE (productPrecision first second precision) precision := by
  unfold productPrecision
  exact PositiveRatio.le_trans (PositiveRatio.capOne_le _) (PositiveRatio.divideNat_le _ _ _)

theorem productPrecision_le_one (first second : RegularRationalApproximation) (precision : PositiveRatio) :
    PositiveRatio.LE (productPrecision first second precision) PositiveRatio.one := PositiveRatio.capOne_le_one _

theorem productPrecision_comm (first second : RegularRationalApproximation) (precision : PositiveRatio) :
    productPrecision first second precision = productPrecision second first precision := by
  apply congrArg PositiveRatio.capOne
  apply PositiveRatio.ext
  · rfl
  · change precision.den * (first.magnitudeBound + second.magnitudeBound) =
      precision.den * (second.magnitudeBound + first.magnitudeBound)
    rw [Nat.add_comm first.magnitudeBound second.magnitudeBound]

/-- A regular product net is computed entirely in rational arithmetic.
Its input precision is scaled by proved magnitude bounds and capped at one. -/
def product (first second : RegularRationalApproximation) : RegularRationalApproximation := by
  let factor := first.magnitudeBound + second.magnitudeBound
  have positive : 0 < factor := by dsimp [factor, magnitudeBound]; omega
  let argument := productPrecision first second
  refine ⟨fun precision => SignedRatio.mul (first.value (argument precision)) (second.value (argument precision)), ?_⟩
  intro left right
  let error := QProb.add (argument left).toQProb (argument right).toQProb
  have estimated := SignedRatio.product_error_bound
    (first.value (argument left)) (second.value (argument left))
    (first.value (argument right)) (second.value (argument right))
    error error (QProb.ofNat first.magnitudeBound) (QProb.ofNat second.magnitudeBound)
    (first.error_bound _ _) (second.error_bound _ _)
    (first.magnitude_bounded _ (PositiveRatio.capOne_le_one _))
    (second.magnitude_bounded _ (PositiveRatio.capOne_le_one _))
  have regrouped : QProb.Equiv
      (QProb.add (QProb.mul error (QProb.ofNat second.magnitudeBound)) (QProb.mul (QProb.ofNat first.magnitudeBound) error))
      (QProb.add (QProb.mul (argument left).toQProb (QProb.ofNat factor))
        (QProb.mul (argument right).toQProb (QProb.ofNat factor))) := by
    simp only [error, factor, QProb.Equiv, QProb.mul, QProb.add, QProb.ofNat,
      Nat.mul_one, Nat.one_mul, Nat.mul_add, Nat.add_mul]
    ac_rfl
  have scaled := QProb.add_le_add (PositiveRatio.capped_divide_mul left factor positive)
    (PositiveRatio.capped_divide_mul right factor positive)
  have bounded := QProb.le_trans (QProb.le_congr (QProb.equiv_refl _) regrouped estimated) scaled
  have signed := ((SignedRatio.magnitude_sub_le_iff _ _ _).mp bounded).1
  simpa only [QProb.toSignedRatio_add] using signed

/-- Pointwise equivalent rational algorithms have the same limit value. -/
theorem limit_congr (first second : RegularRationalApproximation)
    (same : ∀ precision, SignedRatio.Equiv (first.value precision) (second.value precision)) :
    ConstructiveReal.Equiv first.limit second.limit := by
  apply first.limit_unique second.limit
  intro precision
  have lower := ConstructiveReal.ofSignedRatio_equiv_iff _ _ |>.mpr
    (SignedRatio.add_congr (same precision) (SignedRatio.equiv_refl (SignedRatio.neg precision.toSignedRatio)))
  have upper := ConstructiveReal.ofSignedRatio_equiv_iff _ _ |>.mpr
    (SignedRatio.add_congr (same precision) (SignedRatio.equiv_refl precision.toSignedRatio))
  have bounds := second.approximation_bounds precision
  exact ⟨(ConstructiveReal.le_congr lower (ConstructiveReal.equiv_refl _)).mpr bounds.1,
    (ConstructiveReal.le_congr (ConstructiveReal.equiv_refl _) upper).mpr bounds.2⟩

theorem product_comm (first second : RegularRationalApproximation) :
    ConstructiveReal.Equiv (first.product second).limit (second.product first).limit := by
  apply limit_congr
  intro precision
  change SignedRatio.Equiv
    (SignedRatio.mul (first.value (productPrecision first second precision)) (second.value (productPrecision first second precision)))
    (SignedRatio.mul (second.value (productPrecision second first precision)) (first.value (productPrecision second first precision)))
  rw [productPrecision_comm first second precision]
  exact SignedRatio.mul_comm _ _

/-- The product limit depends only on the input values, even when different
presentations compute different bounds and use different precisions. -/
theorem product_congr (first second first' second' : RegularRationalApproximation)
    (sameFirst : ConstructiveReal.Equiv first.limit first'.limit)
    (sameSecond : ConstructiveReal.Equiv second.limit second'.limit) :
    ConstructiveReal.Equiv (first.product second).limit (first'.product second').limit := by
  apply limit_equiv_of_error_bound _ _ (first'.magnitudeBound + second.magnitudeBound)
  intro left right
  let before := productPrecision first second left
  let after := productPrecision first' second' right
  let error := QProb.add left.toQProb right.toQProb
  have precisions : QProb.LE (QProb.add before.toQProb after.toQProb) error :=
    QProb.add_le_add (productPrecision_le first second left) (productPrecision_le first' second' right)
  have firstError := QProb.le_trans (error_of_limit_equiv first first' sameFirst before after) precisions
  have secondError := QProb.le_trans (error_of_limit_equiv second second' sameSecond before after) precisions
  have estimated := SignedRatio.product_error_bound
    (first.value before) (second.value before) (first'.value after) (second'.value after)
    error error (QProb.ofNat first'.magnitudeBound) (QProb.ofNat second.magnitudeBound)
    firstError secondError
    (first'.magnitude_bounded after (productPrecision_le_one first' second' right))
    (second.magnitude_bounded before (productPrecision_le_one first second left))
  have regrouped : QProb.Equiv
      (QProb.add (QProb.mul error (QProb.ofNat second.magnitudeBound))
        (QProb.mul (QProb.ofNat first'.magnitudeBound) error))
      (QProb.mul (QProb.ofNat (first'.magnitudeBound + second.magnitudeBound)) error) := by
    simp only [QProb.Equiv, QProb.add, QProb.mul, QProb.ofNat,
      Nat.mul_one, Nat.one_mul, Nat.add_mul]
    ac_rfl
  exact QProb.le_congr (QProb.equiv_refl _) regrouped estimated

end Thesis.Probability.RegularRationalApproximation
