import Thesis.Probability.ConstructiveUniformDerivative
import Thesis.Probability.ConstructiveRealLogGeneralDerivative

namespace Thesis.Probability.ConstructiveReal

/-- The logarithm first variation has one computed modulus on the whole
supplied positive half-line, independent of each point's presentation. -/
def positiveLog2_uniformDerivative (lower : PositiveRatio) :
    UniformDerivativeWithin (fun x => LE (ofSignedRatio lower.toSignedRatio) x)
      (fun x admitted => x.positiveLog2 lower admitted)
      (fun x admitted => mul RationalLogSecant.limit (x.positiveInverse lower admitted)) where
  congr x y hx hy same := positiveLog2_congr same lower lower hx hy
  modulus := logModulus lower
  remainder epsilon radius small x hx y hy close := positiveLog2_first_variation x y lower hx hy epsilon radius small close

/-- The base-two logarithm slope is at least one on (0,1]. The coefficient
1/ln(2) and positive inverse are both established analytic values. -/
theorem positiveLog2_slope_lower (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) (unit : LE x one) :
    LE one (mul RationalLogSecant.limit (x.positiveInverse lower bounded)) := by
  have inverseLower : LE one (x.positiveInverse lower bounded) :=
    (mul_le_mul_positive_iff x lower bounded one (x.positiveInverse lower bounded)).mp
      ((le_congr (mul_one x) (x.mul_positiveInverse lower bounded)).mpr unit)
  have oneNonnegative : LE zero one := (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
  exact (le_congr (one_mul one) (equiv_refl _)).mp
    (mul_le_mul RationalLogSecant.one_le_limit inverseLower oneNonnegative (x.positiveInverse_nonnegative lower bounded))

/-- A global logarithm increment bound follows by summing the uniform
first-variation bounds over rational interval partitions. No classical
mean-value point or real-order decision is introduced. -/
theorem positiveLog2_increment_lower (x y : ConstructiveReal) (lower : PositiveRatio)
    (boundedX : LE (ofSignedRatio lower.toSignedRatio) x) (boundedY : LE (ofSignedRatio lower.toSignedRatio) y)
    (ordered : LE x y) (unitY : LE y one) :
    LE (sub y x) (sub (y.positiveLog2 lower boundedY) (x.positiveLog2 lower boundedX)) := by
  let lx := x.positiveLog2 lower boundedX
  let ly := y.positiveLog2 lower boundedY
  let length := sub y x
  have nonnegativeX : LE zero x := le_trans
    ((ofSignedRatio_le_iff _ _).mpr ((SignedRatio.zero_le_iff_nonnegative _).mpr lower.signed_nonnegative)) boundedX
  have width : LE length one := interval_width_le_one x y nonnegativeX unitY
  have estimate := (positiveLog2_uniformDerivative lower).lower_bound x y one ordered width
    (fun z above _ => le_trans boundedX above)
    (fun z hz _ below => positiveLog2_slope_lower z lower hz (le_trans below unitY))
  have linear : LE (add lx length) ly := (le_congr (add_congr (equiv_refl lx) (mul_one length)) (equiv_refl ly)).mp estimate
  have positive := (zero_le_sub_iff ly (add lx length)).mpr linear
  have rearranged : Equiv (sub ly (add lx length)) (sub (sub ly lx) length) :=
    equiv_trans (add_congr (equiv_refl _) (neg_add lx length)) (equiv_symm (add_assoc _ _ _))
  exact (zero_le_sub_iff _ _).mp ((le_congr (equiv_refl zero) rearranged).mp positive)

end Thesis.Probability.ConstructiveReal
