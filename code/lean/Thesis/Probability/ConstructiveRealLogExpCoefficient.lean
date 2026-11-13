import Thesis.Probability.ConstructiveRealLogExpLinear
import Thesis.Probability.ConstructiveDerivativeLocalDomain
import Thesis.Probability.ConstructiveDerivativeChain
import Thesis.Probability.ConstructiveDerivativeUniqueness
import Thesis.Probability.ConstructiveRealExpDerivative
import Thesis.Probability.ConstructiveRealLogGeneralDerivative

namespace Thesis.Probability.ConstructiveReal

/-- The derivative of log₂(exp x) at zero is the independently constructed
logarithm coefficient c. Positivity of the nearby exponential is supplied by
an explicit local-domain certificate, rather than a real sign test. -/
def expLog2_hasDerivativeAt_zero : HasDerivativeAt expLog2 zero RationalLogSecant.limit := by
  let inner := exp_hasDerivativeAt zero
  let half := PositiveRatio.one.half
  have oneBound : LE (ofSignedRatio PositiveRatio.one.toSignedRatio) zero.exp := exp_zero.2
  have inside : LE (ofSignedRatio half.toSignedRatio) zero.exp :=
    le_trans ((ofSignedRatio_le_iff _ _).mpr (by decide +kernel)) oneBound
  let partialDerivative := inner.chainWithin (positiveLog2_hasDerivativeWithinAt zero.exp half inside)
  let radius := inner.positiveRadius PositiveRatio.one
  let admitted := fun y close => inner.positive_near PositiveRatio.one oneBound y close
  have atPoint : Equiv (zero.exp.positiveLog2 half inside) zero.expLog2 :=
    positiveLog2_congr (equiv_refl zero.exp) half zero.expLower inside zero.exp_lower
  have nearby : ∀ (y : ConstructiveReal) (close : Within radius.toQProb zero y), Equiv ((y.exp).positiveLog2 half (admitted y close)) y.expLog2 := by
    intro y close
    exact positiveLog2_congr (equiv_refl y.exp) half y.expLower (admitted y close) y.exp_lower
  let total := partialDerivative.toLocalTotal expLog2 radius admitted atPoint nearby
  let inverse := zero.exp.positiveInverse half inside
  have reordered : Equiv (mul zero.exp (mul RationalLogSecant.limit inverse))
      (mul RationalLogSecant.limit (mul zero.exp inverse)) :=
    equiv_trans (mul_comm zero.exp (mul RationalLogSecant.limit inverse))
      (equiv_trans (mul_assoc RationalLogSecant.limit inverse zero.exp)
        (mul_congr (equiv_refl RationalLogSecant.limit) (mul_comm inverse zero.exp)))
  have slope : Equiv (mul zero.exp (mul RationalLogSecant.limit inverse)) RationalLogSecant.limit :=
    equiv_trans reordered (equiv_trans (mul_congr (equiv_refl RationalLogSecant.limit)
      (zero.exp.mul_positiveInverse half inside)) (mul_one RationalLogSecant.limit))
  exact total.slope_congr slope

/-- The linear coefficient of log₂(exp x) equals the logarithm slope already
derived from finite logarithm comparisons. This identifies the unit factor;
it is not assumed as part of either logarithm or exponential construction. -/
theorem expLog2_one_coefficient : Equiv one.expLog2 RationalLogSecant.limit := by
  let linear := ((HasDerivativeAt.identity zero).mul_constant one.expLog2).slope_congr (one_mul one.expLog2)
  let actual := linear.function_congr (fun y => equiv_symm (expLog2_linear y))
  exact actual.unique expLog2_hasDerivativeAt_zero

/-- The natural Taylor exponential has exactly the derived base-two
logarithm units, for every constructive real argument. -/
theorem expLog2_value (x : ConstructiveReal) : Equiv x.expLog2 (mul x RationalLogSecant.limit) :=
  equiv_trans (expLog2_linear x) (mul_congr (equiv_refl x) expLog2_one_coefficient)

end Thesis.Probability.ConstructiveReal
