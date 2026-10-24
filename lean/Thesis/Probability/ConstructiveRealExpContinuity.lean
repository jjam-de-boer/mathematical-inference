import Thesis.Probability.ConstructiveRealExponential

namespace Thesis.Probability.ConstructiveReal

/-- A real input error propagates through the exponential with the same
explicit Taylor constant as for rational inputs. The supplied natural bound
controls fine rational approximants, not decidable comparisons of real values. -/
theorem exp_within_bounded {x y : ConstructiveReal} (error : QProb) (bound : Nat)
    (close : Within error x y)
    (boundedX : ∀ precision, PositiveRatio.LE precision PositiveRatio.one →
      QProb.LE (x.rationalApproximation.value precision).magnitude (QProb.ofNat bound))
    (boundedY : ∀ precision, PositiveRatio.LE precision PositiveRatio.one →
      QProb.LE (y.rationalApproximation.value precision).magnitude (QProb.ofNat bound)) :
    Within (QProb.mul error (QProb.ofNat (RationalTaylorExponential.uniformSumBound bound))) x.exp y.exp := by
  apply within_of_forall_add_error
  intro precision
  let input := RationalExponential.inputPrecision bound precision
  let constant := QProb.ofNat (RationalTaylorExponential.uniformSumBound bound)
  have tail (n : Nat) (later : input.half.den ≤ n) :
      Within (QProb.add (QProb.mul error constant) precision.toQProb) (x.expSequence.value n) (y.expSequence.value n) := by
    let unit := PositiveRatio.unitPrecision n
    have rationalError := RegularRationalApproximation.error_of_limit_within x.rationalApproximation y.rationalApproximation error
      ((within_congr x.rationalApproximation_limit y.rationalApproximation_limit).mpr close) unit unit
    have small := PositiveRatio.unitPrecision_le input.half n later
    have slack := QProb.le_trans (QProb.add_le_add small small)
      (QProb.le_congr (QProb.equiv_refl _) input.half_sum (QProb.le_refl _))
    have scaled := QProb.le_congr (QProb.equiv_refl _) (PositiveRatio.divide_mul precision _ _)
      (QProb.mul_le_mul slack (QProb.le_refl constant))
    have estimate := QProb.le_trans (QProb.mul_le_mul rationalError (QProb.le_refl constant))
      (QProb.le_congr (QProb.equiv_symm (QProb.add_mul_distrib _ _ _)) (QProb.equiv_refl _)
        (QProb.add_le_add (QProb.le_refl (QProb.mul error constant)) scaled))
    exact within_mono (RationalExponential.exp_within _ _ bound
      (boundedX unit (PositiveRatio.unitPrecision_le_one n)) (boundedY unit (PositiveRatio.unitPrecision_le_one n))) estimate
  exact RealCauchySequence.limit_within_of_tail x.expSequence y.expSequence _ input.half.den tail

/-- Every two supplied real presentations compute a certified exponential
error bound. A uniform external bound can instead be supplied to the theorem
above when the inputs vary over an entire family. -/
theorem exp_within {x y : ConstructiveReal} (error : QProb) (close : Within error x y) :
    Within (QProb.mul error (QProb.ofNat (RationalTaylorExponential.uniformSumBound
      (max x.rationalApproximation.magnitudeBound y.rationalApproximation.magnitudeBound)))) x.exp y.exp := by
  apply exp_within_bounded error _ close
  · intro precision small
    apply QProb.le_trans (x.rationalApproximation.magnitude_bounded precision small)
    simpa only [QProb.LE, QProb.ofNat, Nat.mul_one] using Nat.le_max_left x.rationalApproximation.magnitudeBound y.rationalApproximation.magnitudeBound
  · intro precision small
    apply QProb.le_trans (y.rationalApproximation.magnitude_bounded precision small)
    simpa only [QProb.LE, QProb.ofNat, Nat.mul_one] using Nat.le_max_right x.rationalApproximation.magnitudeBound y.rationalApproximation.magnitudeBound

theorem exp_within_of_close {x y : ConstructiveReal} (bound : Nat) (precision : PositiveRatio)
    (close : Within (RationalExponential.inputPrecision bound precision).toQProb x y)
    (boundedX : ∀ input, PositiveRatio.LE input PositiveRatio.one →
      QProb.LE (x.rationalApproximation.value input).magnitude (QProb.ofNat bound))
    (boundedY : ∀ input, PositiveRatio.LE input PositiveRatio.one →
      QProb.LE (y.rationalApproximation.value input).magnitude (QProb.ofNat bound)) :
    Within precision.toQProb x.exp y.exp :=
  within_mono (exp_within_bounded _ bound close boundedX boundedY)
    (QProb.le_congr (QProb.equiv_refl _) (PositiveRatio.divide_mul precision _ _) (QProb.le_refl _))

end Thesis.Probability.ConstructiveReal
