import Thesis.Probability.RationalExponentialContinuity
import Thesis.Probability.RationalPrecision

namespace Thesis.Probability.ConstructiveReal

/-- Exponentials of computed rational approximants form an effective real
Cauchy sequence. Uniform Taylor bounds supply its modulus; no arbitrary real
comparison, real probability weight or assumed analytic identity is used. -/
def expSequence (x : ConstructiveReal) : RealCauchySequence where
  value n := RationalExponential.exp (x.rationalApproximation.value (PositiveRatio.unitPrecision n))
  modulus precision := (RationalExponential.inputPrecision x.rationalApproximation.magnitudeBound precision).half.den
  cauchy precision n m left right := by
    have errors := x.rationalApproximation.error_bound (PositiveRatio.unitPrecision n) (PositiveRatio.unitPrecision m)
    have smaller := QProb.add_le_add (PositiveRatio.unitPrecision_le _ n left) (PositiveRatio.unitPrecision_le _ m right)
    have close := QProb.le_trans errors (QProb.le_congr (QProb.equiv_refl _) (PositiveRatio.half_sum _) smaller)
    exact RationalExponential.exp_within_of_close _ _ _ precision
      (x.rationalApproximation.magnitude_bounded _ (PositiveRatio.unitPrecision_le_one n))
      (x.rationalApproximation.magnitude_bounded _ (PositiveRatio.unitPrecision_le_one m)) close

/-- Natural exponential of a general constructive real, obtained by the
proved continuous extension of its rational Taylor exponential. -/
def exp (x : ConstructiveReal) : ConstructiveReal := x.expSequence.limit

/-- Every sufficiently late rational-input exponential approximates the real
exponential to a supplied rational accuracy. -/
theorem exp_tail (x : ConstructiveReal) (precision : PositiveRatio) (n : Nat)
    (later : x.expSequence.modulus precision.half.half ≤ n) :
    Within precision.toQProb (RationalExponential.exp (x.rationalApproximation.value (PositiveRatio.unitPrecision n))) x.exp :=
  x.expSequence.tail_within precision n later

/-- The real extension recovers the already certified exponential of every
signed rational argument, including negative arguments and zero. -/
theorem exp_ofSignedRatio (x : SignedRatio) : Equiv (exp (ofSignedRatio x)) (RationalExponential.exp x) := by
  apply RealCauchySequence.limit_unique _ _ (fun _ => 0)
  intro precision n _
  exact within_refl precision.toQProb (RationalExponential.exp x)

/-- Exponentiation is independent of the chosen real enclosures, even when
those presentations compute different bounds and evaluation schedules. -/
theorem exp_congr {x y : ConstructiveReal} (same : Equiv x y) : Equiv x.exp y.exp := by
  let bound := max x.rationalApproximation.magnitudeBound y.rationalApproximation.magnitudeBound
  have compareTerms (precision : PositiveRatio) (n : Nat)
      (later : (RationalExponential.inputPrecision bound precision).half.den ≤ n) :
      Within precision.toQProb (x.expSequence.value n) (y.expSequence.value n) := by
    let unit := PositiveRatio.unitPrecision n
    have first := (within_congr (equiv_refl _) same).mp (within_symm (x.lower_within unit))
    have between := within_triangle first (y.lower_within unit)
    have errors := (within_ofSignedRatio_iff _ _ _).mp between
    have small := PositiveRatio.unitPrecision_le (RationalExponential.inputPrecision bound precision).half n later
    have close := QProb.le_trans errors (QProb.le_congr (QProb.equiv_refl _) (PositiveRatio.half_sum _)
      (QProb.add_le_add small small))
    have enlargeX : QProb.LE (QProb.ofNat x.rationalApproximation.magnitudeBound) (QProb.ofNat bound) := by
      simpa only [QProb.LE, QProb.ofNat, Nat.mul_one] using Nat.le_max_left x.rationalApproximation.magnitudeBound y.rationalApproximation.magnitudeBound
    have enlargeY : QProb.LE (QProb.ofNat y.rationalApproximation.magnitudeBound) (QProb.ofNat bound) := by
      simpa only [QProb.LE, QProb.ofNat, Nat.mul_one] using Nat.le_max_right x.rationalApproximation.magnitudeBound y.rationalApproximation.magnitudeBound
    exact RationalExponential.exp_within_of_close _ _ bound precision
      (QProb.le_trans (x.rationalApproximation.magnitude_bounded unit (PositiveRatio.unitPrecision_le_one n)) enlargeX)
      (QProb.le_trans (y.rationalApproximation.magnitude_bounded unit (PositiveRatio.unitPrecision_le_one n)) enlargeY) close
  apply RealCauchySequence.limit_unique _ _ (fun precision => max
    (RationalExponential.inputPrecision bound precision.half).half.den
    (y.expSequence.modulus precision.half.half.half))
  intro precision n later
  exact within_triangle_halves precision
    (compareTerms precision.half n (Nat.le_trans (Nat.le_max_left _ _) later))
    (y.expSequence.tail_within precision.half n (Nat.le_trans (Nat.le_max_right _ _) later))

theorem exp_zero : Equiv zero.exp one := equiv_trans (exp_ofSignedRatio SignedRatio.zero) RationalExponential.exp_zero

end Thesis.Probability.ConstructiveReal
