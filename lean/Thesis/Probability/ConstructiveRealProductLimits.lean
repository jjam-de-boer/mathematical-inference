import Thesis.Probability.ConstructiveRealRing
import Thesis.Probability.ConstructiveRealStability

namespace Thesis.Probability.RealCauchySequence
open ConstructiveReal

/-- One fixed presentation of the already constructed limit bounds every
sufficiently late term's fine rational approximants. -/
def tailMagnitudeBound (sequence : RealCauchySequence) : Nat := sequence.limit.rationalApproximation.magnitudeBound + 3

theorem tailMagnitudeBound_pos (sequence : RealCauchySequence) : 0 < sequence.tailMagnitudeBound := by
  unfold tailMagnitudeBound
  omega

theorem tail_magnitude_bounded (sequence : RealCauchySequence) (n : Nat)
    (later : sequence.modulus PositiveRatio.one.half.half ≤ n) (precision : PositiveRatio)
    (small : PositiveRatio.LE precision PositiveRatio.one) :
    QProb.LE ((sequence.value n).rationalApproximation.value precision).magnitude (QProb.ofNat sequence.tailMagnitudeBound) :=
  RegularRationalApproximation.magnitude_bounded_near _ _
    ((within_congr (sequence.value n).rationalApproximation_limit sequence.limit.rationalApproximation_limit).mpr
      (sequence.tail_within PositiveRatio.one n later)) precision small

theorem limit_magnitude_bounded (sequence : RealCauchySequence) (precision : PositiveRatio)
    (small : PositiveRatio.LE precision PositiveRatio.one) :
    QProb.LE (sequence.limit.rationalApproximation.value precision).magnitude (QProb.ofNat sequence.tailMagnitudeBound) := by
  apply QProb.le_trans (sequence.limit.rationalApproximation.magnitude_bounded precision small)
  change sequence.limit.rationalApproximation.magnitudeBound * 1 ≤
    (sequence.limit.rationalApproximation.magnitudeBound + 3) * 1
  omega

/-- The product schedule is computed from fixed bounds on both tails.
It does not use varying, potentially very unreduced term numerators. -/
def productPrecision (first second : RealCauchySequence) (precision : PositiveRatio) : PositiveRatio :=
  (precision.divideNat (first.tailMagnitudeBound + second.tailMagnitudeBound)
    (Nat.add_pos_left first.tailMagnitudeBound_pos _)).capOne

theorem productPrecision_le_one (first second : RealCauchySequence) (precision : PositiveRatio) :
    PositiveRatio.LE (productPrecision first second precision) PositiveRatio.one := PositiveRatio.capOne_le_one _

private theorem product_error_le (first second : RealCauchySequence) (precision : PositiveRatio) :
    QProb.LE
      (QProb.add (QProb.mul (productPrecision first second precision).toQProb (QProb.ofNat second.tailMagnitudeBound))
        (QProb.mul (QProb.ofNat first.tailMagnitudeBound) (productPrecision first second precision).toQProb)) precision.toQProb := by
  have collect : QProb.Equiv
      (QProb.add (QProb.mul (productPrecision first second precision).toQProb (QProb.ofNat second.tailMagnitudeBound))
        (QProb.mul (QProb.ofNat first.tailMagnitudeBound) (productPrecision first second precision).toQProb))
      (QProb.mul (productPrecision first second precision).toQProb (QProb.ofNat (first.tailMagnitudeBound + second.tailMagnitudeBound))) := by
    simp only [QProb.Equiv, QProb.add, QProb.mul, QProb.ofNat, Nat.mul_one, Nat.one_mul, Nat.mul_add, Nat.add_mul]
    ac_rfl
  exact QProb.le_congr (QProb.equiv_symm collect) (QProb.equiv_refl _)
    (PositiveRatio.capped_divide_mul precision _ _)

private def tailIndex (first second : RealCauchySequence) : Nat :=
  max (first.modulus PositiveRatio.one.half.half) (second.modulus PositiveRatio.one.half.half)

/-- Pointwise multiplication of any two effective real Cauchy sequences.
The necessary uniform tail bounds are derived, not additional hypotheses. -/
def mul (first second : RealCauchySequence) : RealCauchySequence where
  value n := ConstructiveReal.mul (first.value n) (second.value n)
  modulus precision := max
    (max (first.modulus (productPrecision first second precision)) (second.modulus (productPrecision first second precision)))
    (tailIndex first second)
  cauchy precision n m left right := by
    let p := productPrecision first second precision
    have nl : max (first.modulus p) (second.modulus p) ≤ n := Nat.le_trans (Nat.le_max_left _ _) left
    have ml : max (first.modulus p) (second.modulus p) ≤ m := Nat.le_trans (Nat.le_max_left _ _) right
    have nt : tailIndex first second ≤ n := Nat.le_trans (Nat.le_max_right _ _) left
    have mt : tailIndex first second ≤ m := Nat.le_trans (Nat.le_max_right _ _) right
    have compared := mul_within_bounded p.toQProb p.toQProb first.tailMagnitudeBound second.tailMagnitudeBound
      (first.cauchy p n m (Nat.le_trans (Nat.le_max_left _ _) nl) (Nat.le_trans (Nat.le_max_left _ _) ml))
      (second.cauchy p n m (Nat.le_trans (Nat.le_max_right _ _) nl) (Nat.le_trans (Nat.le_max_right _ _) ml))
      (first.tail_magnitude_bounded m (Nat.le_trans (Nat.le_max_left _ _) mt))
      (second.tail_magnitude_bounded n (Nat.le_trans (Nat.le_max_right _ _) nt))
    exact within_mono compared (product_error_le first second precision)

/-- The effective limit of pointwise products is the product of the
independently constructed limits. No boundedness premise is omitted. -/
theorem mul_limit (first second : RealCauchySequence) :
    Equiv (first.mul second).limit (ConstructiveReal.mul first.limit second.limit) := by
  apply limit_unique _ _ (fun precision => max
    (max (first.modulus (productPrecision first second precision).half.half)
      (second.modulus (productPrecision first second precision).half.half)) (tailIndex first second))
  intro precision n later
  let p := productPrecision first second precision
  have nl : max (first.modulus p.half.half) (second.modulus p.half.half) ≤ n := Nat.le_trans (Nat.le_max_left _ _) later
  have nt : tailIndex first second ≤ n := Nat.le_trans (Nat.le_max_right _ _) later
  have compared := mul_within_bounded p.toQProb p.toQProb first.tailMagnitudeBound second.tailMagnitudeBound
    (first.tail_within p n (Nat.le_trans (Nat.le_max_left _ _) nl))
    (second.tail_within p n (Nat.le_trans (Nat.le_max_right _ _) nl))
    first.limit_magnitude_bounded
    (second.tail_magnitude_bounded n (Nat.le_trans (Nat.le_max_right _ _) nt))
  exact within_mono compared (product_error_le first second precision)

/-- Every finite power preserves effective real convergence. -/
def pow (sequence : RealCauchySequence) : Nat → RealCauchySequence
  | 0 => constant ConstructiveReal.one
  | n + 1 => (pow sequence n).mul sequence

theorem pow_value (sequence : RealCauchySequence) (power n : Nat) :
    (sequence.pow power).value n = ConstructiveReal.pow (sequence.value n) power := by
  induction power with
  | zero => rfl
  | succ power ih => exact congrArg (fun value => ConstructiveReal.mul value (sequence.value n)) ih

theorem pow_limit (sequence : RealCauchySequence) (power : Nat) :
    Equiv (sequence.pow power).limit (ConstructiveReal.pow sequence.limit power) := by
  induction power with
  | zero => exact constant_limit ConstructiveReal.one
  | succ power ih => exact equiv_trans (mul_limit _ _) (mul_congr ih (equiv_refl _))

end Thesis.Probability.RealCauchySequence
