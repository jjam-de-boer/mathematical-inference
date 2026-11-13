import Thesis.Probability.ConstructiveRealOrderedRing
import Thesis.Probability.ConstructiveRealCauchyOrder
import Thesis.Probability.EntropyRealProducts

namespace Thesis.Examples.ConstructiveRealOrder
open Probability

example (x y : ConstructiveReal) (first : ConstructiveReal.LE ConstructiveReal.zero x)
    (second : ConstructiveReal.LE ConstructiveReal.zero y) : ConstructiveReal.LE ConstructiveReal.zero (ConstructiveReal.mul x y) :=
  ConstructiveReal.mul_nonnegative first second

example (x : ConstructiveReal) : ConstructiveReal.LE ConstructiveReal.zero (ConstructiveReal.mul x x) :=
  ConstructiveReal.square_nonnegative x

example (x y factor : ConstructiveReal) (positive : ConstructiveReal.LE ConstructiveReal.zero factor)
    (compared : ConstructiveReal.LE x y) : ConstructiveReal.LE (ConstructiveReal.mul factor x) (ConstructiveReal.mul factor y) :=
  ConstructiveReal.mul_le_mul_nonnegative positive compared

example (x y : ConstructiveReal) (positive : ConstructiveReal.LE ConstructiveReal.zero x)
    (compared : ConstructiveReal.LE x y) (n : Nat) : ConstructiveReal.LE (ConstructiveReal.pow x n) (ConstructiveReal.pow y n) :=
  ConstructiveReal.pow_mono positive compared n

example (sequence : RealCauchySequence) (lower upper : ConstructiveReal)
    (bounded : ∀ n, ConstructiveReal.LE lower (sequence.value n) ∧ ConstructiveReal.LE (sequence.value n) upper) :
    ConstructiveReal.LE lower sequence.limit ∧ ConstructiveReal.LE sequence.limit upper := sequence.limit_bounds lower upper bounded

/-- This presentation of zero has genuinely negative lower endpoints.
Clamping is needed even though the real value is nonnegative. -/
private def zeroApproximation : RegularRationalApproximation where
  value _ := SignedRatio.zero
  regular first second := SignedRatio.le_add_of_nonnegative _ _
    (SignedRatio.nonnegative_add first.signed_nonnegative second.signed_nonnegative)

private def looseZero : ConstructiveReal := zeroApproximation.limit

example : SignedRatio.LE (looseZero.enclose PositiveRatio.one).lower ⟨-1, 2, by decide⟩ := by decide +kernel
example : ¬ SignedRatio.LE SignedRatio.zero (looseZero.enclose PositiveRatio.one).lower := by decide +kernel
example : SignedRatio.Equiv (looseZero.nonnegativeCenter PositiveRatio.one) SignedRatio.zero := by decide +kernel
example (precision : PositiveRatio) : ConstructiveReal.Within precision.toQProb looseZero
    (ConstructiveReal.ofSignedRatio (looseZero.nonnegativeCenter precision)) :=
  looseZero.nonnegativeCenter_within (zeroApproximation.limit_nonnegative (fun _ => SignedRatio.le_refl _)) precision

example (x : ConstructiveReal) (weight : QProb) : ConstructiveReal.Equiv
    (ConstructiveReal.scaleRatio weight x) (ConstructiveReal.mul (ConstructiveReal.ofSignedRatio weight.toSignedRatio) x) :=
  ConstructiveReal.scaleRatio_mul weight x

/-- Unreduced coefficients act on arbitrary, possibly irrational, values. -/
example (x : ConstructiveReal) : ConstructiveReal.Equiv
    (ConstructiveReal.scaleRatio ⟨2, 6, by decide⟩ x) (ConstructiveReal.scaleRatio ⟨1, 3, by decide⟩ x) :=
  ConstructiveReal.scaleRatio_weight_congr (by decide +kernel) x

example : ConstructiveReal.Equiv (entropyTerm ⟨1, 3, by decide⟩).interpret
    (ConstructiveReal.neg (ConstructiveReal.mul (ConstructiveReal.ofSignedRatio (QProb.toSignedRatio ⟨1, 3, by decide⟩))
      (ConstructiveReal.rationalLog2 ⟨1, 3, by decide, by decide⟩))) := entropyTerm_interpret_mul _ (by decide)

example : ConstructiveReal.Equiv (entropySum [⟨1, 3, by decide⟩, QProb.zero, ⟨2, 3, by decide⟩]).interpret
    (ConstructiveReal.listSum ([⟨1, 3, by decide⟩, QProb.zero, ⟨2, 3, by decide⟩].map (fun mass =>
      if positive : 0 < mass.num then
        ConstructiveReal.neg (ConstructiveReal.mul (ConstructiveReal.ofSignedRatio mass.toSignedRatio)
          (ConstructiveReal.rationalLog2 ⟨mass.num, mass.den, positive, mass.den_pos⟩))
      else ConstructiveReal.zero))) := entropySum_interpret_mul _

end Thesis.Examples.ConstructiveRealOrder
