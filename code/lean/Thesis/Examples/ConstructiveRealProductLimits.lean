import Thesis.Probability.ConstructiveRealProductLimits
import Thesis.Probability.ExactLogInterpretation

namespace Thesis.Examples.ConstructiveRealProductLimits
open Probability

example (first second : RealCauchySequence) : ConstructiveReal.Equiv (first.mul second).limit
    (ConstructiveReal.mul first.limit second.limit) := first.mul_limit second

example (sequence : RealCauchySequence) (power : Nat) : ConstructiveReal.Equiv (sequence.pow power).limit
    (ConstructiveReal.pow sequence.limit power) := sequence.pow_limit power

example (a b c d : ConstructiveReal) (firstError secondError : QProb)
    (first : ConstructiveReal.Within firstError a c) (second : ConstructiveReal.Within secondError b d) :
    ConstructiveReal.Within
      (QProb.add (QProb.mul firstError (QProb.ofNat b.rationalApproximation.magnitudeBound))
        (QProb.mul (QProb.ofNat c.rationalApproximation.magnitudeBound) secondError))
      (ConstructiveReal.mul a b) (ConstructiveReal.mul c d) := ConstructiveReal.mul_within _ _ first second

/-- All these fractions equal one, but their unreduced numerators grow
without bound. Uniform product estimates must not bound those numerators. -/
private def changingOne (n : Nat) : ConstructiveReal :=
  ConstructiveReal.ofSignedRatio ⟨((n + 1 : Nat) : Int), n + 1, Nat.zero_lt_succ n⟩

private theorem changingOne_value (n : Nat) : ConstructiveReal.Equiv (changingOne n) ConstructiveReal.one := by
  apply (ConstructiveReal.ofSignedRatio_equiv_iff _ _).mpr
  simp only [SignedRatio.Equiv, SignedRatio.one, Int.natCast_one, Int.mul_one, Int.one_mul]

private def changingPresentation : RealCauchySequence where
  value := changingOne
  modulus _ := 0
  cauchy precision n m _ _ :=
    (ConstructiveReal.within_congr (changingOne_value n) (changingOne_value m)).mpr
      (ConstructiveReal.within_refl precision.toQProb ConstructiveReal.one)

private theorem changingPresentation_limit : ConstructiveReal.Equiv changingPresentation.limit ConstructiveReal.one := by
  apply changingPresentation.limit_unique ConstructiveReal.one (fun _ => 0)
  intro precision n _
  exact (ConstructiveReal.within_congr (changingOne_value n) (ConstructiveReal.equiv_refl _)).mpr
    (ConstructiveReal.within_refl precision.toQProb ConstructiveReal.one)

example (n : Nat) (precision : PositiveRatio) (small : PositiveRatio.LE precision PositiveRatio.one) :
    QProb.LE ((changingPresentation.value n).rationalApproximation.value precision).magnitude
      (QProb.ofNat changingPresentation.tailMagnitudeBound) :=
  changingPresentation.tail_magnitude_bounded n (Nat.zero_le _) precision small

example : ConstructiveReal.Equiv (changingPresentation.mul changingPresentation).limit ConstructiveReal.one :=
  ConstructiveReal.equiv_trans (RealCauchySequence.mul_limit _ _)
    (ConstructiveReal.equiv_trans (ConstructiveReal.mul_congr changingPresentation_limit changingPresentation_limit)
      (ConstructiveReal.mul_one _))

/-- General polynomial convergence also applies to a certified irrational
logarithm; no rational atom-weight type is extended. -/
example (sequence : RealCauchySequence) (same : ConstructiveReal.Equiv sequence.limit
    (ExactLog.log ⟨3, 1, by decide, by decide⟩).interpret) :
    ConstructiveReal.Equiv (sequence.pow 3).limit
      (ConstructiveReal.pow (ExactLog.log ⟨3, 1, by decide, by decide⟩).interpret 3) :=
  ConstructiveReal.equiv_trans (sequence.pow_limit 3) (ConstructiveReal.pow_congr same 3)

end Thesis.Examples.ConstructiveRealProductLimits
