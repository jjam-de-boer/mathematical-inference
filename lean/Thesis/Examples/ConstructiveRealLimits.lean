import Thesis.Probability.ConstructiveRealLimits
import Thesis.Probability.ExactLogInterpretation

namespace Thesis.Examples.ConstructiveRealLimits
open Probability

private def unit (n : Nat) : PositiveRatio := ⟨1, n + 1, by decide, Nat.zero_lt_succ n⟩

private theorem unit_bound (precision : PositiveRatio) (n : Nat) (later : precision.den ≤ n) :
    SignedRatio.LE (unit n).toSignedRatio precision.toSignedRatio := by
  apply (SignedRatio.toSignedRatio_le_iff (unit n).toQProb precision.toQProb).mpr
  change 1 * precision.den ≤ precision.num * (n + 1)
  rw [Nat.one_mul]
  exact Nat.le_trans (by omega) (Nat.le_mul_of_pos_left _ precision.num_pos)

private theorem below_one (n : Nat) : SignedRatio.LE (SignedRatio.sub SignedRatio.one (unit n).toSignedRatio) SignedRatio.one :=
  (SignedRatio.sub_le_iff_le_add _ _ _).mpr
    (SignedRatio.le_add_of_nonnegative _ _ (unit n).signed_nonnegative)

private theorem upper_one (precision : PositiveRatio) (n : Nat) (later : precision.den ≤ n) :
    SignedRatio.LE SignedRatio.one
      (SignedRatio.add (SignedRatio.sub SignedRatio.one (unit n).toSignedRatio) precision.toSignedRatio) := by
  have raised := SignedRatio.add_le_add
    (SignedRatio.le_refl (SignedRatio.sub SignedRatio.one (unit n).toSignedRatio)) (unit_bound precision n later)
  exact (SignedRatio.le_congr (SignedRatio.sub_add_cancel _ _) (SignedRatio.equiv_refl _)).mp raised

/-- A nonconstant sequence `1 − 1/(n+1)`, with an executable conservative
Cauchy modulus valid at every positive rational requested precision. -/
private def approachingOne : RationalCauchySequence where
  value n := SignedRatio.sub SignedRatio.one (unit n).toSignedRatio
  modulus precision := precision.den
  cauchy precision n m _ later := SignedRatio.le_trans (below_one n) (upper_one precision m later)

example : approachingOne.value 0 = SignedRatio.sub SignedRatio.one SignedRatio.one := rfl
example : SignedRatio.Equiv (approachingOne.value 3) ⟨3, 4, by decide⟩ := by decide +kernel

/-- The limit is proved to be one; it was constructed independently from
its Cauchy approximants and was not defined to be this claimed result. -/
example : ConstructiveReal.Equiv approachingOne.limit ConstructiveReal.one := by
  apply approachingOne.regular.limit_unique
  intro precision
  constructor
  · apply (ConstructiveReal.ofSignedRatio_le_iff _ _).mpr
    apply (SignedRatio.sub_le_iff_le_add _ _ _).mpr
    exact SignedRatio.le_trans (below_one precision.den)
      (SignedRatio.le_add_of_nonnegative _ _ precision.signed_nonnegative)
  · exact (ConstructiveReal.ofSignedRatio_le_iff _ _).mpr (upper_one precision precision.den (Nat.le_refl _))

example (precision : PositiveRatio) (n : Nat) (later : approachingOne.modulus precision.half ≤ n) :
    ConstructiveReal.LE (ConstructiveReal.ofSignedRatio (SignedRatio.sub (approachingOne.value n) precision.toSignedRatio))
      approachingOne.limit ∧
    ConstructiveReal.LE approachingOne.limit
      (ConstructiveReal.ofSignedRatio (SignedRatio.add (approachingOne.value n) precision.toSignedRatio)) :=
  approachingOne.tail_bounds precision n later

/-- Reconstruction applies to every coherent real presentation, including
the bisection presentation of a nonintegral logarithm. -/
example (x : ConstructiveReal) : ConstructiveReal.Equiv x.rationalApproximation.limit x := x.rationalApproximation_limit
example : ConstructiveReal.Equiv
    (ExactLog.log ⟨3, 1, by decide, by decide⟩).interpret.rationalApproximation.limit
    (ExactLog.log ⟨3, 1, by decide, by decide⟩).interpret := ConstructiveReal.rationalApproximation_limit _

end Thesis.Examples.ConstructiveRealLimits
