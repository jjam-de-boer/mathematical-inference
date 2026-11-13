import Thesis.Probability.ConstructiveRealCauchy
import Thesis.Probability.ExactLogInterpretation

namespace Thesis.Examples.ConstructiveRealCauchy
open Probability

example (sequence : RealCauchySequence) (precision : PositiveRatio) (n : Nat)
    (later : sequence.modulus precision.half.half ≤ n) :
    ConstructiveReal.Within precision.toQProb (sequence.value n) sequence.limit := sequence.tail_within precision n later

example (first second : RealCauchySequence) (same : ∀ n, ConstructiveReal.Equiv (first.value n) (second.value n)) :
    ConstructiveReal.Equiv first.limit second.limit := first.limit_congr second same

example (sequence : RealCauchySequence) (x : ConstructiveReal) (modulus : PositiveRatio → Nat)
    (converges : ∀ precision n, modulus precision ≤ n → ConstructiveReal.Within precision.toQProb (sequence.value n) x) :
    ConstructiveReal.Equiv sequence.limit x := sequence.limit_unique x modulus converges

example (sequences : List RealCauchySequence) :
    ConstructiveReal.Equiv (RealCauchySequence.listSum sequences).limit
      (ConstructiveReal.listSum (sequences.map RealCauchySequence.limit)) := RealCauchySequence.listSum_limit sequences

private def unit (n : Nat) : PositiveRatio := ⟨1, n + 1, by decide, Nat.zero_lt_succ n⟩

private theorem unit_bound (precision : PositiveRatio) (n : Nat) (later : precision.den ≤ n) :
    SignedRatio.LE (unit n).toSignedRatio precision.toSignedRatio := by
  apply (SignedRatio.toSignedRatio_le_iff _ _).mpr
  change 1 * precision.den ≤ precision.num * (n + 1)
  rw [Nat.one_mul]
  exact Nat.le_trans (by omega) (Nat.le_mul_of_pos_left _ precision.num_pos)

/-- A nonconstant rational sequence with an independently supplied modulus. -/
private def vanishing : RationalCauchySequence where
  value n := (unit n).toSignedRatio
  modulus precision := precision.den
  cauchy precision n m later _ := SignedRatio.le_trans (unit_bound precision n later)
    ((SignedRatio.le_congr (SignedRatio.equiv_refl _) (SignedRatio.add_comm _ _)).mp
      (SignedRatio.le_add_of_nonnegative _ _ (unit m).signed_nonnegative))

private theorem vanishing_limit : ConstructiveReal.Equiv vanishing.toReal.limit ConstructiveReal.zero := by
  apply vanishing.toReal.limit_unique ConstructiveReal.zero (fun precision => precision.den)
  intro precision n later
  apply (ConstructiveReal.within_ofSignedRatio_iff _ _ _).mpr
  apply (SignedRatio.magnitude_sub_le_iff _ _ _).mpr
  constructor
  · exact (SignedRatio.le_congr (SignedRatio.equiv_refl _) (SignedRatio.zero_add _)).mpr (unit_bound precision n later)
  · exact SignedRatio.le_trans
      ((SignedRatio.toSignedRatio_le_iff QProb.zero (unit n).toQProb).mpr (QProb.zero_le _))
      (SignedRatio.le_add_of_nonnegative _ _ precision.signed_nonnegative)

/-- The sequence has genuinely different terms. -/
example : ¬ ConstructiveReal.Equiv (vanishing.toReal.value 0) (vanishing.toReal.value 1) := by
  intro same
  have impossible : ¬ SignedRatio.Equiv (vanishing.value 0) (vanishing.value 1) := by decide +kernel
  exact impossible ((ConstructiveReal.ofSignedRatio_equiv_iff _ _).mp same)

/-- Shifting this sequence by any real value recovers that value in the
limit. The terms themselves may be irrational. -/
private theorem shifted_limit (x : ConstructiveReal) : ConstructiveReal.Equiv
    ((RealCauchySequence.constant x).add vanishing.toReal).limit x :=
  ConstructiveReal.equiv_trans (RealCauchySequence.add_limit _ _)
    (ConstructiveReal.equiv_trans (ConstructiveReal.add_congr (RealCauchySequence.constant_limit x) vanishing_limit)
      (ConstructiveReal.add_zero x))

example : ConstructiveReal.Equiv
    ((RealCauchySequence.constant (ExactLog.log ⟨3, 1, by decide, by decide⟩).interpret).add vanishing.toReal).limit
    (ExactLog.log ⟨3, 1, by decide, by decide⟩).interpret := shifted_limit _

example (sequence : RationalCauchySequence) : ConstructiveReal.Equiv sequence.toReal.limit sequence.limit := sequence.toReal_limit

end Thesis.Examples.ConstructiveRealCauchy
