import Thesis.Probability.ConstructiveRealLogInverse

namespace Thesis.Examples.ConstructiveLogExp
open Probability ConstructiveReal

/-- Additivity forces zero and rational linearity without a continuity
premise or an arbitrary-real comparison. -/
example (f : AdditiveMap) : Equiv (f.value zero) zero := f.map_zero
example (f : AdditiveMap) : Equiv (f.value (ofSignedRatio ⟨-6, 4, by decide⟩))
    (mul (ofSignedRatio ⟨-6, 4, by decide⟩) (f.value one)) := f.map_rational _

example (f : AdditiveMap) (nonzero : Equiv (f.value zero) one) : False := by
  have impossible : Equiv one zero := equiv_trans (equiv_symm nonzero) f.map_zero
  exact (by decide +kernel : ¬ SignedRatio.Equiv SignedRatio.one SignedRatio.zero) ((ofSignedRatio_equiv_iff _ _).mp impossible)

/-- A sequence with a negative first term can still have a positive limit. -/
private def delayedOne : RealCauchySequence where
  value n := if n = 0 then neg one else one
  modulus _ := 1
  cauchy precision n m hn hm := by
    have hn' : n ≠ 0 := by omega
    have hm' : m ≠ 0 := by omega
    simp only [if_neg hn', if_neg hm']
    exact within_refl _ one

private theorem delayedOne_limit : Equiv delayedOne.limit one := by
  apply delayedOne.limit_unique one (fun _ => 1)
  intro precision n later
  have nonzero : n ≠ 0 := by omega
  simpa only [delayedOne, if_neg nonzero] using within_refl precision.toQProb one

private def half : PositiveRatio := ⟨1, 2, by decide, by decide⟩
private theorem delayedOne_positive : LE (ofSignedRatio half.toSignedRatio) delayedOne.limit :=
  (le_congr (equiv_refl _) (equiv_symm delayedOne_limit)).mp ((ofSignedRatio_le_iff _ _).mpr (by decide +kernel))

/-- The computable positive tail, rather than the whole original sequence,
is what licenses taking its logarithm. -/
example : Equiv ((delayedOne.positiveTail half).value 0) one := equiv_refl one
example : Equiv (delayedOne.mapLog2Tail half delayedOne_positive).limit zero :=
  equiv_trans (delayedOne.mapLog2Tail_limit half delayedOne_positive)
    (equiv_trans (positiveLog2_congr delayedOne_limit half PositiveRatio.one delayedOne_positive (le_refl one))
      (positiveLog2_one PositiveRatio.one (le_refl one)))

example (x : ConstructiveReal) : Equiv x.expLog2 (mul x RationalLogSecant.limit) := expLog2_value x
example : HasDerivativeAt expLog2 zero RationalLogSecant.limit := expLog2_hasDerivativeAt_zero

/-- Both inverse directions are tested with their actual domain certificates. -/
example (x : ConstructiveReal) : Equiv (x.exp.positiveLn x.expLower x.exp_lower) x := positiveLn_exp x
example (x : ConstructiveReal) (lower : PositiveRatio) (bounded : LE (ofSignedRatio lower.toSignedRatio) x) :
    Equiv (exp (x.positiveLn lower bounded)) x := exp_positiveLn x lower bounded

example (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) (ofSignedRatio (PositiveRatio.ofNat 2 (by decide)).toSignedRatio)) :
    Equiv ((ofSignedRatio (PositiveRatio.ofNat 2 (by decide)).toSignedRatio).positiveLn lower bounded) lnTwo :=
  positiveLn_two lower bounded

example (point : ConstructiveReal) (lower : PositiveRatio) (inside : LE (ofSignedRatio lower.toSignedRatio) point) :
    HasDerivativeWithinAt (fun y => LE (ofSignedRatio lower.toSignedRatio) y)
      (fun y admitted => y.positiveLn lower admitted) point inside (point.positiveInverse lower inside) :=
  positiveLn_hasDerivativeWithinAt point lower inside

example (x y : ConstructiveReal) : LE x.exp y.exp ↔ LE x y := exp_le_exp_iff x y
example (x y : ConstructiveReal) : Equiv x.exp y.exp ↔ Equiv x y := exp_equiv_iff x y

/-- Logarithm injectivity retains independent positive-bound witnesses. -/
example (x y : ConstructiveReal) (lowerX lowerY : PositiveRatio)
    (boundedX : LE (ofSignedRatio lowerX.toSignedRatio) x) (boundedY : LE (ofSignedRatio lowerY.toSignedRatio) y)
    (same : Equiv (x.positiveLn lowerX boundedX) (y.positiveLn lowerY boundedY)) : Equiv x y :=
  (positiveLn_equiv_iff x y lowerX lowerY boundedX boundedY).mp same

end Thesis.Examples.ConstructiveLogExp
