import Thesis.Probability.ConstructiveRealEntropyStrongConcavityClosed

namespace Thesis.Examples.ConstructiveEntropyCurvature
open Probability ConstructiveReal

private def halfRatio : SignedRatio := ⟨1, 2, by decide⟩
private def eighthRatio : SignedRatio := ⟨1, 8, by decide⟩
private def z : UnitIntervalValue := .ofQProb QProb.zero (by decide)
private def o : UnitIntervalValue := .ofQProb QProb.one (by decide)
private def h : UnitIntervalValue := .ofQProb ⟨1, 2, by decide⟩ (by decide)
private theorem hz : Equiv z.entropy zero := realEntropyTerm_zero z.nonnegative z.bounded
private theorem ho : Equiv o.entropy zero := realEntropyTerm_one o.nonnegative o.bounded
private theorem hh : Equiv h.entropy (ofSignedRatio halfRatio) :=
  equiv_trans (UnitIntervalValue.entropy_ofQProb (⟨1, 2, by decide⟩ : QProb) (by decide))
    (equiv_trans (ExactLog.interpret_congr (by decide +kernel :
      ExactLog.Equiv (Probability.entropyTerm (⟨1, 2, by decide⟩ : QProb)) (ExactLog.ofSignedRatio halfRatio)))
      (ExactLog.interpret_ofSignedRatio halfRatio))

private theorem midpoint_entropy : Equiv (z.midpoint o).entropy (ofSignedRatio halfRatio) := by
  have value : Equiv (z.midpoint o).value h.value :=
    equiv_trans (mul_congr (zero_add one) (equiv_refl _)) (one_mul h.value)
  exact equiv_trans (realEntropyTerm_congr value (z.midpoint o).nonnegative h.nonnegative (z.midpoint o).bounded h.bounded) hh

private def left (x y : UnitIntervalValue) : ConstructiveReal :=
  add (mul (add x.entropy y.entropy) (ofSignedRatio halfRatio))
    (mul (mul (sub x.value y.value) (sub x.value y.value)) (ofSignedRatio eighthRatio))

private theorem left_of_zero (x y : UnitIntervalValue) (hx : Equiv x.entropy zero) (hy : Equiv y.entropy zero)
    (arithmetic : Equiv (mul (mul (sub x.value y.value) (sub x.value y.value)) (ofSignedRatio eighthRatio)) (ofSignedRatio eighthRatio)) :
    Equiv (left x y) (ofSignedRatio eighthRatio) := by
  have average : Equiv (mul (add x.entropy y.entropy) (ofSignedRatio halfRatio)) zero :=
    equiv_trans (mul_congr (equiv_trans (add_congr hx hy) (zero_add zero)) (equiv_refl _)) (zero_mul _)
  exact equiv_trans (add_congr average arithmetic) (zero_add _)

private def arithmeticExpr (a b : SignedRatio) : RationalPolynomial.Expression 0 :=
  .mul (.mul (.sub (.constant a) (.constant b)) (.sub (.constant a) (.constant b))) (.constant eighthRatio)

private theorem endpoint_arithmetic (a b : SignedRatio)
    (checked : (arithmeticExpr a b).equalityCheck (.constant eighthRatio) = true) :
    Equiv (mul (mul (sub (ofSignedRatio a) (ofSignedRatio b)) (sub (ofSignedRatio a) (ofSignedRatio b))) (ofSignedRatio eighthRatio))
      (ofSignedRatio eighthRatio) :=
  RationalPolynomial.Expression.equalityCheck_sound_real _ _ checked (fun i => Fin.elim0 i)

/-- The zero/unit endpoint case yields the actual numerical inequality
1/8 ≤ 1/2. No logarithm at zero or positivity premise on that endpoint occurs. -/
example : LE (ofSignedRatio eighthRatio) (ofSignedRatio halfRatio) :=
  (le_congr (left_of_zero z o hz ho (endpoint_arithmetic SignedRatio.zero SignedRatio.one (by decide +kernel))) midpoint_entropy).mp
    (z.entropy_strong_midpoint o)

/-- The same boundary case in the opposite order exercises the order-free
real theorem and its midpoint presentation invariance. -/
example : LE (ofSignedRatio eighthRatio) (ofSignedRatio halfRatio) := by
  have right : Equiv (o.midpoint z).entropy (ofSignedRatio halfRatio) :=
    equiv_trans (realEntropyTerm_congr (midpoint_comm o.value z.value)
      (o.midpoint z).nonnegative (z.midpoint o).nonnegative (o.midpoint z).bounded (z.midpoint o).bounded) midpoint_entropy
  exact (le_congr (left_of_zero o z ho hz (endpoint_arithmetic SignedRatio.one SignedRatio.zero (by decide +kernel))) right).mp
    (o.entropy_strong_midpoint z)

/-- A noncanonical zero mass is smoothed to exactly 1/(n+2), rather than
requiring a positive input or silently evaluating log(0). -/
example (n : Nat) : QProb.Equiv (smoothUnitMass (⟨0, 7, by decide⟩ : QProb) n) ⟨1, n + 2, by omega⟩ := by
  change (((n + 1) * 0) * (n + 2) + 1 * ((n + 2) * 7)) * (n + 2) = 1 * (((n + 2) * 7) * (n + 2))
  simp only [Nat.mul_zero, Nat.zero_mul, Nat.zero_add, Nat.one_mul]

end Thesis.Examples.ConstructiveEntropyCurvature
