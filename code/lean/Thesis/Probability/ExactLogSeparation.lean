import Thesis.Probability.ExactLogConvex

namespace Thesis.Probability.ExactLog

private theorem unit_power_lower (b n : Nat) :
    b ^ (n + 1) + (n + 1) * b ^ n ≤ (b + 1) ^ (n + 1) := by
  induction n with
  | zero => simp only [Nat.zero_add, Nat.pow_one, Nat.pow_zero, Nat.mul_one]; exact Nat.le_refl _
  | succ n ih =>
      have scaled := Nat.mul_le_mul_right (b + 1) ih
      calc
        b ^ (n + 1 + 1) + (n + 1 + 1) * b ^ (n + 1)
            ≤ b ^ (n + 1 + 1) + (n + 1 + 1) * b ^ (n + 1) + (n + 1) * b ^ n := Nat.le_add_right _ _
        _ = (b ^ (n + 1) + (n + 1) * b ^ n) * (b + 1) := by
          simp only [Nat.pow_succ, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
          ac_rfl
        _ ≤ (b + 1) ^ (n + 1 + 1) := by simpa only [Nat.pow_succ] using scaled

private theorem unit_power_double (b : Nat) (positive : 0 < b) :
    2 * b ^ b ≤ (b + 1) ^ b := by
  have lower := unit_power_lower b (b - 1)
  rw [Nat.sub_add_cancel positive] at lower
  have recovered : b * b ^ (b - 1) = b ^ b := by
    rw [Nat.mul_comm, ← Nat.pow_succ]
    congr 1
    omega
  rw [recovered, ← Nat.two_mul] at lower
  exact lower

/-- A positive exact logarithm has a computable natural multiple of at
least one bit. This supplies order separation without real completeness. -/
theorem one_le_multiple_of_not_nonpositive (x : ExactLog) (positive : ¬ LE x zero) :
    LE (log (PositiveRatio.ofNat 2 (by decide))) (scaleNat (x.degree * x.argument.den) x) := by
  have greater : x.argument.den < x.argument.num := by
    have refused : ¬ x.argument.num ≤ x.argument.den := by
      simpa only [LE, zero, PositiveRatio.pow, PositiveRatio.LE, PositiveRatio.toQProb,
        PositiveRatio.one, QProb.LE, Nat.pow_one, Nat.one_pow, Nat.mul_one, Nat.one_mul] using positive
    exact Nat.lt_of_not_ge refused
  have lower := Nat.le_trans (unit_power_double x.argument.den x.argument.den_pos)
    (Nat.pow_le_pow_left greater x.argument.den)
  have raised := Nat.pow_le_pow_left lower x.degree
  simp only [LE, log, scaleNat, PositiveRatio.ofNat, PositiveRatio.pow, PositiveRatio.LE,
    PositiveRatio.toQProb, QProb.LE, Nat.one_pow, Nat.pow_one, Nat.mul_one]
  simpa only [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm] using raised

/-- An exact logarithm all of whose natural multiples are at most one bit
is nonpositive. No general excluded middle or infinitesimal assumption occurs. -/
theorem nonpositive_of_multiples_bounded (x : ExactLog)
    (bounded : ∀ n, LE (scaleNat n x) (log (PositiveRatio.ofNat 2 (by decide)))) : LE x zero := by
  by_cases nonpositive : LE x zero
  · exact nonpositive
  · have lower := one_le_multiple_of_not_nonpositive x nonpositive
    have twice := (scaleNat_le_scaleNat_iff 2 (by decide) _ _).mpr lower
    rw [scaleNat_mul] at twice
    have compared := le_trans twice (bounded ((x.degree * x.argument.den) * 2))
    have impossible : ¬ LE (scaleNat 2 (log (PositiveRatio.ofNat 2 (by decide))))
        (log (PositiveRatio.ofNat 2 (by decide))) := by decide +kernel
    exact False.elim (impossible compared)

private theorem scale_neg (n : Nat) (x : ExactLog) : scaleNat n (neg x) = neg (scaleNat n x) := by
  apply ext
  · exact (PositiveRatio.inv_pow _ _).symm
  · rfl

/-- Bounded error after every natural amplification forces the exact order.
This is the Archimedean step in the rational Shannon uniqueness argument. -/
theorem le_of_multiples_le_add_one (x y : ExactLog)
    (bounded : ∀ n, LE (scaleNat n x)
      (add (scaleNat n y) (log (PositiveRatio.ofNat 2 (by decide))))) : LE x y := by
  apply (sub_le_zero_iff x y).mp
  apply nonpositive_of_multiples_bounded
  intro n
  have moved := (add_le_add_right_iff _ _ (neg (scaleNat n y))).mpr (bounded n)
  have reduced : Equiv (add (add (scaleNat n y) (log (PositiveRatio.ofNat 2 (by decide))))
      (neg (scaleNat n y))) (log (PositiveRatio.ofNat 2 (by decide))) := by
    rw [add_assoc]
    have commuted := add_left_comm (scaleNat n y) (log (PositiveRatio.ofNat 2 (by decide))) (neg (scaleNat n y))
    have erased := add_congr (equiv_refl (log (PositiveRatio.ofNat 2 (by decide)))) (add_neg (scaleNat n y))
    rw [add_zero] at erased
    exact equiv_trans commuted erased
  simpa only [sub, scaleNat_add, scale_neg] using (le_congr (equiv_refl _) reduced).mp moved

end Thesis.Probability.ExactLog
