import Thesis.Probability.ExactLog
import Thesis.Probability.SignedRatio

namespace Thesis.Probability.ExactLog

/-- A signed rational number of bits, represented exactly by powers of two.
The two natural exponents avoid normalized rationals and signed exponentiation. -/
def ofSignedRatio (q : SignedRatio) : ExactLog :=
  ⟨⟨2 ^ q.num.toNat, 2 ^ (-q.num).toNat, Nat.pow_pos (by decide), Nat.pow_pos (by decide)⟩,
    q.den, q.den_pos⟩

private theorem signed_parts (a : Int) : (a.toNat : Int) - ((-a).toNat : Int) = a := by
  cases a with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

private theorem cross_difference (p q r s : Int) : p + s ≤ r + q ↔ p - q ≤ r - s := by
  have left : (p - q) + (q + s) = p + s := by
    rw [← Int.add_assoc, Int.sub_add_cancel]
  have right : (r - s) + (q + s) = r + q := by
    calc
      _ = ((r - s) + s) + q := by ac_rfl
      _ = r + q := by rw [Int.sub_add_cancel]
  calc
    _ ↔ (p - q) + (q + s) ≤ (r - s) + (q + s) := by rw [left, right]
    _ ↔ _ := Int.add_le_add_iff_right (q + s)

private theorem signed_cross (a b : Int) (m n : Nat) :
    a.toNat * m + (-b).toNat * n ≤ b.toNat * n + (-a).toNat * m ↔
      a * (m : Int) ≤ b * (n : Int) := by
  rw [← Int.ofNat_le]
  simp only [Int.natCast_add, Int.natCast_mul]
  rw [cross_difference, ← Int.sub_mul, ← Int.sub_mul, signed_parts a, signed_parts b]

private theorem two_pow_le_iff (m n : Nat) : 2 ^ m ≤ 2 ^ n ↔ m ≤ n := by
  constructor
  · intro bounded
    by_cases compared : m ≤ n
    · exact compared
    · exact False.elim (Nat.not_le_of_gt (Nat.pow_lt_pow_of_lt (by decide : 1 < 2)
        (Nat.lt_of_not_ge compared)) bounded)
  · intro compared
    exact Nat.pow_le_pow_right (by decide : 0 < 2) compared

/-- Rational-bit comparison is the existing integer cross-product comparison. -/
theorem ofSignedRatio_le_iff (a b : SignedRatio) :
    LE (ofSignedRatio a) (ofSignedRatio b) ↔ a.num * (b.den : Int) ≤ b.num * (a.den : Int) := by
  change (2 ^ a.num.toNat) ^ b.den * (2 ^ (-b.num).toNat) ^ a.den ≤
    (2 ^ b.num.toNat) ^ a.den * (2 ^ (-a.num).toNat) ^ b.den ↔ _
  simp only [← Nat.pow_mul, ← Nat.pow_add]
  rw [two_pow_le_iff]
  exact signed_cross _ _ _ _

theorem ofSignedRatio_equiv_iff (a b : SignedRatio) :
    Equiv (ofSignedRatio a) (ofSignedRatio b) ↔ SignedRatio.Equiv a b := by
  rw [equiv_iff_le, ofSignedRatio_le_iff, ofSignedRatio_le_iff]
  exact ⟨fun h => Int.le_antisymm h.1 h.2, fun h => ⟨Int.le_of_eq h, Int.le_of_eq h.symm⟩⟩

theorem ofSignedRatio_congr {a b : SignedRatio} (same : SignedRatio.Equiv a b) :
    Equiv (ofSignedRatio a) (ofSignedRatio b) := (ofSignedRatio_equiv_iff a b).mpr same

theorem ofSignedRatio_zero : ofSignedRatio SignedRatio.zero = zero := rfl

/-- A simple finite initial upper bound; no search or analytic logarithm is used. -/
theorem natural_upper (x : ExactLog) :
    LE x (ofSignedRatio ⟨((x.argument.num.log2 + 1 : Nat) : Int), 1, Nat.zero_lt_one⟩) := by
  change x.argument.num ^ 1 * (2 ^ (-((x.argument.num.log2 + 1 : Nat) : Int)).toNat) ^ x.degree ≤
    (2 ^ ((x.argument.num.log2 + 1 : Nat) : Int).toNat) ^ x.degree * x.argument.den ^ 1
  simp only [Int.toNat_neg_natCast, Int.toNat_natCast, Nat.pow_zero, Nat.one_pow, Nat.pow_one, Nat.mul_one]
  have initial : x.argument.num ≤ 2 ^ (x.argument.num.log2 + 1) := Nat.le_of_lt Nat.lt_log2_self
  have raised : 2 ^ (x.argument.num.log2 + 1) ≤ (2 ^ (x.argument.num.log2 + 1)) ^ x.degree := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.pow_pos (by decide : 0 < 2))
      (show 1 ≤ x.degree from x.degree_pos)
  exact Nat.le_trans (Nat.le_trans initial raised) (Nat.le_mul_of_pos_right _ x.argument.den_pos)

/-- The reciprocal gives a finite initial lower bound, including values below zero. -/
theorem natural_lower (x : ExactLog) :
    LE (ofSignedRatio ⟨-((x.argument.den.log2 + 1 : Nat) : Int), 1, Nat.zero_lt_one⟩) x := by
  change (2 ^ (-((x.argument.den.log2 + 1 : Nat) : Int)).toNat) ^ x.degree * x.argument.den ^ 1 ≤
    x.argument.num ^ 1 * (2 ^ (- -((x.argument.den.log2 + 1 : Nat) : Int)).toNat) ^ x.degree
  simp only [Int.toNat_neg_natCast, Int.toNat_natCast, Int.neg_neg, Nat.pow_zero,
    Nat.one_pow, Nat.pow_one, Nat.one_mul]
  have initial : x.argument.den ≤ 2 ^ (x.argument.den.log2 + 1) := Nat.le_of_lt Nat.lt_log2_self
  have raised : 2 ^ (x.argument.den.log2 + 1) ≤ (2 ^ (x.argument.den.log2 + 1)) ^ x.degree := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.pow_pos (by decide : 0 < 2))
      (show 1 ≤ x.degree from x.degree_pos)
  exact Nat.le_trans (Nat.le_trans initial raised) (Nat.le_mul_of_pos_left _ x.argument.num_pos)

end Thesis.Probability.ExactLog
