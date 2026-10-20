import Thesis.Probability.ExactLog
import Thesis.Probability.SignedRatio

namespace Thesis.Probability.ExactLog

/-- A signed rational number of bits, represented exactly by powers of two.
The two natural exponents avoid normalized rationals and signed exponentiation. -/
def ofSignedRatio (q : SignedRatio) : ExactLog :=
  ⟨⟨2 ^ q.num.toNat, 2 ^ (-q.num).toNat, Nat.pow_pos (by decide), Nat.pow_pos (by decide)⟩,
    q.den, q.den_pos⟩

private theorem signed_cross (a b : Int) (m n : Nat) :
    a.toNat * m + (-b).toNat * n ≤ b.toNat * n + (-a).toNat * m ↔
      a * (m : Int) ≤ b * (n : Int) := by
  have left : (a.toNat : Int) - ((-a).toNat : Int) = a := by omega
  have right : (b.toNat : Int) - ((-b).toNat : Int) = b := by omega
  rw [← Int.ofNat_le]
  simp only [Int.natCast_add, Int.natCast_mul]
  have leftScaled := congrArg (fun z : Int => z * (m : Int)) left
  have rightScaled := congrArg (fun z : Int => z * (n : Int)) right
  simp only [Int.sub_mul] at leftScaled rightScaled
  omega

/-- Rational-bit comparison is the existing integer cross-product comparison. -/
theorem ofSignedRatio_le_iff (a b : SignedRatio) :
    LE (ofSignedRatio a) (ofSignedRatio b) ↔ a.num * (b.den : Int) ≤ b.num * (a.den : Int) := by
  change (2 ^ a.num.toNat) ^ b.den * (2 ^ (-b.num).toNat) ^ a.den ≤
    (2 ^ b.num.toNat) ^ a.den * (2 ^ (-a.num).toNat) ^ b.den ↔ _
  simp only [← Nat.pow_mul, ← Nat.pow_add]
  rw [Nat.pow_le_pow_iff_right (by decide : 1 < 2)]
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
