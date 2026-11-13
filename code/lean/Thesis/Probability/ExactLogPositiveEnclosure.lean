import Thesis.Probability.ExactLogEnclosure
import Thesis.Probability.ExactLogLinear
import Thesis.Probability.ConstructiveInteger
import Thesis.Probability.RationalValues

namespace Thesis.Probability.ExactLog

/-- Nonnegative rational numbers of bits, embedded without changing any
probability weights or claiming that all entropy values are rational. -/
def ofQProb (value : QProb) : ExactLog := ofSignedRatio value.toSignedRatio

theorem ofQProb_add (p q : QProb) : add (ofQProb p) (ofQProb q) = ofQProb (QProb.add p q) := by
  apply ext
  · apply PositiveRatio.ext <;>
      simp only [ofQProb, ofSignedRatio, QProb.toSignedRatio, QProb.add, add, PositiveRatio.mul, PositiveRatio.pow,
        Int.toNat_natCast, Int.toNat_neg_natCast, Nat.pow_zero, Nat.one_pow, Nat.mul_one,
        ← Nat.pow_mul, ← Nat.pow_add]
  · rfl

theorem ofQProb_le_iff (p q : QProb) : LE (ofQProb p) (ofQProb q) ↔ QProb.LE p q := by
  simpa only [ofQProb, QProb.toSignedRatio, ← Int.natCast_mul, Int.ofNat_le] using
    ofSignedRatio_le_iff p.toSignedRatio q.toSignedRatio

theorem ofQProb_zero : ofQProb QProb.zero = zero := rfl

/-- A rational interval for a nonnegative exact log, with both endpoints
nonnegative and width at most the requested rational tolerance. -/
structure NonnegativeEnclosure (x : ExactLog) (tolerance : QProb) where
  lower : QProb
  upper : QProb
  lower_bound : LE (ofQProb lower) x
  upper_bound : LE x (ofQProb upper)
  width_bound : QProb.LE upper (QProb.add lower tolerance)

/-- Clip a possibly negative lower enclosure endpoint at zero, using a proof
that the enclosed value is nonnegative. Upper endpoints remain certified. -/
def encloseNonnegative (x : ExactLog) (nonnegative : LE zero x) (tolerance : QProb)
    (positive : 0 < tolerance.num) : NonnegativeEnclosure x tolerance := by
  let enclosed := enclose x tolerance positive
  have upperNonnegative : 0 ≤ enclosed.lower + (enclosed.width : Int) := by
    have bound := le_trans nonnegative enclosed.upper_bound
    have rational := (ofSignedRatio_le_iff SignedRatio.zero
      ⟨enclosed.lower + (enclosed.width : Int), enclosed.den, enclosed.den_pos⟩).mp bound
    simpa only [SignedRatio.zero, Int.natCast_one, Int.zero_mul, Int.mul_one] using rational
  let lower : QProb := ⟨enclosed.lower.toNat, enclosed.den, enclosed.den_pos⟩
  let upper : QProb := ⟨(enclosed.lower + (enclosed.width : Int)).toNat, enclosed.den, enclosed.den_pos⟩
  have upperCast := ConstructiveInteger.toNat_cast (enclosed.lower + (enclosed.width : Int)) upperNonnegative
  have upperSame : Equiv (ofQProb upper)
      (ofSignedRatio ⟨enclosed.lower + (enclosed.width : Int), enclosed.den, enclosed.den_pos⟩) := by
    apply ofSignedRatio_congr
    change ((enclosed.lower + (enclosed.width : Int)).toNat : Int) * enclosed.den =
      (enclosed.lower + (enclosed.width : Int)) * enclosed.den
    rw [upperCast]
  have lowerBound : LE (ofQProb lower) x := by
    by_cases nonnegativeLower : 0 ≤ enclosed.lower
    · have same : Equiv (ofQProb lower) (ofSignedRatio ⟨enclosed.lower, enclosed.den, enclosed.den_pos⟩) := by
        apply ofSignedRatio_congr
        change (enclosed.lower.toNat : Int) * enclosed.den = enclosed.lower * enclosed.den
        rw [ConstructiveInteger.toNat_cast enclosed.lower nonnegativeLower]
      exact (le_congr same (equiv_refl _)).mpr enclosed.lower_bound
    · have vanished : enclosed.lower.toNat = 0 := by
        cases value : enclosed.lower with
        | ofNat n =>
            have impossible : ¬ 0 ≤ (n : Int) := by simpa only [value] using nonnegativeLower
            exact False.elim (impossible (Int.natCast_nonneg n))
        | negSucc _ => rfl
      have same : Equiv (ofQProb lower) zero := by
        change Equiv (ofSignedRatio lower.toSignedRatio) (ofSignedRatio SignedRatio.zero)
        apply ofSignedRatio_congr
        simp only [SignedRatio.Equiv, lower, QProb.toSignedRatio, vanished, SignedRatio.zero, Int.natCast_zero, Int.zero_mul]
      exact (le_congr same (equiv_refl _)).mpr nonnegative
  have clipped : enclosed.lower ≤ (enclosed.lower.toNat : Int) := by
    cases value : enclosed.lower with
    | ofNat n => exact Int.le_refl _
    | negSucc n => exact Int.le_of_lt (Int.negSucc_lt_zero n)
  have numerators : upper.num ≤ lower.num + enclosed.width := by
    have compared := Int.add_le_add_right clipped (enclosed.width : Int)
    rw [← upperCast] at compared
    exact Int.ofNat_le.mp (by simpa only [Int.natCast_add] using compared)
  have widthBound : QProb.LE upper (QProb.add lower tolerance) := by
    have scaled := Nat.mul_le_mul_right tolerance.den numerators
    rw [Nat.add_mul] at scaled
    have compared := Nat.le_trans scaled (Nat.add_le_add_left (Nat.le_of_lt enclosed.width_lt) _)
    have multiplied := Nat.mul_le_mul_right enclosed.den compared
    simpa only [QProb.LE, QProb.add, lower, upper, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using multiplied
  exact ⟨lower, upper, lowerBound, (le_congr (equiv_refl _) (equiv_symm upperSame)).mp enclosed.upper_bound, widthBound⟩

end Thesis.Probability.ExactLog
