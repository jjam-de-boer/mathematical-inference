import Thesis.Probability.Core
import Init.Data.Rat.Lemmas

namespace Thesis
namespace Probability
namespace QProb

/-!
# Exact rational values for auxiliary constructive algebra

Probability records and their weights remain unchanged: `QProb` still has
a natural numerator and positive natural denominator, with equality by
cross-multiplication.  This module embeds those values into Lean's concrete
normalized rational type for auxiliary signed linear algebra and polynomial
identities.  It introduces no real numbers or signed probability weights.

The equality bridge is exact in both directions, so changing presentations
does not change values and normalization cannot identify unequal probability
values.  Addition and multiplication commute with the embedding, and every
embedded probability value is nonnegative.  These lemmas are prerequisites,
not a compression theorem or an assumed rational-optimization interface.
-/

/-- A computable normalized rational presentation, using the stored
positive denominator rather than selecting a quotient representative. -/
def toRat (value : QProb) : Rat := mkRat (value.num : Int) value.den

theorem toRat_eq_iff (left right : QProb) : toRat left = toRat right ↔ Equiv left right := by
  unfold toRat
  rw [Rat.mkRat_eq_iff (Nat.ne_of_gt left.den_pos) (Nat.ne_of_gt right.den_pos)]
  simp only [← Int.natCast_mul, Int.ofNat_inj, Equiv]

theorem toRat_congr {left right : QProb} (same : Equiv left right) : toRat left = toRat right :=
  (toRat_eq_iff left right).mpr same

theorem toRat_nonnegative (value : QProb) : 0 ≤ toRat value := by
  unfold toRat
  rw [← Rat.divInt_ofNat]
  exact Rat.divInt_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)

theorem toRat_zero : toRat zero = 0 := by simp [toRat, zero]
theorem toRat_one : toRat one = 1 := by decide +kernel

/-- Normalized rational addition agrees with the original unreduced
cross-denominator operation; no probability representative is discarded. -/
theorem toRat_add (left right : QProb) : toRat (add left right) = toRat left + toRat right := by
  unfold toRat
  rw [Rat.mkRat_add_mkRat _ _ (Nat.ne_of_gt left.den_pos) (Nat.ne_of_gt right.den_pos)]
  simp only [add, Int.natCast_add, Int.natCast_mul]

theorem toRat_mul (left right : QProb) : toRat (mul left right) = toRat left * toRat right := by
  simp only [toRat, mul, Int.natCast_mul, Rat.mkRat_mul_mkRat]

theorem toRat_eq_div (value : QProb) : toRat value = (value.num : Rat) / (value.den : Rat) := by
  exact Rat.mkRat_eq_div (value.num : Int) value.den

end QProb
end Probability
end Thesis
