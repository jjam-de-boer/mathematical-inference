import Thesis.Probability.RationalApproximation
import Thesis.Probability.QProbOrder

namespace Thesis.Probability.PositiveRatio

def capOne (precision : PositiveRatio) : PositiveRatio := if LE precision one then precision else one

theorem capOne_le (precision : PositiveRatio) : LE precision.capOne precision := by
  by_cases small : LE precision one
  · simp only [capOne, small, ↓reduceIte]
    exact le_refl _
  · simp only [capOne, small, ↓reduceIte]
    exact (le_total precision one).resolve_left small

theorem capOne_le_one (precision : PositiveRatio) : LE precision.capOne one := by
  by_cases small : LE precision one
  · simp only [capOne, small, ↓reduceIte]
  · simp only [capOne, small, ↓reduceIte]
    exact le_refl _

def divideNat (precision : PositiveRatio) (factor : Nat) (positive : 0 < factor) : PositiveRatio :=
  ⟨precision.num, precision.den * factor, precision.num_pos, Nat.mul_pos precision.den_pos positive⟩

theorem divideNat_le (precision : PositiveRatio) (factor : Nat) (positive : 0 < factor) :
    LE (precision.divideNat factor positive) precision := by
  simpa only [LE, toQProb, divideNat, QProb.LE, Nat.mul_assoc] using
    (Nat.le_mul_of_pos_right (precision.num * precision.den) positive)

theorem capped_divide_mul (precision : PositiveRatio) (factor : Nat) (positive : 0 < factor) :
    QProb.LE (QProb.mul (precision.divideNat factor positive).capOne.toQProb (QProb.ofNat factor)) precision.toQProb := by
  have bounded := capOne_le (precision.divideNat factor positive)
  simpa only [LE, toQProb, divideNat, QProb.LE, QProb.mul, QProb.ofNat, Nat.mul_one, Nat.one_mul,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using bounded

theorem divide_mul (precision : PositiveRatio) (factor : Nat) (positive : 0 < factor) :
    QProb.Equiv (QProb.mul (precision.divideNat factor positive).toQProb (QProb.ofNat factor)) precision.toQProb := by
  simp only [QProb.Equiv, QProb.mul, toQProb, divideNat, QProb.ofNat, Nat.mul_one]
  ac_rfl


/-- A decreasing rational accuracy schedule with an explicit index bound
for every positive rational tolerance. -/
def unitPrecision (n : Nat) : PositiveRatio := ⟨1, n + 1, by decide, Nat.zero_lt_succ n⟩

theorem unitPrecision_le (precision : PositiveRatio) (n : Nat) (later : precision.den ≤ n) :
    LE (unitPrecision n) precision := by
  change 1 * precision.den ≤ precision.num * (n + 1)
  rw [Nat.one_mul]
  exact Nat.le_trans (by omega) (Nat.le_mul_of_pos_left _ precision.num_pos)


theorem unitPrecision_le_one (n : Nat) : LE (unitPrecision n) one := by
  change 1 ≤ 1 * (n + 1)
  omega

end Thesis.Probability.PositiveRatio

