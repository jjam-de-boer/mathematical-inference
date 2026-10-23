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

end Thesis.Probability.PositiveRatio

