import Thesis.Probability.RationalTaylorBounds

namespace Thesis.Probability.RationalTaylorExponential
open SignedRatio RationalGeometricSeries

/-- Enlarging the dyadic coefficient absorbs the finite Taylor prefix. -/
def geometricCoefficient (bound : Nat) : Nat := uniformCoefficient bound * 2 ^ uniformOffset bound

/-- A global dyadic bound for every Taylor coefficient, with the prefix
included. It is uniform in all signed rational arguments of the given size. -/
theorem coefficient_global_bound (bound n : Nat) :
    QProb.LE (coefficient bound n) (envelope (geometricCoefficient bound) n) := by
  by_cases before : n ≤ uniformOffset bound
  · have coarse : QProb.LE (coefficient bound n) (QProb.ofNat (uniformCoefficient bound)) := by
      change bound ^ n * 1 ≤ uniformCoefficient bound * factorial n
      rw [Nat.mul_one]
      exact Nat.le_trans (Nat.le_trans (Nat.pow_le_pow_left (by omega : bound ≤ bound + 1) n)
        (Nat.pow_le_pow_right (by omega) before)) (Nat.le_mul_of_pos_right _ (factorial_pos n))
    have enlarged : QProb.LE (QProb.ofNat (uniformCoefficient bound)) (envelope (geometricCoefficient bound) n) := by
      change uniformCoefficient bound * 2 ^ n ≤ geometricCoefficient bound * 1
      rw [Nat.mul_one]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) before)
    exact QProb.le_trans coarse enlarged
  · have after : uniformOffset bound ≤ n := by omega
    have tail := coefficient_tail_bound bound (n - uniformOffset bound)
    simp only [Nat.add_sub_of_le after] at tail
    have powers : 2 ^ n = 2 ^ uniformOffset bound * 2 ^ (n - uniformOffset bound) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le after]
    have same : QProb.Equiv (envelope (uniformCoefficient bound) (n - uniformOffset bound))
        (envelope (geometricCoefficient bound) n) := by
      simp only [QProb.Equiv, envelope, geometricCoefficient, powers]
      ac_rfl
    exact QProb.le_congr (QProb.equiv_refl _) same tail

theorem term_global_bound (x : SignedRatio) (bound : Nat) (bounded : QProb.LE x.magnitude (QProb.ofNat bound)) (n : Nat) :
    QProb.LE (term x n).magnitude (envelope (geometricCoefficient bound) n) :=
  QProb.le_trans (term_coefficient_bound x bound bounded n) (coefficient_global_bound bound n)

end Thesis.Probability.RationalTaylorExponential
