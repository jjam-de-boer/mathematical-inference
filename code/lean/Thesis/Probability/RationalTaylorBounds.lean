import Thesis.Probability.RationalExponential
import Thesis.Probability.RationalSeriesNorm

namespace Thesis.Probability.RationalTaylorExponential
open SignedRatio RationalGeometricSeries

/-- Nonnegative Taylor coefficients at a natural argument bound. They also
bound signed coefficients throughout the corresponding rational interval. -/
def coefficient (bound n : Nat) : QProb := ⟨bound ^ n, factorial n, factorial_pos n⟩

theorem coefficient_step (bound n : Nat) :
    QProb.Equiv (QProb.mul (QProb.mul (QProb.ofNat bound) (coefficient bound n)) ⟨1, n + 1, Nat.zero_lt_succ n⟩)
      (coefficient bound (n + 1)) := by
  simp only [QProb.Equiv, QProb.mul, QProb.ofNat, coefficient, factorial, Nat.pow_succ, Nat.mul_one, Nat.one_mul]
  ac_rfl

theorem term_coefficient_bound (x : SignedRatio) (bound : Nat) (bounded : QProb.LE x.magnitude (QProb.ofNat bound)) (n : Nat) :
    QProb.LE (term x n).magnitude (coefficient bound n) := by
  induction n with
  | zero => exact QProb.le_refl _
  | succ n ih =>
      have estimate := QProb.mul_le_mul (QProb.mul_le_mul bounded ih) (QProb.le_refl (⟨1, n + 1, Nat.zero_lt_succ n⟩ : QProb))
      exact QProb.le_congr (QProb.equiv_symm (magnitude_divideNat _ _ _)) (coefficient_step bound n)
        (QProb.le_congr (QProb.mul_congr (QProb.equiv_symm (magnitude_mul _ _)) (QProb.equiv_refl _)) (QProb.equiv_refl _) estimate)

private theorem coefficient_coarse (bound n : Nat) :
    QProb.LE (coefficient bound n) (QProb.ofNat ((bound + 1) ^ n)) := by
  change bound ^ n * 1 ≤ (bound + 1) ^ n * factorial n
  rw [Nat.mul_one]
  exact Nat.le_trans (Nat.pow_le_pow_left (by omega) n) (Nat.le_mul_of_pos_right _ (factorial_pos n))

/-- A common tail schedule for every argument of magnitude at most `bound`.
Unlike the pointwise schedule, this data can be used in continuity moduli. -/
def uniformOffset (bound : Nat) : Nat := 2 * bound

def uniformCoefficient (bound : Nat) : Nat := (bound + 1) ^ uniformOffset bound

def uniformSumBound (bound : Nat) : Nat := (uniformOffset bound + 2) * uniformCoefficient bound

theorem uniformSumBound_pos (bound : Nat) : 0 < uniformSumBound bound :=
  Nat.mul_pos (by omega) (Nat.pow_pos (Nat.zero_lt_succ bound))

private theorem uniform_ratio (bound n : Nat) :
    QProb.LE (QProb.mul (QProb.ofNat bound) (⟨1, uniformOffset bound + n + 1, Nat.zero_lt_succ _⟩ : QProb)) ⟨1, 2, by decide⟩ := by
  change (bound * 1) * 2 ≤ 1 * (1 * (uniformOffset bound + n + 1))
  simp only [Nat.mul_one, Nat.one_mul, uniformOffset]
  omega

theorem coefficient_tail_bound (bound n : Nat) :
    QProb.LE (coefficient bound (uniformOffset bound + n)) (envelope (uniformCoefficient bound) n) := by
  induction n with
  | zero => exact coefficient_coarse bound (uniformOffset bound)
  | succ n ih =>
      have rearrange : QProb.Equiv (coefficient bound (uniformOffset bound + n + 1))
          (QProb.mul (coefficient bound (uniformOffset bound + n))
            (QProb.mul (QProb.ofNat bound) (⟨1, uniformOffset bound + n + 1, Nat.zero_lt_succ _⟩ : QProb))) :=
        QProb.equiv_trans (QProb.equiv_symm (coefficient_step bound (uniformOffset bound + n)))
          (QProb.equiv_trans (QProb.mul_congr (QProb.mul_comm _ _) (QProb.equiv_refl _)) (QProb.mul_assoc _ _ _))
      have collect : QProb.Equiv (QProb.mul (envelope (uniformCoefficient bound) n) (⟨1, 2, by decide⟩ : QProb))
          (envelope (uniformCoefficient bound) (n + 1)) := by
        simp only [QProb.Equiv, QProb.mul, envelope, Nat.mul_one, Nat.pow_succ]
      exact QProb.le_congr (QProb.equiv_symm rearrange) collect (QProb.mul_le_mul ih (uniform_ratio bound n))

private theorem coefficient_prefix_bound (bound count : Nat) (before : count ≤ uniformOffset bound) :
    QProb.LE (normSum (coefficient bound) 0 count) (QProb.ofNat (uniformOffset bound * uniformCoefficient bound)) := by
  have estimate := normSum_constant_bound (coefficient bound) (uniformCoefficient bound) 0 count (by
    intro n _ upper
    exact QProb.le_trans (coefficient_coarse bound n) (by
      change (bound + 1) ^ n * 1 ≤ uniformCoefficient bound * 1
      simpa only [Nat.mul_one] using Nat.pow_le_pow_right (by omega : 0 < bound + 1) (by omega : n ≤ uniformOffset bound)))
  exact QProb.le_trans estimate (by simpa only [QProb.LE, QProb.ofNat, Nat.mul_one] using Nat.mul_le_mul_right (uniformCoefficient bound) before)

/-- All finite absolute Taylor sums on a bounded rational interval admit one
explicit natural bound. A zero radius and empty sums are included. -/
theorem coefficient_sum_bound (bound count : Nat) :
    QProb.LE (normSum (coefficient bound) 0 count) (QProb.ofNat (uniformSumBound bound)) := by
  by_cases before : count ≤ uniformOffset bound
  · exact QProb.le_trans (coefficient_prefix_bound bound count before)
      (by simpa only [QProb.LE, QProb.ofNat, Nat.mul_one, uniformSumBound] using Nat.mul_le_mul_right (uniformCoefficient bound) (Nat.le_add_right (uniformOffset bound) 2))
  · have after : uniformOffset bound ≤ count := by omega
    have split := normSum_split (coefficient bound) 0 (uniformOffset bound) (count - uniformOffset bound)
    simp only [Nat.zero_add, Nat.add_sub_of_le after] at split
    have tail := normSum_geometric_bound (fun n => coefficient bound (uniformOffset bound + n))
      (uniformCoefficient bound) (coefficient_tail_bound bound) 0 (count - uniformOffset bound)
    have shifted := normSum_shift (coefficient bound) (uniformOffset bound) 0 (count - uniformOffset bound)
    simp only [Nat.add_zero] at shifted
    have estimate := QProb.add_le_add (coefficient_prefix_bound bound (uniformOffset bound) (Nat.le_refl _))
      (QProb.le_congr shifted (QProb.equiv_refl _) tail)
    have collect : QProb.Equiv
        (QProb.add (QProb.ofNat (uniformOffset bound * uniformCoefficient bound)) (envelope (2 * uniformCoefficient bound) 0))
        (QProb.ofNat (uniformSumBound bound)) := by
      simp only [QProb.Equiv, QProb.add, QProb.ofNat, envelope, Nat.pow_zero, Nat.mul_one, uniformSumBound, Nat.add_mul]
    exact QProb.le_congr (QProb.equiv_symm split) collect estimate

end Thesis.Probability.RationalTaylorExponential
