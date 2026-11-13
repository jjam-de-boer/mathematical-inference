import Thesis.Probability.RationalSeriesTail

namespace Thesis.Probability.RationalGeometricSeries
open SignedRatio

/-- Finite sums of nonnegative rational bounds for a signed series. -/
def normSum (sizes : Nat → QProb) (start : Nat) : Nat → QProb
  | 0 => QProb.zero
  | count + 1 => QProb.add (sizes start) (normSum sizes (start + 1) count)

theorem block_magnitude (terms : Nat → SignedRatio) (sizes : Nat → QProb)
    (bounded : ∀ n, QProb.LE (terms n).magnitude (sizes n)) (start count : Nat) :
    QProb.LE (block terms start count).magnitude (normSum sizes start count) := by
  induction count generalizing start with
  | zero => exact QProb.le_refl _
  | succ count ih => exact QProb.le_trans (magnitude_add _ _) (QProb.add_le_add (bounded start) (ih (start + 1)))

theorem normSum_split (sizes : Nat → QProb) (start first second : Nat) :
    QProb.Equiv (normSum sizes start (first + second))
      (QProb.add (normSum sizes start first) (normSum sizes (start + first) second)) := by
  induction first generalizing start with
  | zero => simp only [Nat.zero_add, Nat.add_zero, normSum, QProb.Equiv, QProb.add, QProb.zero, Nat.zero_mul, Nat.one_mul, Nat.mul_one]
  | succ first ih =>
      simp only [Nat.succ_add, normSum]
      rw [show start + (first + 1) = (start + 1) + first by omega]
      exact QProb.equiv_trans (QProb.add_congr (QProb.equiv_refl _) (ih (start + 1))) (QProb.equiv_symm (QProb.add_assoc _ _ _))

theorem normSum_mul (sizes : Nat → QProb) (factor : QProb) (start count : Nat) :
    QProb.Equiv (normSum (fun n => QProb.mul factor (sizes n)) start count) (QProb.mul factor (normSum sizes start count)) := by
  induction count generalizing start with
  | zero => simp only [normSum, QProb.Equiv, QProb.mul, QProb.zero, Nat.zero_mul, Nat.mul_zero]
  | succ count ih => exact QProb.equiv_trans (QProb.add_congr (QProb.equiv_refl _) (ih (start + 1))) (QProb.equiv_symm (QProb.mul_add_distrib _ _ _))

theorem normSum_constant_bound (sizes : Nat → QProb) (size start count : Nat)
    (bounded : ∀ n, start ≤ n → n < start + count → QProb.LE (sizes n) (QProb.ofNat size)) :
    QProb.LE (normSum sizes start count) (QProb.ofNat (count * size)) := by
  induction count generalizing start with
  | zero => simp only [normSum, Nat.zero_mul, QProb.LE, QProb.zero, QProb.ofNat, Nat.le_refl]
  | succ count ih =>
      have estimate := QProb.add_le_add (bounded start (Nat.le_refl _) (by omega))
        (ih (start + 1) (fun n lower upper => bounded n (by omega) (by omega)))
      have collect : QProb.Equiv (QProb.add (QProb.ofNat size) (QProb.ofNat (count * size))) (QProb.ofNat ((count + 1) * size)) := by
        simp only [QProb.Equiv, QProb.add, QProb.ofNat, Nat.mul_one, Nat.one_mul, Nat.add_mul]
        omega
      exact QProb.le_congr (QProb.equiv_refl _) collect estimate

/-- Dyadic bounds also control the sum of absolute values, so later
continuity estimates do not rely on cancellation in signed partial sums. -/
theorem normSum_geometric_bound (sizes : Nat → QProb) (coefficient : Nat)
    (bounded : ∀ n, QProb.LE (sizes n) (envelope coefficient n)) (start count : Nat) :
    QProb.LE (normSum sizes start count) (envelope (2 * coefficient) start) := by
  induction count generalizing start with
  | zero => exact QProb.zero_le _
  | succ count ih =>
      have estimate := QProb.add_le_add (bounded start) (ih (start + 1))
      have collect : QProb.Equiv (QProb.add (envelope coefficient start) (envelope (2 * coefficient) (start + 1)))
          (envelope (2 * coefficient) start) := by
        simp only [QProb.Equiv, QProb.add, envelope, Nat.pow_succ, Nat.two_mul, Nat.mul_two, Nat.mul_add, Nat.add_mul]
        ac_rfl
      exact QProb.le_congr (QProb.equiv_refl _) collect estimate

theorem normSum_shift (sizes : Nat → QProb) (offset start count : Nat) :
    QProb.Equiv (normSum (fun n => sizes (offset + n)) start count) (normSum sizes (offset + start) count) := by
  induction count generalizing start with
  | zero => exact QProb.equiv_refl _
  | succ count ih => simpa only [normSum, Nat.add_assoc] using QProb.add_congr (QProb.equiv_refl (sizes (offset + start))) (ih (start + 1))

end Thesis.Probability.RationalGeometricSeries
