import Thesis.Probability.SignedRatioRangeSum
import Thesis.Probability.RationalSeriesNorm

namespace Thesis.Probability.SignedRatio

/-- Changing the order in which a finite prefix is accumulated preserves
its value. This connects final-term and first-term recursive sums. -/
theorem rangeSum_block (f : Nat → SignedRatio) (n : Nat) : Equiv (rangeSum f n) (RationalGeometricSeries.block f 0 n) := by
  induction n with
  | zero => exact equiv_refl _
  | succ n ih =>
      have split := RationalGeometricSeries.block_split f 0 n 1
      simp only [Nat.zero_add] at split
      exact equiv_trans (add_congr ih (equiv_symm (add_zero (f n)))) (equiv_symm split)

/-- A finite number of signed summands, each with the same certified rational
magnitude bound, has at most that bound times the number of summands. -/
theorem rangeSum_magnitude_bounded (f : Nat → SignedRatio) (n : Nat) (size : QProb)
    (bounded : ∀ k, k < n → QProb.LE (f k).magnitude size) : QProb.LE (rangeSum f n).magnitude (QProb.scale n size) := by
  induction n with
  | zero => simp only [rangeSum, magnitude, zero, QProb.LE, QProb.scale, Nat.zero_mul, Int.natAbs_zero, Nat.le_refl]
  | succ n ih =>
      have estimate := QProb.le_trans (magnitude_add _ _) (QProb.add_le_add
        (ih (fun k hk => bounded k (by omega))) (bounded n (by omega)))
      have collect : QProb.Equiv (QProb.add (QProb.scale n size) size) (QProb.scale (n + 1) size) := by
        simp only [QProb.Equiv, QProb.add, QProb.scale, Nat.add_mul, Nat.one_mul]
        ac_rfl
      exact QProb.le_congr (QProb.equiv_refl _) collect estimate

end Thesis.Probability.SignedRatio

namespace Thesis.Probability.RationalDoubleSum
open SignedRatio RationalGeometricSeries

/-- Square and strict-total-degree triangular finite sums. -/
def square (f : Nat → Nat → SignedRatio) (n : Nat) : SignedRatio :=
  rangeSum (fun i => rangeSum (f i) n) n

def triangle (f : Nat → Nat → SignedRatio) (n : Nat) : SignedRatio :=
  rangeSum (fun i => rangeSum (f i) (n - i)) n

def corner (f : Nat → Nat → SignedRatio) (n : Nat) : SignedRatio :=
  rangeSum (fun i => rangeSum (fun j => f i (n - i + j)) i) n

/-- Adding the next diagonal extends a triangular sum by one total degree. -/
theorem triangle_succ (f : Nat → Nat → SignedRatio) (n : Nat) :
    Equiv (triangle f (n + 1)) (add (triangle f n) (rangeSum (fun i => f i (n - i)) (n + 1))) := by
  have prefixes : Equiv (rangeSum (fun i => rangeSum (f i) (n + 1 - i)) n)
      (add (triangle f n) (rangeSum (fun i => f i (n - i)) n)) := by
    apply equiv_trans (rangeSum_congr _ _ n (fun i within => by
      rw [show n + 1 - i = (n - i) + 1 by omega]
      exact equiv_refl _))
    exact rangeSum_add _ _ _
  have last : Equiv (rangeSum (f n) (n + 1 - n)) (f n (n - n)) := by
    simp only [Nat.add_sub_cancel_left, Nat.sub_self, rangeSum]
    exact zero_add _
  exact equiv_trans (add_congr prefixes last) (add_assoc _ _ _)

/-- Summing successive diagonals equals summing the same finite triangle
by rows. No infinite rearrangement is part of this identity. -/
theorem diagonals (f : Nat → Nat → SignedRatio) (n : Nat) :
    Equiv (rangeSum (fun k => rangeSum (fun i => f i (k - i)) (k + 1)) n) (triangle f n) := by
  induction n with
  | zero => exact equiv_refl _
  | succ n ih => exact equiv_trans (add_congr ih (equiv_refl _)) (equiv_symm (triangle_succ f n))

/-- The square consists of its low-degree triangle and the remaining corner. -/
theorem square_split (f : Nat → Nat → SignedRatio) (n : Nat) : Equiv (square f n) (add (triangle f n) (corner f n)) := by
  have rows : Equiv (square f n)
      (rangeSum (fun i => add (rangeSum (f i) (n - i)) (rangeSum (fun j => f i (n - i + j)) i)) n) := by
    apply rangeSum_congr
    intro i within
    have split := rangeSum_split (f i) (n - i) i
    rw [Nat.sub_add_cancel (by omega : i ≤ n)] at split
    exact split
  exact equiv_trans rows (rangeSum_add _ _ _)

/-- The rectangular sum of a separable kernel is the product of its two
finite sums. Zero and signed factors are all retained. -/
theorem square_product (a b : Nat → SignedRatio) (n : Nat) :
    Equiv (square (fun i j => mul (a i) (b j)) n) (mul (rangeSum a n) (rangeSum b n)) :=
  equiv_trans (rangeSum_congr _ _ n (fun i _ => rangeSum_mul_left (a i) b n)) (rangeSum_mul_right a _ n)

/-- If every entry decays with total degree, the omitted corner has the
explicit polynomial-times-geometric error bound. -/
theorem corner_bound (f : Nat → Nat → SignedRatio) (coefficient n : Nat)
    (bounded : ∀ i j, QProb.LE (f i j).magnitude (envelope coefficient (i + j))) :
    QProb.LE (corner f n).magnitude (QProb.scale (n * n) (envelope coefficient n)) := by
  let size := envelope coefficient n
  have rows : ∀ i, i < n → QProb.LE (rangeSum (fun j => f i (n - i + j)) i).magnitude (QProb.scale n size) := by
    intro i within
    have estimate := rangeSum_magnitude_bounded (fun j => f i (n - i + j)) i size (by
      intro j _
      have exponent : n ≤ i + (n - i + j) := by omega
      have enlarged : QProb.LE (envelope coefficient (i + (n - i + j))) size := by
        exact Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_right (by decide) exponent)
      exact QProb.le_trans (bounded i (n - i + j)) enlarged)
    have count : QProb.LE (QProb.scale i size) (QProb.scale n size) :=
      Nat.mul_le_mul_right size.den (Nat.mul_le_mul_right size.num (Nat.le_of_lt within))
    exact QProb.le_trans estimate count
  have estimate := rangeSum_magnitude_bounded _ n (QProb.scale n size) rows
  have collect : QProb.Equiv (QProb.scale n (QProb.scale n size)) (QProb.scale (n * n) size) := by
    simp only [QProb.Equiv, QProb.scale]; ac_rfl
  exact QProb.le_congr (QProb.equiv_refl _) collect estimate

end Thesis.Probability.RationalDoubleSum
