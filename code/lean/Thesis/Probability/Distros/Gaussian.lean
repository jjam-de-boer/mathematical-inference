import Thesis.Probability.Distros.LimitAnalogs
import Thesis.Probability.Distros.Categorical

namespace Thesis
namespace Probability
namespace Distros

/-!
The exact rational kernel and boundary laws of the finite lattice Gaussian.
The constructor clears a single positive common denominator, so the use of
natural atom weights preserves the kernel rather than reversing its shape.
-/

open Combinatorics

/-- Every cleared weight is the intended rational kernel on the same
positive common denominator. -/
theorem discreteGaussianWeight_kernel (radius : Nat) (q : QProb)
    (k : Fin (2 * radius + 1)) :
    QProb.Equiv (qpow q (natSqDiff k.val radius))
      ⟨discreteGaussianWeight radius q k, q.den ^ (radius * radius),
        Nat.pow_pos q.den_pos⟩ := by
  simpa [QProb.scale, discreteGaussianWeight] using
    scale_qpow_homogenize q (radius * radius) (natSqDiff k.val radius) 1
      (natSqDiff_window radius k.val k.isLt)

/-- A bounded kernel has its greatest weight at the centre. -/
theorem discreteGaussianWeight_le_center (radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) (k : Fin (2 * radius + 1)) :
    discreteGaussianWeight radius q k ≤ q.den ^ (radius * radius) := by
  have hbase : q.num ≤ q.den := by simpa [QProb.LE, QProb.one] using bounded
  have hsq := natSqDiff_window radius k.val k.isLt
  calc
    discreteGaussianWeight radius q k
        ≤ q.den ^ natSqDiff k.val radius *
          q.den ^ (radius * radius - natSqDiff k.val radius) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hbase _)
    _ = q.den ^ (radius * radius) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hsq]

/-- Weights decrease as the squared distance from the centre increases. -/
theorem discreteGaussianWeight_antitone_distance (radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) (k j : Fin (2 * radius + 1))
    (distance : natSqDiff k.val radius ≤ natSqDiff j.val radius) :
    discreteGaussianWeight radius q j ≤ discreteGaussianWeight radius q k := by
  have hbase : q.num ≤ q.den := by simpa [QProb.LE, QProb.one] using bounded
  have hjsq := natSqDiff_window radius j.val j.isLt
  have hsplit : natSqDiff j.val radius =
      natSqDiff k.val radius + (natSqDiff j.val radius - natSqDiff k.val radius) := by
    omega
  have hrest : radius * radius - natSqDiff k.val radius =
      (natSqDiff j.val radius - natSqDiff k.val radius) +
        (radius * radius - natSqDiff j.val radius) := by omega
  unfold discreteGaussianWeight
  conv => lhs; lhs; rw [hsplit, Nat.pow_add]
  conv => rhs; rhs; rw [hrest, Nat.pow_add]
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    Nat.mul_le_mul_left
      (q.num ^ natSqDiff k.val radius *
        q.den ^ (radius * radius - natSqDiff j.val radius))
      (Nat.pow_le_pow_left hbase
        (natSqDiff j.val radius - natSqDiff k.val radius))

theorem discreteGaussianWeight_zero (radius : Nat) (k : Fin (2 * radius + 1)) :
    discreteGaussianWeight radius QProb.zero k =
      if k.val = radius then 1 else 0 := by
  by_cases hk : k.val = radius
  · simp [discreteGaussianWeight, QProb.zero, hk, natSqDiff_self]
  · have hsq : 0 < natSqDiff k.val radius := by
      have hne : natSqDiff k.val radius ≠ 0 :=
        fun h => hk ((natSqDiff_eq_zero_iff k.val radius).mp h)
      omega
    simp [discreteGaussianWeight, QProb.zero, Nat.zero_pow hsq, hk]

theorem discreteGaussian_zero_den (radius : Nat) :
    (discreteGaussianDistro radius QProb.zero (QProb.zero_le _)).record.den = 1 := by
  rw [discreteGaussian_den]
  have hcongr :
      natSum (2 * radius + 1) (finWeight (discreteGaussianWeight radius QProb.zero)) =
        natSum (2 * radius + 1) (fun i => (if i = radius then 1 else 0) * 1) := by
    apply natSum_congr
    intro i hi
    simp [finWeight, hi, discreteGaussianWeight_zero]
  rw [hcongr, natSum_spike]
  simp [radius_lt_window]

/-- The zero kernel is a point mass at the centre. -/
theorem discreteGaussian_zero_pmf (radius : Nat) (k : Fin (2 * radius + 1)) :
    QProb.Equiv
      ((discreteGaussianDistro radius QProb.zero (QProb.zero_le _)).pmf k)
      (if k.val = radius then QProb.one else QProb.zero) := by
  refine QProb.equiv_trans (discreteGaussian_pmf radius QProb.zero _ k) ?_
  simp [QProb.Equiv, discreteGaussianWeight_zero, discreteGaussian_zero_den]
  split <;> simp_all [QProb.one, QProb.zero]

theorem discreteGaussianWeight_one (radius : Nat) (k : Fin (2 * radius + 1)) :
    discreteGaussianWeight radius QProb.one k = 1 := by
  simp [discreteGaussianWeight, QProb.one]

/-- The unit kernel is exactly the existing discrete-uniform constructor. -/
theorem discreteGaussian_one_eq_uniform (radius : Nat) :
    discreteGaussianDistro radius QProb.one (QProb.le_refl _) =
      discreteUniformDistro (2 * radius + 1) (Nat.succ_pos _) := by
  have hw : discreteGaussianWeight radius QProb.one = fun _ => 1 :=
    funext (discreteGaussianWeight_one radius)
  simp [discreteGaussianDistro, discreteUniformDistro, categoricalDistro, hw]

theorem discreteGaussian_one_pmf (radius : Nat) (k : Fin (2 * radius + 1)) :
    QProb.Equiv
      ((discreteGaussianDistro radius QProb.one (QProb.le_refl _)).pmf k)
      ⟨1, 2 * radius + 1, Nat.succ_pos _⟩ := by
  rw [discreteGaussian_one_eq_uniform]
  exact discreteUniform_pmf _ _ k

end Distros
end Probability
end Thesis
