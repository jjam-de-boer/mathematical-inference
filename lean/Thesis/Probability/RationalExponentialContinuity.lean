import Thesis.Probability.RationalTaylorBounds
import Thesis.Probability.ConstructiveRealScaling

namespace Thesis.Probability.RationalGeometricSeries
open SignedRatio

theorem block_sub (first second : Nat → SignedRatio) (start count : Nat) :
    Equiv (sub (block first start count) (block second start count))
      (block (fun n => sub (first n) (second n)) start count) := by
  induction count generalizing start with
  | zero => exact (sub_equiv_zero_iff _ _).mpr (equiv_refl _)
  | succ count ih =>
      exact equiv_trans (sub_add_sub _ _ _ _) (add_congr (equiv_refl _) (ih (start + 1)))

end Thesis.Probability.RationalGeometricSeries

namespace Thesis.Probability.RationalTaylorExponential
open SignedRatio RationalGeometricSeries

private theorem term_one (x : SignedRatio) : Equiv (term x 1) x := by
  simp only [term, Equiv, mul, one, divideNat, Nat.mul_one, Int.mul_one, Nat.zero_add]

private theorem coefficient_derivative_step (bound n : Nat) :
    QProb.Equiv
      (QProb.mul (QProb.add (coefficient bound (n + 1)) (QProb.mul (QProb.ofNat bound) (coefficient bound n)))
        ⟨1, n + 2, Nat.zero_lt_succ _⟩)
      (coefficient bound (n + 1)) := by
  simp only [QProb.Equiv, QProb.mul, QProb.add, QProb.ofNat, coefficient, factorial, Nat.pow_succ,
    Nat.mul_one, Nat.one_mul, Nat.mul_add, Nat.add_mul, Nat.mul_two]
  ac_rfl

/-- Finite Taylor coefficient differences obey the derivative-sized bound,
proved algebraically before any real differentiation rule is available. -/
theorem term_difference_bound (x y : SignedRatio) (bound : Nat)
    (boundedX : QProb.LE x.magnitude (QProb.ofNat bound)) (boundedY : QProb.LE y.magnitude (QProb.ofNat bound)) (n : Nat) :
    QProb.LE (sub (term x (n + 1)) (term y (n + 1))).magnitude
      (QProb.mul (sub x y).magnitude (coefficient bound n)) := by
  induction n with
  | zero =>
      have same := magnitude_congr (add_congr (term_one x) (neg_congr (term_one y)))
      exact QProb.le_congr (QProb.equiv_symm same) (QProb.equiv_symm (QProb.mul_one _)) (QProb.le_refl _)
  | succ n ih =>
      have division : Equiv (sub (term x (n + 2)) (term y (n + 2)))
          (divideNat (sub (mul x (term x (n + 1))) (mul y (term y (n + 1)))) (n + 2) (Nat.zero_lt_succ _)) :=
        equiv_symm (divideNat_add _ _ _ _)
      have product := product_error_bound x (term x (n + 1)) y (term y (n + 1))
        (sub x y).magnitude (QProb.mul (sub x y).magnitude (coefficient bound n))
        (QProb.ofNat bound) (coefficient bound (n + 1))
        (QProb.le_refl _) ih boundedY (term_coefficient_bound x bound boundedX (n + 1))
      have estimate := QProb.mul_le_mul product (QProb.le_refl (⟨1, n + 2, Nat.zero_lt_succ _⟩ : QProb))
      have collect : QProb.Equiv
          (QProb.mul
            (QProb.add (QProb.mul (sub x y).magnitude (coefficient bound (n + 1)))
              (QProb.mul (QProb.ofNat bound) (QProb.mul (sub x y).magnitude (coefficient bound n))))
            ⟨1, n + 2, Nat.zero_lt_succ _⟩)
          (QProb.mul (sub x y).magnitude (coefficient bound (n + 1))) := by
        have factor : QProb.Equiv
            (QProb.add (QProb.mul (sub x y).magnitude (coefficient bound (n + 1)))
              (QProb.mul (QProb.ofNat bound) (QProb.mul (sub x y).magnitude (coefficient bound n))))
            (QProb.mul (sub x y).magnitude
              (QProb.add (coefficient bound (n + 1)) (QProb.mul (QProb.ofNat bound) (coefficient bound n)))) := by
          exact QProb.equiv_trans (QProb.add_congr (QProb.equiv_refl _)
            (QProb.equiv_trans (QProb.equiv_symm (QProb.mul_assoc _ _ _))
              (QProb.equiv_trans (QProb.mul_congr (QProb.mul_comm _ _) (QProb.equiv_refl _)) (QProb.mul_assoc _ _ _))))
            (QProb.equiv_symm (QProb.mul_add_distrib _ _ _))
        exact QProb.equiv_trans (QProb.mul_congr factor (QProb.equiv_refl _))
          (QProb.equiv_trans (QProb.mul_assoc _ _ _) (QProb.mul_congr (QProb.equiv_refl _) (coefficient_derivative_step bound n)))
      exact QProb.le_congr
        (QProb.equiv_symm (QProb.equiv_trans (magnitude_congr division) (magnitude_divideNat _ _ _))) collect estimate

/-- A single Lipschitz constant controls every finite Taylor truncation on
a bounded interval, independently of the truncation order. -/
theorem partial_difference_bound (x y : SignedRatio) (bound : Nat)
    (boundedX : QProb.LE x.magnitude (QProb.ofNat bound)) (boundedY : QProb.LE y.magnitude (QProb.ofNat bound)) (count : Nat) :
    QProb.LE (sub (partialSum (term x) count) (partialSum (term y) count)).magnitude
      (QProb.mul (sub x y).magnitude (QProb.ofNat (uniformSumBound bound))) := by
  cases count with
  | zero =>
      have vanished := magnitude_congr ((sub_equiv_zero_iff zero zero).mpr (equiv_refl _))
      exact QProb.le_congr (QProb.equiv_symm vanished) (QProb.equiv_refl _) (QProb.zero_le _)
  | succ count =>
      have cancel : Equiv (sub (partialSum (term x) (count + 1)) (partialSum (term y) (count + 1)))
          (block (fun n => sub (term x (n + 1)) (term y (n + 1))) 0 count) := by
        have split := block_sub (term x) (term y) 0 (count + 1)
        have shifted := block_shift (fun n => sub (term x n) (term y n)) 1 0 count
        simp only [Nat.add_zero, Nat.add_comm 1] at shifted
        exact equiv_trans split (equiv_trans (add_congr ((sub_equiv_zero_iff one one).mpr (equiv_refl _))
          (equiv_symm shifted)) (zero_add _))
      have estimate := block_magnitude (fun n => sub (term x (n + 1)) (term y (n + 1)))
        (fun n => QProb.mul (sub x y).magnitude (coefficient bound n)) (term_difference_bound x y bound boundedX boundedY) 0 count
      have collected := QProb.le_congr (QProb.equiv_refl _)
        (normSum_mul (coefficient bound) (sub x y).magnitude 0 count) estimate
      exact QProb.le_congr (QProb.equiv_symm (magnitude_congr cancel)) (QProb.equiv_refl _)
        (QProb.le_trans collected (QProb.mul_le_mul (QProb.le_refl _) (coefficient_sum_bound bound count)))

end Thesis.Probability.RationalTaylorExponential

namespace Thesis.Probability.RationalExponential
open ConstructiveReal

/-- Local uniform continuity of the completed rational exponential, with an
explicit natural Lipschitz constant on every bounded rational interval. -/
theorem exp_within (x y : SignedRatio) (bound : Nat)
    (boundedX : QProb.LE x.magnitude (QProb.ofNat bound)) (boundedY : QProb.LE y.magnitude (QProb.ofNat bound)) :
    Within (QProb.mul (SignedRatio.sub x y).magnitude (QProb.ofNat (RationalTaylorExponential.uniformSumBound bound))) (exp x) (exp y) := by
  have compared := RealCauchySequence.limit_within_of_tail (sequence x).toReal (sequence y).toReal
    (QProb.mul (SignedRatio.sub x y).magnitude (QProb.ofNat (RationalTaylorExponential.uniformSumBound bound))) 0 (by
      intro n _
      exact (within_ofSignedRatio_iff _ _ _).mpr (RationalTaylorExponential.partial_difference_bound x y bound boundedX boundedY n))
  exact (within_congr (sequence x).toReal_limit (sequence y).toReal_limit).mp compared

/-- Input accuracy sufficient for any requested exponential accuracy on
this bounded interval. No real comparison or unbounded search is used. -/
def inputPrecision (bound : Nat) (precision : PositiveRatio) : PositiveRatio :=
  precision.divideNat (RationalTaylorExponential.uniformSumBound bound) (RationalTaylorExponential.uniformSumBound_pos bound)

theorem exp_within_of_close (x y : SignedRatio) (bound : Nat) (precision : PositiveRatio)
    (boundedX : QProb.LE x.magnitude (QProb.ofNat bound)) (boundedY : QProb.LE y.magnitude (QProb.ofNat bound))
    (close : QProb.LE (SignedRatio.sub x y).magnitude (inputPrecision bound precision).toQProb) :
    Within precision.toQProb (exp x) (exp y) :=
  within_mono (exp_within x y bound boundedX boundedY)
    (QProb.le_congr (QProb.equiv_refl _) (PositiveRatio.divide_mul precision _ _)
      (QProb.mul_le_mul close (QProb.le_refl _)))

end Thesis.Probability.RationalExponential
