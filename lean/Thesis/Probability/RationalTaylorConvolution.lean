import Thesis.Probability.RationalTaylorExponential
import Thesis.Probability.SignedRatioRangeSum

namespace Thesis.Probability.RationalTaylorExponential
open SignedRatio

/-- Finite convolution of exact Taylor coefficients at total degree n. -/
def convolution (a b : SignedRatio) (n : Nat) : SignedRatio :=
  rangeSum (fun k => mul (term a k) (term b (n - k))) (n + 1)

private theorem term_scaled (x : SignedRatio) (n : Nat) :
    Equiv (scaleNat (n + 1) (term x (n + 1))) (mul x (term x n)) :=
  scaleNat_divideNat _ _ _

private theorem convolution_left (a b : SignedRatio) (n : Nat) :
    Equiv (rangeSum (fun k => scaleNat k (mul (term a k) (term b (n + 1 - k)))) (n + 2))
      (mul a (convolution a b n)) := by
  have shifted := rangeSum_shift (fun k => scaleNat k (mul (term a k) (term b (n + 1 - k)))) (n + 1)
  have pointwise : Equiv
      (rangeSum (fun k => scaleNat (k + 1) (mul (term a (k + 1)) (term b (n + 1 - (k + 1))))) (n + 1))
      (rangeSum (fun k => mul a (mul (term a k) (term b (n - k)))) (n + 1)) := by
    apply rangeSum_congr
    intro k _
    rw [show n + 1 - (k + 1) = n - k by omega]
    exact equiv_trans (scaleNat_mul_left _ _ _)
      (equiv_trans (mul_congr (term_scaled a k) (equiv_refl _)) (mul_assoc _ _ _))
  exact equiv_trans shifted (equiv_trans (add_congr (scaleNat_zero_value _) pointwise)
    (equiv_trans (zero_add _) (rangeSum_mul_left a _ _)))

private theorem convolution_right (a b : SignedRatio) (n : Nat) :
    Equiv (rangeSum (fun k => scaleNat (n + 1 - k) (mul (term a k) (term b (n + 1 - k)))) (n + 2))
      (mul b (convolution a b n)) := by
  have pointwise : Equiv
      (rangeSum (fun k => scaleNat (n + 1 - k) (mul (term a k) (term b (n + 1 - k)))) (n + 1))
      (rangeSum (fun k => mul b (mul (term a k) (term b (n - k)))) (n + 1)) := by
    apply rangeSum_congr
    intro k within
    rw [show n + 1 - k = (n - k) + 1 by omega]
    exact equiv_trans (scaleNat_mul_right _ _ _) (equiv_trans
      (mul_congr (equiv_refl _) (term_scaled b (n - k)))
      (equiv_trans (equiv_symm (mul_assoc _ _ _)) (equiv_trans (mul_congr (mul_comm _ _) (equiv_refl _)) (mul_assoc _ _ _))))
  exact equiv_trans (add_congr pointwise (by
      dsimp only; rw [Nat.sub_self]; exact scaleNat_zero_value _))
    (equiv_trans (add_zero _) (rangeSum_mul_left b _ _))

/-- Finite convolution obeys the same coefficient recurrence as the Taylor
series at a+b. Every identity is over signed rationals, including negatives. -/
theorem convolution_recurrence (a b : SignedRatio) (n : Nat) :
    Equiv (scaleNat (n + 1) (convolution a b (n + 1))) (mul (add a b) (convolution a b n)) := by
  have split : Equiv
      (rangeSum (fun k => scaleNat (n + 1) (mul (term a k) (term b (n + 1 - k)))) (n + 2))
      (rangeSum (fun k => add (scaleNat k (mul (term a k) (term b (n + 1 - k))))
        (scaleNat (n + 1 - k) (mul (term a k) (term b (n + 1 - k))))) (n + 2)) := by
    apply rangeSum_congr
    intro k within
    have recovered : k + (n + 1 - k) = n + 1 := by omega
    simpa only [recovered] using scaleNat_add_weight k (n + 1 - k) (mul (term a k) (term b (n + 1 - k)))
  exact equiv_trans (rangeSum_scaleNat (n + 1) _ (n + 2))
    (equiv_trans split (equiv_trans (rangeSum_add _ _ _)
      (equiv_trans (add_congr (convolution_left a b n) (convolution_right a b n)) (equiv_symm (add_mul a b _)))))

/-- Taylor coefficients of a sum are the finite convolution of the original
coefficients. This is proved before any exponential addition law or infinite
series rearrangement is assumed. -/
theorem term_add (a b : SignedRatio) (n : Nat) : Equiv (term (add a b) n) (convolution a b n) := by
  induction n with
  | zero =>
      exact equiv_symm (equiv_trans (zero_add _) (one_mul one))
  | succ n ih =>
      have divided := divideNat_congr (convolution_recurrence a b n) (n + 1) (Nat.zero_lt_succ _)
      exact equiv_trans (divideNat_congr (mul_congr (equiv_refl _) ih) _ _)
        (equiv_trans (equiv_symm divided) (divideNat_scaleNat _ _ _))

end Thesis.Probability.RationalTaylorExponential
