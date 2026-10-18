import Thesis.Probability.Distros.FactorialPGF

namespace Thesis.Probability.Distros
open Combinatorics

/-- Finite integer sums for alternating auxiliary coefficients. Probability
weights remain natural; signed terms occur only in the reconstruction formula. -/
def intRangeSum : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => intRangeSum n f + f n

theorem intRangeSum_congr (n : Nat) (f g : Nat → Int) (same : ∀ k, k < n → f k = g k) :
    intRangeSum n f = intRangeSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [intRangeSum, intRangeSum, ih (fun k bound => same k (by omega)), same n (by omega)]

theorem intRangeSum_add (n : Nat) (f g : Nat → Int) :
    intRangeSum n (fun k => f k + g k) = intRangeSum n f + intRangeSum n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [intRangeSum, ih]; omega

theorem intRangeSum_zero (n : Nat) : intRangeSum n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [intRangeSum, ih, Int.add_zero]

theorem intRangeSum_head (n : Nat) (f : Nat → Int) :
    intRangeSum (n + 1) f = f 0 + intRangeSum n (fun k => f (k + 1)) := by
  induction n with
  | zero => simp only [intRangeSum, Int.zero_add, Int.add_zero]
  | succ n ih => rw [intRangeSum, ih, intRangeSum]; omega

/-- The finite sign (-1)^n, expressed without any choice of rational representative. -/
def alternatingSign : Nat → Int
  | 0 => 1
  | n + 1 => -alternatingSign n

/-- The inverse Pascal coefficients. The closed form below identifies these
executable signed integers with (-1)^(order-value) * binom order value. -/
def inverseBinomial : Nat → Nat → Int
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | order + 1, 0 => -inverseBinomial order 0
  | order + 1, value + 1 => inverseBinomial order value - inverseBinomial order (value + 1)

theorem inverseBinomial_above (order value : Nat) (above : order < value) : inverseBinomial order value = 0 := by
  induction order generalizing value with
  | zero => cases value with
      | zero => omega
      | succ value => rfl
  | succ order ih => cases value with
      | zero => omega
      | succ value =>
          rw [inverseBinomial, ih value (by omega), ih (value + 1) (by omega), Int.sub_self]

theorem inverseBinomial_closed (order value : Nat) (within : value ≤ order) :
    inverseBinomial order value = alternatingSign (order - value) * (binom order value : Int) := by
  induction order generalizing value with
  | zero => have zero : value = 0 := by omega; subst value; rfl
  | succ order ih => cases value with
      | zero =>
          simp only [inverseBinomial, ih 0 (Nat.zero_le _), Nat.sub_zero,
            alternatingSign, binom_zero_right, Int.natCast_one, Int.mul_one]
      | succ value =>
          by_cases inside : value + 1 ≤ order
          · rw [inverseBinomial, ih value (by omega), ih (value + 1) inside,
              Nat.succ_sub_succ, binom_succ_succ, Int.natCast_add]
            have shift : order - value = (order - (value + 1)) + 1 := by omega
            rw [shift, alternatingSign]
            simp only [Int.mul_add, Int.neg_mul]
            omega
          · have edge : value = order := by omega
            subst value
            have diagonal : inverseBinomial order order = 1 := by
              rw [ih order (Nat.le_refl _), Nat.sub_self, alternatingSign, binom_self, Int.natCast_one, Int.mul_one]
            simp only [inverseBinomial, diagonal, inverseBinomial_above order (order + 1) (by omega),
              Int.sub_zero, Nat.sub_self, alternatingSign, binom_self, Int.natCast_one, Int.mul_one]

/-- Pascal's recurrence and its inverse cancel inside a finite row. -/
private theorem inverseBinomial_kernel_step (n value : Nat) :
    intRangeSum (n + 2) (fun order => inverseBinomial order value * (binom (n + 1) order : Int)) =
      intRangeSum (n + 1) (fun order => inverseBinomial (order + 1) value * (binom n order : Int)) +
      intRangeSum (n + 1) (fun order => inverseBinomial order value * (binom n order : Int)) := by
  rw [intRangeSum_head]
  have tail : intRangeSum (n + 1) (fun order => inverseBinomial (order + 1) value * (binom (n + 1) (order + 1) : Int)) =
      intRangeSum (n + 1) (fun order => inverseBinomial (order + 1) value * (binom n order : Int)) +
      intRangeSum (n + 1) (fun order => inverseBinomial (order + 1) value * (binom n (order + 1) : Int)) := by
    rw [← intRangeSum_add]
    apply intRangeSum_congr
    intro order _
    rw [binom_succ_succ, Int.natCast_add, Int.mul_add]
  rw [tail]
  have padded := intRangeSum_head (n + 1) (fun order => inverseBinomial order value * (binom n order : Int))
  have last : intRangeSum (n + 2) (fun order => inverseBinomial order value * (binom n order : Int)) =
      intRangeSum (n + 1) (fun order => inverseBinomial order value * (binom n order : Int)) := by
    rw [intRangeSum, binom_eq_zero_of_lt (Nat.lt_succ_self n), Int.natCast_zero, Int.mul_zero, Int.add_zero]
  rw [last] at padded
  simp only [binom_zero_right, Int.natCast_one, Int.mul_one] at padded ⊢
  omega

/-- Finite inverse Pascal orthogonality isolates one singleton count. -/
theorem inverseBinomial_kernel (n value : Nat) :
    intRangeSum (n + 1) (fun order => inverseBinomial order value * (binom n order : Int)) =
      if n = value then 1 else 0 := by
  induction n generalizing value with
  | zero => cases value with
      | zero => rfl
      | succ value => simp only [intRangeSum, inverseBinomial, Int.zero_mul, Int.add_zero,
          Nat.zero_ne_add_one, if_false]
  | succ n ih =>
      rw [inverseBinomial_kernel_step, ← intRangeSum_add]
      cases value with
      | zero =>
          have zero : intRangeSum (n + 1) (fun order =>
              inverseBinomial (order + 1) 0 * (binom n order : Int) + inverseBinomial order 0 * (binom n order : Int)) = 0 := by
            have same := intRangeSum_congr (n + 1)
              (fun order => inverseBinomial (order + 1) 0 * (binom n order : Int) + inverseBinomial order 0 * (binom n order : Int))
              (fun _ => 0) (fun order _ => by rw [inverseBinomial, Int.neg_mul]; omega)
            exact same.trans (intRangeSum_zero _)
          rw [zero, if_neg (Nat.succ_ne_zero _)]
      | succ value =>
          have same := intRangeSum_congr (n + 1)
            (fun order => inverseBinomial (order + 1) (value + 1) * (binom n order : Int) +
              inverseBinomial order (value + 1) * (binom n order : Int))
            (fun order => inverseBinomial order value * (binom n order : Int))
            (fun order _ => by rw [← Int.add_mul, inverseBinomial, Int.sub_add_cancel])
          rw [same, ih]
          simp only [Nat.succ.injEq]

/-- Padding a known support bound adds only zero terms. The target value
may lie outside the bound, in which case both sides are zero. -/
theorem inverseBinomial_kernel_bounded (n value bound : Nat) (within : n ≤ bound) :
    intRangeSum (bound + 1) (fun order => inverseBinomial order value * (binom n order : Int)) =
      if n = value then 1 else 0 := by
  induction bound generalizing n with
  | zero => have zero : n = 0 := by omega; subst n; exact inverseBinomial_kernel 0 value
  | succ bound ih =>
      by_cases edge : n = bound + 1
      · subst n; exact inverseBinomial_kernel _ value
      · have smaller : n ≤ bound := by omega
        rw [intRangeSum, binom_eq_zero_of_lt (by omega : n < bound + 1), Int.natCast_zero,
          Int.mul_zero, Int.add_zero, ih n smaller]

end Thesis.Probability.Distros
