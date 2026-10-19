import Thesis.Probability.Distros.FactorialInversion

namespace Thesis.Probability.SignedRatio

theorem listSum_map_congr_on_mem (values : List A) (f g : A → SignedRatio)
    (same : ∀ value ∈ values, Equiv (f value) (g value)) :
    Equiv (listSum (values.map f)) (listSum (values.map g)) := by
  induction values with
  | nil => exact equiv_refl _
  | cons value values ih =>
      exact add_congr (same value (List.mem_cons_self ..))
        (ih (fun other member => same other (List.mem_cons_of_mem _ member)))

theorem listSum_map_zero (values : List A) : Equiv (listSum (values.map (fun _ => zero))) zero := by
  induction values with
  | nil => exact equiv_refl _
  | cons value values ih => exact equiv_trans (add_congr (equiv_refl _) ih) (add_zero _)

/-- Finite sums commute without choosing representatives of rational values. -/
theorem listSum_swap (left : List A) (right : List B) (f : A → B → SignedRatio) :
    Equiv (listSum (left.map (fun a => listSum (right.map (f a)))))
      (listSum (right.map (fun b => listSum (left.map (fun a => f a b))))) := by
  induction left with
  | nil => exact equiv_symm (listSum_map_zero right)
  | cons a left ih =>
      exact equiv_trans (add_congr (equiv_refl _) ih)
        (equiv_symm (listSum_map_add right (f a) (fun b => listSum (left.map (fun a => f a b)))))

theorem listSum_range_select (n value : Nat) (f : Nat → SignedRatio) (within : value < n) :
    Equiv (listSum ((List.range n).map (fun k => if k = value then f value else zero))) (f value) := by
  induction n generalizing value with
  | zero => omega
  | succ n ih =>
      rw [List.range_succ, List.map_append]
      refine equiv_trans (listSum_append _ _) ?_
      refine equiv_trans (add_congr (equiv_refl _) (add_zero _)) ?_
      by_cases last : value = n
      · subst value
        have earlier : Equiv (listSum ((List.range n).map (fun k => if k = n then f n else zero))) zero := by
          refine equiv_trans (listSum_map_congr_on_mem _ _ _ ?_) (listSum_map_zero (List.range n))
          intro k member
          have different : k ≠ n := by have bound := List.mem_range.mp member; omega
          rw [if_neg different]
          exact equiv_refl _
        exact equiv_trans (add_congr earlier (by rw [if_pos rfl]; exact equiv_refl _)) (zero_add _)
      · have earlier : value < n := by omega
        exact equiv_trans (add_congr (ih value earlier)
          (by rw [if_neg (Ne.symm last)]; exact equiv_refl _)) (add_zero _)

end Thesis.Probability.SignedRatio

namespace Thesis.Probability.Distros
open Combinatorics

theorem alternatingSign_add (a b : Nat) : alternatingSign (a + b) = alternatingSign a * alternatingSign b := by
  induction b with
  | zero => simp only [Nat.add_zero, alternatingSign, Int.mul_one]
  | succ b ih => rw [Nat.add_succ, alternatingSign, ih, alternatingSign, Int.mul_neg]

theorem alternatingSign_square (n : Nat) : alternatingSign n * alternatingSign n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [alternatingSign, Int.neg_mul, Int.mul_neg, Int.neg_neg, ih]

private theorem inverseBinomial_dual_term (n value order : Nat) :
    inverseBinomial n value * (binom value order : Int) =
      alternatingSign (n - order) * (inverseBinomial value order * (binom n value : Int)) := by
  by_cases above : n < value
  · rw [inverseBinomial_above n value above, binom_eq_zero_of_lt above, Int.natCast_zero,
      Int.zero_mul, Int.mul_zero, Int.mul_zero]
  · by_cases below : value < order
    · rw [binom_eq_zero_of_lt below, inverseBinomial_above value order below, Int.natCast_zero,
        Int.zero_mul, Int.mul_zero, Int.mul_zero]
    · rw [inverseBinomial_closed n value (by omega), inverseBinomial_closed value order (by omega)]
      have split : n - order = (n - value) + (value - order) := by omega
      have sign : alternatingSign (n - order) * alternatingSign (value - order) = alternatingSign (n - value) := by
        rw [split, alternatingSign_add, Int.mul_assoc, alternatingSign_square, Int.mul_one]
      calc
        _ = alternatingSign (n - value) * ((binom value order : Int) * (binom n value : Int)) := by ac_rfl
        _ = (alternatingSign (n - order) * alternatingSign (value - order)) *
            ((binom value order : Int) * (binom n value : Int)) := by rw [sign]
        _ = _ := by ac_rfl

theorem intRangeSum_mul_left (n : Nat) (factor : Int) (f : Nat → Int) :
    intRangeSum n (fun k => factor * f k) = factor * intRangeSum n f := by
  induction n with
  | zero => simp only [intRangeSum, Int.mul_zero]
  | succ n ih => rw [intRangeSum, ih, intRangeSum, Int.mul_add]

/-- The other inverse Pascal identity recovers a moment from candidate PMFs.
The original kernel recovered a PMF from the moments of an existing law. -/
theorem inverseBinomial_reverse_kernel (n order bound : Nat) (within : n ≤ bound) :
    intRangeSum (bound + 1) (fun value => inverseBinomial n value * (binom value order : Int)) =
      if n = order then 1 else 0 := by
  rw [intRangeSum_congr (bound + 1) _ _ (fun value _ => inverseBinomial_dual_term n value order),
    intRangeSum_mul_left, inverseBinomial_kernel_bounded n order bound within]
  by_cases same : n = order
  · subst n
    simp only [Nat.sub_self, alternatingSign, if_true, Int.mul_one]
  · simp only [if_neg same, Int.mul_zero]

theorem inverseBinomial_reverse_ratio_kernel (n order bound : Nat) (within : n ≤ bound) :
    SignedRatio.Equiv (SignedRatio.listSum ((List.range (bound + 1)).map (fun value =>
      SignedRatio.mul ⟨inverseBinomial n value, 1, Nat.zero_lt_one⟩
        (QProb.ofNat (binom value order)).toSignedRatio)))
      (if n = order then SignedRatio.one else SignedRatio.zero) := by
  have terms := SignedRatio.listSum_map_congr (List.range (bound + 1))
    (fun value => SignedRatio.mul ⟨inverseBinomial n value, 1, Nat.zero_lt_one⟩
      (QProb.ofNat (binom value order)).toSignedRatio)
    (fun value => (⟨inverseBinomial n value * (binom value order : Int), 1, Nat.zero_lt_one⟩ : SignedRatio))
    (fun value => by simp only [SignedRatio.Equiv, SignedRatio.mul, QProb.ofNat, QProb.toSignedRatio,
      Int.natCast_one, Int.mul_one, Nat.mul_one])
  have result := SignedRatio.equiv_trans terms (signedRatio_intRangeSum (bound + 1)
    (fun value => inverseBinomial n value * (binom value order : Int)))
  rw [inverseBinomial_reverse_kernel n order bound within] at result
  by_cases same : n = order
  · simpa only [if_pos same] using result
  · simpa only [if_neg same] using result

end Thesis.Probability.Distros
