import Thesis.Probability.SignedRatioAlgebra

namespace Thesis.Probability.SignedRatio

/-- A finite prefix sum with its final term exposed by the recursion. -/
def rangeSum (f : Nat → SignedRatio) : Nat → SignedRatio
  | 0 => zero
  | n + 1 => add (rangeSum f n) (f n)

theorem rangeSum_congr (f g : Nat → SignedRatio) (n : Nat)
    (same : ∀ k, k < n → Equiv (f k) (g k)) : Equiv (rangeSum f n) (rangeSum g n) := by
  induction n with
  | zero => exact equiv_refl _
  | succ n ih => exact add_congr (ih (fun k hk => same k (by omega))) (same n (by omega))

theorem rangeSum_add (f g : Nat → SignedRatio) (n : Nat) :
    Equiv (rangeSum (fun k => add (f k) (g k)) n) (add (rangeSum f n) (rangeSum g n)) := by
  induction n with
  | zero => exact equiv_symm (add_zero zero)
  | succ n ih => exact equiv_trans (add_congr ih (equiv_refl _)) (add_interchange _ _ _ _)

theorem rangeSum_mul_left (factor : SignedRatio) (f : Nat → SignedRatio) (n : Nat) :
    Equiv (rangeSum (fun k => mul factor (f k)) n) (mul factor (rangeSum f n)) := by
  induction n with
  | zero => exact equiv_symm (mul_zero factor)
  | succ n ih => exact equiv_trans (add_congr ih (equiv_refl _)) (equiv_symm (mul_add factor _ _))


theorem rangeSum_mul_right (f : Nat → SignedRatio) (factor : SignedRatio) (n : Nat) :
    Equiv (rangeSum (fun k => mul (f k) factor) n) (mul (rangeSum f n) factor) := by
  induction n with
  | zero => exact equiv_symm (zero_mul factor)
  | succ n ih => exact equiv_trans (add_congr ih (equiv_refl _)) (equiv_symm (add_mul _ _ factor))

theorem rangeSum_split (f : Nat → SignedRatio) (first second : Nat) :
    Equiv (rangeSum f (first + second)) (add (rangeSum f first) (rangeSum (fun k => f (first + k)) second)) := by
  induction second with
  | zero => exact equiv_symm (add_zero _)
  | succ second ih => exact equiv_trans (add_congr ih (equiv_refl _)) (add_assoc _ _ _)

theorem rangeSum_shift (f : Nat → SignedRatio) (n : Nat) :
    Equiv (rangeSum f (n + 1)) (add (f 0) (rangeSum (fun k => f (k + 1)) n)) := by
  induction n with
  | zero => exact equiv_trans (zero_add _) (equiv_symm (add_zero _))
  | succ n ih => exact equiv_trans (add_congr ih (equiv_refl _)) (add_assoc _ _ _)

theorem scaleNat_add_value (weight : Nat) (a b : SignedRatio) :
    Equiv (scaleNat weight (add a b)) (add (scaleNat weight a) (scaleNat weight b)) := by
  simp only [Equiv, scaleNat, add, Int.natCast_mul, Int.mul_add, Int.add_mul]
  ac_rfl

theorem scaleNat_add_weight (first second : Nat) (value : SignedRatio) :
    Equiv (scaleNat (first + second) value) (add (scaleNat first value) (scaleNat second value)) := by
  simp only [Equiv, scaleNat, add, Int.natCast_add, Int.add_mul, Int.natCast_mul]
  ac_rfl

theorem scaleNat_zero_value (value : SignedRatio) : Equiv (scaleNat 0 value) zero := by
  simp only [Equiv, scaleNat, zero, Int.natCast_zero, Int.zero_mul]

theorem rangeSum_scaleNat (weight : Nat) (f : Nat → SignedRatio) (n : Nat) :
    Equiv (scaleNat weight (rangeSum f n)) (rangeSum (fun k => scaleNat weight (f k)) n) := by
  induction n with
  | zero => simp only [rangeSum, Equiv, scaleNat, zero, Int.mul_zero, Int.zero_mul]
  | succ n ih => exact equiv_trans (scaleNat_add_value weight _ _) (add_congr ih (equiv_refl _))

theorem scaleNat_mul_left (weight : Nat) (a b : SignedRatio) :
    Equiv (scaleNat weight (mul a b)) (mul (scaleNat weight a) b) := by
  simp only [Equiv, scaleNat, mul, Int.natCast_mul]
  ac_rfl

theorem scaleNat_mul_right (weight : Nat) (a b : SignedRatio) :
    Equiv (scaleNat weight (mul a b)) (mul a (scaleNat weight b)) := by
  simp only [Equiv, scaleNat, mul, Int.natCast_mul]
  ac_rfl

theorem scaleNat_divideNat (value : SignedRatio) (n : Nat) (positive : 0 < n) :
    Equiv (scaleNat n (divideNat value n positive)) value := by
  simp only [Equiv, scaleNat, divideNat, Int.natCast_mul]
  ac_rfl

theorem divideNat_scaleNat (value : SignedRatio) (n : Nat) (positive : 0 < n) :
    Equiv (divideNat (scaleNat n value) n positive) value := by
  simp only [Equiv, scaleNat, divideNat, Int.natCast_mul]
  ac_rfl

end Thesis.Probability.SignedRatio
