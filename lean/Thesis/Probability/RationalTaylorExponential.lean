import Thesis.Probability.RationalGeometricSeries
import Thesis.Probability.RationalDivisionBounds
import Thesis.Probability.RationalMonomial

namespace Thesis.Probability.RationalTaylorExponential
open SignedRatio

/-- Factorials are executable positive naturals. -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

theorem factorial_pos (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih => exact Nat.mul_pos (Nat.zero_lt_succ _) ih

/-- Exact exponential Taylor coefficients, computed by the recurrence
`t₀ = 1`, `tₙ₊₁ = x tₙ/(n+1)`. -/
def term (x : SignedRatio) : Nat → SignedRatio
  | 0 => one
  | n + 1 => divideNat (mul x (term x n)) (n + 1) (Nat.zero_lt_succ n)

theorem term_formula (x : SignedRatio) (n : Nat) :
    Equiv (term x n) (divideNat (RationalMonomial.power x n) (factorial n) (factorial_pos n)) := by
  induction n with
  | zero => exact equiv_refl _
  | succ n ih =>
      apply equiv_trans (divideNat_congr (mul_congr (equiv_refl x) ih) _ _)
      simp only [RationalMonomial.power, factorial, Equiv, divideNat, mul, Int.natCast_mul]
      ac_rfl

theorem term_congr {x y : SignedRatio} (same : Equiv x y) (n : Nat) : Equiv (term x n) (term y n) := by
  induction n with
  | zero => exact equiv_refl _
  | succ n ih => exact divideNat_congr (mul_congr same ih) _ _

/-- For `|x| ≤ 1/2`, each signed Taylor coefficient is dominated by `2⁻ⁿ`.
This is an explicit finite estimate, including negative arguments. -/
theorem term_bound (x : SignedRatio) (small : QProb.LE x.magnitude ⟨1, 2, by decide⟩) (n : Nat) :
    QProb.LE (term x n).magnitude (RationalGeometricSeries.envelope 1 n) := by
  induction n with
  | zero => exact QProb.le_refl _
  | succ n ih =>
      have contracted := magnitude_divideNat_le (mul x (term x n)) (n + 1) (Nat.zero_lt_succ n)
      have multiplied := QProb.mul_le_mul small ih
      have collect : QProb.Equiv (QProb.mul (⟨1, 2, by decide⟩ : QProb) (RationalGeometricSeries.envelope 1 n))
          (RationalGeometricSeries.envelope 1 (n + 1)) := by
        simp only [QProb.Equiv, QProb.mul, RationalGeometricSeries.envelope, Nat.pow_succ, Nat.one_mul]
        ac_rfl
      exact QProb.le_trans contracted
        (QProb.le_congr (QProb.equiv_symm (magnitude_mul _ _)) collect multiplied)

/-- The natural exponential on small rational arguments is constructed from
its Taylor series, with a certified effective modulus. Extension to arbitrary
real arguments and calculus identities are subsequent proof obligations. -/
def expSmall (x : SignedRatio) (small : QProb.LE x.magnitude ⟨1, 2, by decide⟩) : ConstructiveReal :=
  (RationalGeometricSeries.sequence (term x) 1 (term_bound x small)).limit

/-- Every truncation has the explicit remainder bound `2 / 2ⁿ`. -/
theorem expSmall_remainder (x : SignedRatio) (small : QProb.LE x.magnitude ⟨1, 2, by decide⟩) (n : Nat) :
    ConstructiveReal.Within (RationalGeometricSeries.envelope 2 n)
      (ConstructiveReal.ofSignedRatio (RationalGeometricSeries.partialSum (term x) n)) (expSmall x small) :=
  RationalGeometricSeries.remainder (term x) 1 (term_bound x small) n

private theorem block_congr (first second : Nat → SignedRatio) (same : ∀ n, Equiv (first n) (second n)) (start count : Nat) :
    Equiv (RationalGeometricSeries.block first start count) (RationalGeometricSeries.block second start count) := by
  induction count generalizing start with
  | zero => exact equiv_refl _
  | succ count ih => exact add_congr (same start) (ih (start + 1))

theorem expSmall_congr {x y : SignedRatio} (same : Equiv x y)
    (smallX : QProb.LE x.magnitude ⟨1, 2, by decide⟩) (smallY : QProb.LE y.magnitude ⟨1, 2, by decide⟩) :
    ConstructiveReal.Equiv (expSmall x smallX) (expSmall y smallY) := by
  apply RegularRationalApproximation.limit_congr
  intro precision
  exact block_congr (term x) (term y) (term_congr same) _ _

private theorem term_zero_succ (n : Nat) : Equiv (term zero (n + 1)) zero := by
  apply equiv_trans (divideNat_congr (zero_mul (term zero n)) _ _)
  simp only [Equiv, divideNat, zero, Int.zero_mul]

private theorem block_zero (start count : Nat) (positive : 0 < start) :
    Equiv (RationalGeometricSeries.block (term zero) start count) zero := by
  induction count generalizing start with
  | zero => exact equiv_refl _
  | succ count ih =>
      cases start with
      | zero => omega
      | succ start => exact equiv_trans (add_congr (term_zero_succ start) (ih (start + 2) (by omega))) (zero_add zero)

theorem expSmall_zero : ConstructiveReal.Equiv (expSmall zero (by decide)) ConstructiveReal.one := by
  have compared : ConstructiveReal.Equiv (expSmall zero (by decide)) ConstructiveReal.one.rationalApproximation.limit := by
    apply RegularRationalApproximation.limit_congr
    intro precision
    exact equiv_trans (add_congr (equiv_refl one) (block_zero 1 _ (by decide))) (add_zero one)
  exact ConstructiveReal.equiv_trans compared ConstructiveReal.one.rationalApproximation_limit

end Thesis.Probability.RationalTaylorExponential
