import Thesis.Probability.PositiveRatio

namespace Thesis.Probability.FiniteBernoulli

/-- A finite power difference bound, proved by induction over natural data.
This is the algebraic Bernoulli estimate used near probability zero. -/
theorem power_gap (a b n : Nat) :
    (a + b) ^ (n + 1) ≤ a ^ (n + 1) + (n + 1) * b * (a + b) ^ n := by
  induction n with
  | zero => simp only [Nat.zero_add, Nat.pow_one, Nat.pow_zero, Nat.one_mul, Nat.mul_one]; exact Nat.le_refl _
  | succ n ih =>
      have next := Nat.mul_le_mul_right (a + b) ih
      have monotone : a ^ (n + 1) ≤ (a + b) ^ (n + 1) := Nat.pow_le_pow_left (Nat.le_add_right a b) (n + 1)
      have tail := Nat.mul_le_mul_left b monotone
      calc
        (a + b) ^ (n + 1 + 1) ≤ (a ^ (n + 1) + (n + 1) * b * (a + b) ^ n) * (a + b) := by
          simpa only [Nat.pow_succ] using next
        _ = a ^ (n + 1 + 1) + b * a ^ (n + 1) + (n + 1) * b * (a + b) ^ (n + 1) := by
          simp only [Nat.pow_succ, Nat.add_mul, Nat.mul_add]; ac_rfl
        _ ≤ a ^ (n + 1 + 1) + b * (a + b) ^ (n + 1) + (n + 1) * b * (a + b) ^ (n + 1) :=
          Nat.add_le_add_right (Nat.add_le_add_left tail _) _
        _ = a ^ (n + 1 + 1) + (n + 1 + 1) * b * (a + b) ^ (n + 1) := by
          simp only [Nat.add_mul, Nat.one_mul]; ac_rfl

/-- Common-denominator Bernoulli inequality, without integer subtraction. -/
theorem complement_power (a b n : Nat) :
    (a + b) ^ (n + 1) ≤ (a + b) * a ^ n + n * b * (a + b) ^ n := by
  cases n with
  | zero => simp only [Nat.zero_add, Nat.pow_one, Nat.pow_zero, Nat.mul_one, Nat.zero_mul, Nat.add_zero]; exact Nat.le_refl _
  | succ n =>
      have gap := power_gap a b n
      have scaled := Nat.mul_le_mul_left (a + b) gap
      calc
        (a + b) ^ (n + 1 + 1) ≤ (a + b) * a ^ (n + 1) + (a + b) * ((n + 1) * b * (a + b) ^ n) := by
          simpa only [Nat.pow_succ, Nat.mul_add, Nat.mul_comm] using scaled
        _ = (a + b) * a ^ (n + 1) + (n + 1) * b * (a + b) ^ (n + 1) := by
          simp only [Nat.pow_succ]; ac_rfl

/-- If a one-unit decrement is at most `1/(2m)` of the denominator, its
`m`th power retains at least half of the original power. -/
theorem half_power (den m : Nat) (denPositive : 0 < den) (bounded : 2 * m ≤ den) :
    den ^ m ≤ 2 * (den - 1) ^ m := by
  have recovered : den - 1 + 1 = den := Nat.sub_add_cancel denPositive
  have bernoulli := complement_power (den - 1) 1 m
  rw [recovered, Nat.mul_one] at bernoulli
  have scaled := Nat.mul_le_mul_left 2 bernoulli
  have loss : 2 * (m * den ^ m) ≤ den * den ^ m := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (den ^ m) bounded
  have compared : den * den ^ m ≤ 2 * (den * (den - 1) ^ m) := by
    rw [Nat.pow_succ, Nat.mul_comm (den ^ m) den] at scaled
    rw [Nat.mul_add] at scaled
    omega
  have cancel : den * den ^ m ≤ den * (2 * (den - 1) ^ m) := by simpa only [Nat.mul_assoc, Nat.mul_left_comm 2 den] using compared
  exact Nat.le_of_mul_le_mul_left cancel denPositive

end Thesis.Probability.FiniteBernoulli
