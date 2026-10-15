import Thesis.Probability.Distros.ReinforcedUrn
namespace Thesis.Probability.Distros
open Combinatorics

/-- Strip any falling-factorial order from a binomial coefficient inside
an arbitrary finite sum. The identity includes orders above the trial count. -/
theorem binomial_factorial_sum (n order : Nat) (f : Nat → Nat) :
    natSum (n + 1) (fun k => fallingFactorial k order * binom n k * f k) =
      fallingFactorial n order * natSum (n - order + 1) (fun k => binom (n - order) k * f (k + order)) := by
  induction order generalizing n f with
  | zero => simp only [fallingFactorial, Nat.one_mul, Nat.sub_zero, Nat.add_zero]
  | succ order ih =>
      cases n with
      | zero => simp only [natSum, fallingFactorial, Nat.zero_mul, Nat.zero_add]
      | succ n =>
          rw [natSum_head]
          have tail : natSum (n + 1) (fun k => fallingFactorial (k + 1) (order + 1) *
                binom (n + 1) (k + 1) * f (k + 1)) =
              (n + 1) * natSum (n + 1) (fun k => fallingFactorial k order * binom n k * f (k + 1)) := by
            rw [← natSum_mul_left]
            apply natSum_congr
            intro k _
            rw [fallingFactorial_succ]
            calc
              _ = fallingFactorial k order * ((k + 1) * binom (n + 1) (k + 1)) * f (k + 1) := by ac_rfl
              _ = _ := by rw [binom_succ_mul]; ac_rfl
          rw [tail, ih, fallingFactorial_succ]
          simp only [fallingFactorial, Nat.zero_mul, Nat.zero_add, Nat.succ_sub_succ, Nat.add_assoc]
          ac_rfl

theorem binom_complement (n k : Nat) (within : k ≤ n) : binom n (n - k) = binom n k := by
  have complement : n - (n - k) = k := by omega
  have left := binom_factorial_split n (n - k) (Nat.sub_le _ _)
  rw [complement] at left
  have right := binom_factorial_split n k within
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (fallingFactorial_pos k k (Nat.le_refl k))
    (fallingFactorial_pos (n - k) (n - k) (Nat.le_refl _)))
  calc
    _ = binom n (n - k) * fallingFactorial (n - k) (n - k) * fallingFactorial k k := by ac_rfl
    _ = _ := by rw [left, ← right]; ac_rfl

/-- Complementary count orders can be stripped without dividing by a
parameter rising factorial, which may vanish for a zero-colour urn. -/
theorem binomial_complement_factorial_sum (n order : Nat) (f : Nat → Nat → Nat) :
    natSum (n + 1) (fun k => fallingFactorial (n - k) order * binom n k * f k (n - k - order)) =
      fallingFactorial n order * natSum (n - order + 1)
        (fun k => binom (n - order) k * f k (n - order - k)) := by
  rw [← natSum_reverse n]
  have reversed : natSum (n + 1) (fun k =>
      fallingFactorial (n - (n - k)) order * binom n (n - k) * f (n - k) (n - (n - k) - order)) =
      natSum (n + 1) (fun k => fallingFactorial k order * binom n k * f (n - k) (k - order)) := by
    apply natSum_congr
    intro k bound
    have hk : k ≤ n := Nat.le_of_lt_succ bound
    have complement : n - (n - k) = k := by omega
    rw [complement, binom_complement n k hk]
  rw [reversed, binomial_factorial_sum]
  by_cases within : order ≤ n
  · rw [← natSum_reverse (n - order)]
    congr 1
    apply natSum_congr
    intro k bound
    have hk : k ≤ n - order := Nat.le_of_lt_succ bound
    have a : n - (n - order - k + order) = k := by omega
    have b : n - order - k + order - order = n - order - k := by omega
    rw [a, b, binom_complement (n - order) k hk]
  · rw [fallingFactorial_eq_zero n order (by omega), Nat.zero_mul, Nat.zero_mul]

def stepBetaTerm (increment n a b k : Nat) : Nat :=
  binom n k * stepRising a increment k * stepRising b increment (n - k)

theorem stepBetaTerm_outside (increment n a b k : Nat) (above : n < k) : stepBetaTerm increment n a b k = 0 := by
  simp only [stepBetaTerm, binom_eq_zero_of_lt above, Nat.zero_mul]

theorem stepBetaTerm_step_zero (increment n a b : Nat) :
    stepBetaTerm increment (n + 1) a b 0 = b * stepBetaTerm increment n a (b + increment) 0 := by
  simp only [stepBetaTerm, binom_zero_right, stepRising, Nat.sub_zero, Nat.mul_one, Nat.one_mul]

theorem stepBetaTerm_step (increment n a b k : Nat) (within : k ≤ n) :
    stepBetaTerm increment (n + 1) a b (k + 1) =
      a * stepBetaTerm increment n (a + increment) b k + b * stepBetaTerm increment n a (b + increment) (k + 1) := by
  rw [stepBetaTerm, binom_succ_succ, Nat.succ_sub_succ, stepRising, Nat.add_mul, Nat.add_mul]
  by_cases inside : k < n
  · have index : n - k = (n - (k + 1)) + 1 := by omega
    have second : binom n (k + 1) * (a * stepRising (a + increment) increment k) * stepRising b increment (n - k) =
        b * stepBetaTerm increment n a (b + increment) (k + 1) := by
      rw [index, stepRising]
      simp only [stepBetaTerm, stepRising]
      ac_rfl
    rw [second]
    simp only [stepBetaTerm]
    ac_rfl
  · have eq : k = n := by omega
    rw [eq, binom_eq_zero_of_lt (Nat.lt_succ_self n)]
    simp only [Nat.zero_mul, stepBetaTerm, binom_eq_zero_of_lt (Nat.lt_succ_self n), Nat.mul_zero, Nat.add_zero]
    ac_rfl

/-- Vandermonde for any natural reinforcement increment, including zero. -/
theorem stepRising_vandermonde (increment n a b : Nat) :
    natSum (n + 1) (stepBetaTerm increment n a b) = stepRising (a + b) increment n := by
  induction n generalizing a b with
  | zero => simp only [natSum, stepBetaTerm, binom_zero_right, stepRising, Nat.mul_one]
  | succ n ih =>
      rw [natSum_head, stepBetaTerm_step_zero]
      have tail : natSum (n + 1) (fun k => stepBetaTerm increment (n + 1) a b (k + 1)) =
          a * natSum (n + 1) (stepBetaTerm increment n (a + increment) b) +
            b * natSum (n + 1) (fun k => stepBetaTerm increment n a (b + increment) (k + 1)) := by
        rw [← natSum_mul_left, ← natSum_mul_left, ← natSum_add]
        apply natSum_congr
        intro k hk
        exact stepBetaTerm_step increment n a b k (Nat.le_of_lt_succ hk)
      rw [tail]
      have front : stepBetaTerm increment n a (b + increment) 0 +
          natSum (n + 1) (fun k => stepBetaTerm increment n a (b + increment) (k + 1)) =
          natSum (n + 1) (stepBetaTerm increment n a (b + increment)) := by
        rw [← natSum_head, natSum_succ, stepBetaTerm_outside increment n a (b + increment) (n + 1)
          (Nat.lt_succ_self n), Nat.add_zero]
      calc
        _ = a * natSum (n + 1) (stepBetaTerm increment n (a + increment) b) +
            b * (stepBetaTerm increment n a (b + increment) 0 +
              natSum (n + 1) (fun k => stepBetaTerm increment n a (b + increment) (k + 1))) := by
          rw [Nat.mul_add]; ac_rfl
        _ = a * stepRising (a + increment + b) increment n + b * stepRising (a + (b + increment)) increment n := by
          rw [front, ih, ih]
        _ = (a + b) * stepRising (a + b + increment) increment n := by
          have index : a + increment + b = a + b + increment := by omega
          rw [index, Nat.add_assoc, Nat.add_mul]
        _ = _ := rfl

theorem stepBetaTerm_factorial_moment (increment n a b order : Nat) :
    natSum (n + 1) (fun k => fallingFactorial k order * stepBetaTerm increment n a b k) =
      fallingFactorial n order * stepRising a increment order *
        stepRising (a + b + increment * order) increment (n - order) := by
  have grouping : natSum (n + 1) (fun k => fallingFactorial k order * stepBetaTerm increment n a b k) =
      natSum (n + 1) (fun k => fallingFactorial k order * binom n k *
        (stepRising a increment k * stepRising b increment (n - k))) := by
    apply natSum_congr; intro k _; simp only [stepBetaTerm]; ac_rfl
  rw [grouping, binomial_factorial_sum]
  by_cases within : order ≤ n
  · have terms : natSum (n - order + 1) (fun k => binom (n - order) k *
        (stepRising a increment (k + order) * stepRising b increment (n - (k + order)))) =
      stepRising a increment order * natSum (n - order + 1)
        (stepBetaTerm increment (n - order) (a + increment * order) b) := by
      rw [← natSum_mul_left]
      apply natSum_congr
      intro k _
      have index : n - (k + order) = n - order - k := by omega
      rw [Nat.add_comm k order, stepRising_add, Nat.add_comm order k, index]
      simp only [stepBetaTerm]
      ac_rfl
    rw [terms, stepRising_vandermonde]
    have index : a + increment * order + b = a + b + increment * order := by omega
    rw [index, Nat.mul_assoc]
  · rw [fallingFactorial_eq_zero n order (by omega)]
    simp only [Nat.zero_mul]

end Thesis.Probability.Distros
