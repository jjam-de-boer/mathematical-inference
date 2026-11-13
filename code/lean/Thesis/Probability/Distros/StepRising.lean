import Thesis.Probability.Distros.MulticolourPolya
import Thesis.Probability.Distros.MultinomialAggregation
namespace Thesis.Probability.Distros
open Combinatorics

/-- Rising factorial with a natural reinforcement increment. -/
def stepRising (a increment : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => a * stepRising (a + increment) increment n

theorem stepRising_pos (a increment n : Nat) (positive : 0 < a) : 0 < stepRising a increment n := by
  induction n generalizing a with
  | zero => exact Nat.zero_lt_one
  | succ n ih => exact Nat.mul_pos positive (ih _ (by omega))

theorem stepRising_zero (a n : Nat) : stepRising a 0 n = a ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [stepRising, Nat.add_zero, ih, Nat.pow_succ]; ac_rfl

theorem stepRising_one (a n : Nat) : stepRising a 1 n = risingFactorial a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => rw [stepRising, ih, risingFactorial_head]

theorem stepRising_scale (c a increment n : Nat) :
    stepRising (c * a) (c * increment) n = c ^ n * stepRising a increment n := by
  induction n generalizing a with
  | zero => simp only [stepRising, Nat.pow_zero, Nat.mul_one]
  | succ n ih => rw [stepRising, ← Nat.mul_add, ih, stepRising, Nat.pow_succ]; ac_rfl

theorem stepRising_add (a increment r n : Nat) :
    stepRising a increment (r + n) = stepRising a increment r * stepRising (a + increment * r) increment n := by
  induction r generalizing a with
  | zero => simp only [Nat.zero_add, Nat.mul_zero, Nat.add_zero, stepRising, Nat.one_mul]
  | succ r ih =>
      rw [Nat.add_right_comm r 1 n, stepRising, ih, stepRising]
      have index : a + increment + increment * r = a + increment * (r + 1) := by
        rw [Nat.mul_add, Nat.mul_one]; omega
      rw [index]
      ac_rfl

def stepKernel (increment : Nat) : List Nat → List Nat → Nat
  | [], [] => 1
  | alpha :: alphas, count :: counts => stepRising alpha increment count * stepKernel increment alphas counts
  | _, _ => 0

theorem stepKernel_zeros (increment : Nat) (alphas : List Nat) :
    stepKernel increment alphas (List.replicate alphas.length 0) = 1 := by
  induction alphas with
  | nil => rfl
  | cons alpha alphas ih => simp only [List.length_cons, List.replicate_succ, stepKernel, stepRising, Nat.one_mul, ih]

theorem stepKernel_increment (increment : Nat) (alphas counts : List Nat)
    (dimension : alphas.length = counts.length) (index : Nat) (within : index < alphas.length) :
    stepKernel increment alphas (counts.modify index (fun c => c + 1)) =
      alphas.getD index 0 * stepKernel increment (alphas.modify index (fun a => a + increment)) counts := by
  induction alphas generalizing counts index with
  | nil => simp only [List.length_nil] at within; omega
  | cons alpha alphas ih =>
      cases counts with
      | nil => simp only [List.length_cons, List.length_nil] at dimension; omega
      | cons count counts =>
          cases index with
          | zero => simp only [List.modify_zero_cons, List.getD_cons_zero, stepKernel, stepRising]; ac_rfl
          | succ index =>
              simp only [List.modify_succ_cons, List.getD_cons_succ, stepKernel]
              rw [ih counts (Nat.succ.inj dimension) index (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using within)]
              ac_rfl

theorem stepKernel_one (alphas counts : List Nat) : stepKernel 1 alphas counts = risingKernel alphas counts := by
  induction alphas generalizing counts with
  | nil => cases counts <;> rfl
  | cons alpha alphas ih => cases counts <;> simp only [stepKernel, risingKernel, stepRising_one, ih]

theorem stepKernel_zero (alphas counts : List Nat) : stepKernel 0 alphas counts = natMonomial alphas counts := by
  induction alphas generalizing counts with
  | nil => cases counts <;> rfl
  | cons alpha alphas ih => cases counts <;> simp only [stepKernel, natMonomial, stepRising_zero, ih]

theorem stepKernel_scale (c increment : Nat) (alphas counts : List Nat) :
    stepKernel (c * increment) (alphas.map (fun a => c * a)) counts =
      c ^ counts.sum * stepKernel increment alphas counts := by
  induction alphas generalizing counts with
  | nil => cases counts <;> simp only [List.map_nil, stepKernel, List.sum_nil, Nat.pow_zero, Nat.mul_one, Nat.mul_zero]
  | cons alpha alphas ih =>
      cases counts with
      | nil => simp only [List.map_cons, stepKernel, Nat.mul_zero]
      | cons count counts =>
          simp only [List.map_cons, stepKernel, stepRising_scale, ih, List.sum_cons, Nat.pow_add]
          ac_rfl

end Thesis.Probability.Distros
