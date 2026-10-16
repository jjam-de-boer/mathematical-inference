import Thesis.Probability.Distros.FactorialConvolution
import Thesis.Probability.Distros.JointFactorialMoments
import Thesis.Probability.Distros.HypergeometricUrn

namespace Thesis.Probability.Distros
open Combinatorics

/-- Falling-factorial Vandermonde, valid beyond the total population as
well as for empty colour stocks. -/
theorem fallingFactorial_vandermonde (n a b : Nat) :
    natSum (n + 1) (fun k => binom n k * fallingFactorial a k * fallingFactorial b (n - k)) =
      fallingFactorial (a + b) n := by
  calc
    _ = natSum (n + 1) (fun k => fallingFactorial n n * binom a k * binom b (n - k)) := by
      apply natSum_congr
      intro k within
      exact depletingTerm_hypergeometric n a b k (by omega)
    _ = fallingFactorial n n * natSum (n + 1) (fun k => binom a k * binom b (n - k)) := by
      rw [← natSum_mul_left]
      apply natSum_congr
      intro k _
      ac_rfl
    _ = fallingFactorial n n * binom (a + b) n := by rw [vandermonde]
    _ = _ := (fallingFactorial_binom (a + b) n).symm

/-- Strip a coordinate falling moment from the finite depleting kernel.
Every order is allowed; factors that vanish are never divided out. -/
theorem fallingBeta_factorial_moment (n a b order : Nat) :
    natSum (n + 1) (fun k => fallingFactorial k order *
      (binom n k * fallingFactorial a k * fallingFactorial b (n - k))) =
      fallingFactorial n order * fallingFactorial a order *
        fallingFactorial (a + b - order) (n - order) := by
  have grouping : natSum (n + 1) (fun k => fallingFactorial k order *
      (binom n k * fallingFactorial a k * fallingFactorial b (n - k))) =
      natSum (n + 1) (fun k => fallingFactorial k order * binom n k *
        (fallingFactorial a k * fallingFactorial b (n - k))) := by
    apply natSum_congr
    intro k _
    ac_rfl
  rw [grouping, binomial_factorial_sum]
  by_cases within : order ≤ n
  · have rows : natSum (n - order + 1) (fun k => binom (n - order) k *
        (fallingFactorial a (k + order) * fallingFactorial b (n - (k + order)))) =
        fallingFactorial a order * natSum (n - order + 1) (fun k =>
          binom (n - order) k * fallingFactorial (a - order) k * fallingFactorial b (n - order - k)) := by
      rw [← natSum_mul_left]
      apply natSum_congr
      intro k _
      rw [Nat.add_comm k order, fallingFactorial_add]
      have index : n - (order + k) = n - order - k := by omega
      rw [index]
      ac_rfl
    rw [rows, fallingFactorial_vandermonde]
    by_cases enough : order ≤ a
    · have total : a - order + b = a + b - order := by omega
      rw [total]
      ac_rfl
    · rw [fallingFactorial_eq_zero a order (by omega)]
      simp only [Nat.zero_mul, Nat.mul_zero]
  · rw [fallingFactorial_eq_zero n order (by omega)]
    simp only [Nat.zero_mul]

/-- A mixed falling monomial vanishes above the total degree of its count
vector. The statement also covers dimension mismatch. -/
theorem jointFalling_above_sum (orders counts : List Nat) (above : counts.sum < orders.sum) :
    jointFalling orders counts = 0 := by
  induction orders generalizing counts with
  | nil => simp only [List.sum_nil] at above; exact False.elim (by omega)
  | cons order orders ih => cases counts with
      | nil => rfl
      | cons count counts =>
          by_cases larger : count < order
          · simp only [jointFalling, fallingFactorial_eq_zero count order larger, Nat.zero_mul]
          · have tail : counts.sum < orders.sum := by simp only [List.sum_cons] at above; omega
            rw [jointFalling, ih counts tail, Nat.mul_zero]

end Thesis.Probability.Distros
