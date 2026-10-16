import Thesis.Probability.Distros.ReinforcedMoments

namespace Thesis.Probability.Distros
open Combinatorics

/-- A selected count in an urn with arbitrary natural reinforcement. -/
def reinforcedCountCoordinate (n : Nat) (alphas : List Nat) (increment : Nat)
    (positive : 0 < alphas.sum) (index : Nat) : NatDistro (List Nat) :=
  ⟨reinforcedCountDistro n alphas increment positive, fun counts => counts.getD index 0⟩

theorem reinforcedCount_coordinate_secondMoment (n increment : Nat) (alphas : List Nat)
    (positive : 0 < alphas.sum) (index : Nat) (within : index < alphas.length) :
    QProb.Equiv (secondMoment (reinforcedCountCoordinate n alphas increment positive index))
      ⟨n * (n - 1) * alphas.getD index 0 * (alphas.getD index 0 + increment) +
          n * alphas.getD index 0 * (alphas.sum + increment),
        alphas.sum * (alphas.sum + increment), Nat.mul_pos positive (by omega)⟩ := by
  let μ := reinforcedCountDistro n alphas increment positive
  have factorial := reinforcedCount_coordinate_factorialMoment n increment alphas positive index 2 within
  simp only [fallingFactorial, stepRising, Nat.mul_one] at factorial
  have square : secondMoment (reinforcedCountCoordinate n alphas increment positive index) =
      μ.expectNat (fun counts => counts.getD index 0 * (counts.getD index 0 - 1) + counts.getD index 0) := by
    rw [secondMoment, rawMoment_expectNat]
    apply μ.expectNat_congr_on_support
    intro atom _
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    exact (nat_falling_square _).symm
  rw [square]
  refine QProb.equiv_trans (μ.expectNat_add _ _) ?_
  refine QProb.equiv_trans (QProb.add_congr factorial
    (reinforcedCount_coordinate_mean n increment alphas positive index within)) ?_
  simp only [QProb.Equiv, QProb.add, Nat.add_mul, Nat.mul_add]
  ac_rfl

/-- The numerator balance is valid even when a selected weight or the
trial count is zero; no positive selected-colour assumption is needed. -/
theorem reinforced_variance_numerator (n a b increment : Nat) :
    n * a * b * (a + b + increment * n) + n * a * (n * a) * (a + b + increment) =
      (n * (n - 1) * a * (a + increment) + n * a * (a + b + increment)) * (a + b) := by
  symm
  calc
    _ = (n * (n - 1) + n) * (a * a) * (a + b) + n * a * b * (a + b) +
        (n * (n - 1) + n) * a * increment * (a + b) := by
      simp only [Nat.mul_add, Nat.add_mul]
      ac_rfl
    _ = _ := by
      rw [nat_falling_square]
      simp only [Nat.mul_add]
      ac_rfl

/-- Var(Kᵢ) = n aᵢ (S-aᵢ) (S+d n) / (S² (S+d)).
This includes zero reinforcement, zero trials and zero colour weights. -/
theorem reinforcedCount_coordinate_variance (n increment : Nat) (alphas : List Nat)
    (positive : 0 < alphas.sum) (index : Nat) (within : index < alphas.length) :
    QProb.Equiv (variance (reinforcedCountCoordinate n alphas increment positive index))
      ⟨n * alphas.getD index 0 * (alphas.sum - alphas.getD index 0) * (alphas.sum + increment * n),
        alphas.sum * alphas.sum * (alphas.sum + increment),
        Nat.mul_pos (Nat.mul_pos positive positive) (by omega)⟩ := by
  let numeric := reinforcedCountCoordinate n alphas increment positive index
  let a := alphas.getD index 0
  let S := alphas.sum
  let D := S * S * (S + increment)
  have hD : 0 < D := Nat.mul_pos (Nat.mul_pos positive positive) (by omega)
  have hm : QProb.Equiv (mean numeric) ⟨n * a, S, positive⟩ := by
    rw [mean_expectNat]
    exact reinforcedCount_coordinate_mean n increment alphas positive index within
  have hmean : QProb.Equiv (QProb.mul (mean numeric) (mean numeric))
      ⟨n * a * (n * a) * (S + increment), D, hD⟩ := by
    refine QProb.equiv_trans (QProb.mul_congr hm hm) ?_
    simp only [QProb.Equiv, QProb.mul, D]
    ac_rfl
  have hnum : n * a * (S - a) * (S + increment * n) + n * a * (n * a) * (S + increment) =
      (n * (n - 1) * a * (a + increment) + n * a * (S + increment)) * S := by
    have total : a + (S - a) = S := Nat.add_sub_of_le (list_getD_le_sum alphas index)
    simpa only [total] using reinforced_variance_numerator n a (S - a) increment
  apply variance_eq_of_balance
  refine QProb.equiv_trans (QProb.add_congr (QProb.equiv_refl _) hmean) ?_
  refine QProb.equiv_trans (QProb.add_mk_same_den D hD
    (n * a * (S - a) * (S + increment * n)) (n * a * (n * a) * (S + increment))) ?_
  refine QProb.equiv_trans ?_ (QProb.equiv_symm
    (reinforcedCount_coordinate_secondMoment n increment alphas positive index within))
  change (n * a * (S - a) * (S + increment * n) + n * a * (n * a) * (S + increment)) *
      (S * (S + increment)) =
    (n * (n - 1) * a * (a + increment) + n * a * (S + increment)) * D
  rw [hnum]
  unfold D
  ac_rfl

end Thesis.Probability.Distros
