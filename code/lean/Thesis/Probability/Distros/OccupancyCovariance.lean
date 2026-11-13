import Thesis.Probability.Distros.FiniteCovariance
import Thesis.Probability.Distros.HypergeometricMarginals

namespace Thesis.Probability.Distros
open Combinatorics

/-- A count coordinate as a signed rational response. -/
def countResponse (index : Nat) (counts : List Nat) : SignedRatio :=
  (QProb.ofNat (counts.getD index 0)).toSignedRatio

def Distro.occupancyCovarianceForm (μ : Distro (List Nat)) (colours : Nat)
    (coefficients : Nat → SignedRatio) : SignedRatio :=
  μ.rationalCovarianceForm (List.range colours) countResponse coefficients

theorem Distro.occupancyCovarianceForm_nonnegative (μ : Distro (List Nat)) (colours : Nat)
    (coefficients : Nat → SignedRatio) : SignedRatio.Nonnegative (μ.occupancyCovarianceForm colours coefficients) :=
  μ.rationalCovarianceForm_nonnegative _ _ _

private theorem ratio_natSum (n : Nat) (f : Nat → Nat) :
    SignedRatio.Equiv (SignedRatio.listSum ((List.range n).map (fun i => (QProb.ofNat (f i)).toSignedRatio)))
      (QProb.ofNat (natSum n f)).toSignedRatio := by
  induction n with
  | zero => exact SignedRatio.equiv_refl _
  | succ n ih =>
      rw [List.range_succ, List.map_append]
      refine SignedRatio.equiv_trans (SignedRatio.listSum_append _ _) ?_
      refine SignedRatio.equiv_trans (SignedRatio.add_congr ih (SignedRatio.add_zero _)) ?_
      simp only [SignedRatio.Equiv, SignedRatio.add, QProb.ofNat, QProb.toSignedRatio, natSum,
        Nat.mul_one, Int.natCast_one, Int.natCast_add, Int.mul_one]

private theorem natSum_count_coordinates (counts : List Nat) :
    natSum counts.length (fun i => counts.getD i 0) = counts.sum := by
  induction counts with
  | nil => rfl
  | cons count counts ih =>
      rw [List.length_cons, natSum_head]
      simpa only [List.getD_cons_zero, List.getD_cons_succ, ih, List.sum_cons]

/-- The all-ones direction is null for every almost-sure fixed-total count
law. For positive dimension this witnesses a singular covariance matrix. -/
theorem Distro.occupancyCovarianceForm_ones_zero (μ : Distro (List Nat)) (colours total : Nat)
    (fixed : μ.AlmostSurely (fun counts => counts.length = colours ∧ counts.sum = total)) :
    SignedRatio.Equiv (μ.occupancyCovarianceForm colours (fun _ => SignedRatio.one)) SignedRatio.zero := by
  apply (SignedRatio.equiv_zero_iff _).mpr
  apply (μ.rationalCovarianceForm_zero_iff (List.range colours) countResponse (fun _ => SignedRatio.one)).mpr
  refine ⟨(QProb.ofNat total).toSignedRatio, ?_⟩
  intro atom member weight
  have data := fixed atom member weight
  refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr (List.range colours) _ _
    (fun i => SignedRatio.one_mul (countResponse i atom.1))) ?_
  have result := ratio_natSum atom.1.length (fun i => atom.1.getD i 0)
  rw [natSum_count_coordinates, data.1, data.2] at result
  exact result

/-- A zero natural mean is an almost-sure zero response, by finite positivity. -/
theorem Distro.expectNat_equiv_zero_iff (μ : Distro Ω) (f : Ω → Nat) :
    QProb.Equiv (μ.expectNat f) QProb.zero ↔ μ.AlmostSurely (fun x => f x = 0) := by
  simpa only [QProb.Equiv, QProb.zero, Distro.expectNat, Nat.mul_one, Nat.zero_mul] using
    natIntegral_eq_zero_iff μ.record.atoms f

/-- A zero-stock or zero-weight coordinate supplies a complete zero row. -/
theorem Distro.occupancyCovariance_zero_row (μ : Distro (List Nat)) (i j : Nat)
    (meanZero : QProb.Equiv (μ.expectNat (fun counts => counts.getD i 0)) QProb.zero) :
    SignedRatio.Equiv (μ.rationalCovariance (countResponse i) (countResponse j)) SignedRatio.zero := by
  have supported := (μ.expectNat_equiv_zero_iff _).mp meanZero
  apply μ.rationalCovariance_zero_left_of_almostSurely
  intro atom member weight
  change SignedRatio.Equiv (QProb.ofNat (atom.1.getD i 0)).toSignedRatio SignedRatio.zero
  rw [supported atom member weight]
  exact SignedRatio.equiv_refl _

theorem multinomial_covarianceForm_nonnegative (n : Nat) (weights : List Nat) (positive : 0 < weights.sum)
    (coefficients : Nat → SignedRatio) :
    SignedRatio.Nonnegative ((multinomialDistro n weights positive).occupancyCovarianceForm weights.length coefficients) :=
  Distro.occupancyCovarianceForm_nonnegative _ _ _

theorem reinforcedCount_covarianceForm_nonnegative (n increment : Nat) (alphas : List Nat) (positive : 0 < alphas.sum)
    (coefficients : Nat → SignedRatio) :
    SignedRatio.Nonnegative ((reinforcedCountDistro n alphas increment positive).occupancyCovarianceForm alphas.length coefficients) :=
  Distro.occupancyCovarianceForm_nonnegative _ _ _

theorem multivariateHypergeometric_covarianceForm_nonnegative (n : Nat) (stocks : List Nat)
    (positive : 0 < binom stocks.sum n) (coefficients : Nat → SignedRatio) :
    SignedRatio.Nonnegative ((multivariateHypergeometricDistro n stocks positive).occupancyCovarianceForm stocks.length coefficients) :=
  Distro.occupancyCovarianceForm_nonnegative _ _ _

theorem multinomial_covarianceForm_ones_zero (n : Nat) (weights : List Nat) (positive : 0 < weights.sum) :
    SignedRatio.Equiv ((multinomialDistro n weights positive).occupancyCovarianceForm weights.length (fun _ => SignedRatio.one))
      SignedRatio.zero :=
  Distro.occupancyCovarianceForm_ones_zero _ _ n (fun atom member _ => multinomialAtoms_support n weights atom member)

theorem reinforcedCount_covarianceForm_ones_zero (n increment : Nat) (alphas : List Nat) (positive : 0 < alphas.sum) :
    SignedRatio.Equiv ((reinforcedCountDistro n alphas increment positive).occupancyCovarianceForm alphas.length (fun _ => SignedRatio.one))
      SignedRatio.zero :=
  Distro.occupancyCovarianceForm_ones_zero _ _ n (fun atom member _ => reinforcedCount_support n alphas increment atom member)

theorem multivariateHypergeometric_covarianceForm_ones_zero (n : Nat) (stocks : List Nat) (positive : 0 < binom stocks.sum n) :
    SignedRatio.Equiv ((multivariateHypergeometricDistro n stocks positive).occupancyCovarianceForm stocks.length (fun _ => SignedRatio.one))
      SignedRatio.zero :=
  Distro.occupancyCovarianceForm_ones_zero _ _ n (fun atom member _ => multivariateHypergeometric_support n stocks atom member)

theorem multinomial_covariance_zero_weight (n : Nat) (weights : List Nat) (positive : 0 < weights.sum)
    (i j : Nat) (within : i < weights.length) (zero : weights.getD i 0 = 0) :
    SignedRatio.Equiv ((multinomialDistro n weights positive).rationalCovariance (countResponse i) (countResponse j)) SignedRatio.zero := by
  apply Distro.occupancyCovariance_zero_row
  have result := multinomial_coordinate_mean n weights positive i within
  rw [mean_expectNat] at result
  exact QProb.equiv_trans result (by simp only [QProb.Equiv, zero, Nat.mul_zero, QProb.zero, Nat.zero_mul])

theorem reinforcedCount_covariance_zero_weight (n increment : Nat) (alphas : List Nat) (positive : 0 < alphas.sum)
    (i j : Nat) (within : i < alphas.length) (zero : alphas.getD i 0 = 0) :
    SignedRatio.Equiv ((reinforcedCountDistro n alphas increment positive).rationalCovariance (countResponse i) (countResponse j)) SignedRatio.zero := by
  apply Distro.occupancyCovariance_zero_row
  exact QProb.equiv_trans (reinforcedCount_coordinate_mean n increment alphas positive i within)
    (by simp only [QProb.Equiv, zero, Nat.mul_zero, QProb.zero, Nat.zero_mul])

theorem multivariateHypergeometric_covariance_zero_stock (n : Nat) (stocks : List Nat) (positive : 0 < binom stocks.sum n)
    (i j : Nat) (within : i < stocks.length) (zero : stocks.getD i 0 = 0) :
    SignedRatio.Equiv ((multivariateHypergeometricDistro n stocks positive).rationalCovariance (countResponse i) (countResponse j)) SignedRatio.zero := by
  apply Distro.occupancyCovariance_zero_row
  by_cases population : 0 < stocks.sum
  · have result := QProb.equiv_trans (multivariateHypergeometric_coordinate_hypergeometric n stocks positive i within).mean
      (hypergeometric_mean (stocks.getD i 0) stocks.sum n (list_getD_le_sum _ _) positive population)
    rw [mean_expectNat] at result
    exact QProb.equiv_trans result (by simp only [QProb.Equiv, zero, Nat.mul_zero, QProb.zero, Nat.zero_mul])
  · apply (Distro.expectNat_equiv_zero_iff _ _).mpr
    intro atom member _
    change atom.1.getD i 0 = 0
    have bound := multivariateHypergeometric_coordinate_bound n stocks atom member i
    have sample := hypergeometric_draws_le_total stocks.sum n positive
    omega

end Thesis.Probability.Distros
