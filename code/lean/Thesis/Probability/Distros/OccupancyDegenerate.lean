import Thesis.Probability.Distros.HypergeometricCovariance
import Thesis.Probability.Distros.MomentTableAlgebra

namespace Thesis.Probability.Distros
open Combinatorics

/-- A zero total count forces every weighted response sum to vanish. The
shape of a retained null occurrence imposes no obligation. -/
theorem Distro.occupancyCovarianceForm_zero_total (μ : Distro (List Nat)) (colours : Nat)
    (coefficients : Nat → SignedRatio) (fixed : μ.AlmostSurely (fun counts => counts.sum = 0)) :
    SignedRatio.Equiv (μ.occupancyCovarianceForm colours coefficients) SignedRatio.zero := by
  apply (SignedRatio.equiv_zero_iff _).mpr
  apply (μ.rationalCovarianceForm_zero_iff (List.range colours) countResponse coefficients).mpr
  refine ⟨SignedRatio.zero, ?_⟩
  intro atom member weight
  refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr (List.range colours) _ (fun _ => SignedRatio.zero) ?_)
    (SignedRatio.listSum_map_zero _)
  intro i
  have bound := list_getD_le_sum atom.1 i
  have zero : atom.1.getD i 0 = 0 := by have total := fixed atom member weight; omega
  change SignedRatio.Equiv (SignedRatio.mul (coefficients i) (QProb.ofNat (atom.1.getD i 0)).toSignedRatio) SignedRatio.zero
  rw [zero]
  exact SignedRatio.mul_zero _

/-- Every coefficient vector is null for an almost-sure point law. -/
theorem Distro.occupancyCovarianceForm_zero_point (μ : Distro (List Nat)) (colours : Nat)
    (coefficients : Nat → SignedRatio) (counts : List Nat) (fixed : μ.AlmostSurely (fun values => values = counts)) :
    SignedRatio.Equiv (μ.occupancyCovarianceForm colours coefficients) SignedRatio.zero := by
  apply (SignedRatio.equiv_zero_iff _).mpr
  apply (μ.rationalCovarianceForm_zero_iff (List.range colours) countResponse coefficients).mpr
  refine ⟨rationalLinearCombination (List.range colours) coefficients countResponse counts, ?_⟩
  intro atom member weight
  rw [fixed atom member weight]
  exact SignedRatio.equiv_refl _

theorem multinomial_covarianceForm_zero_trials (weights : List Nat) (positive : 0 < weights.sum) (coefficients : Nat → SignedRatio) :
    SignedRatio.Equiv ((multinomialDistro 0 weights positive).occupancyCovarianceForm weights.length coefficients) SignedRatio.zero :=
  Distro.occupancyCovarianceForm_zero_total _ _ _ (fun atom member _ => (multinomialAtoms_support 0 weights atom member).2)

theorem reinforcedCount_covarianceForm_zero_trials (increment : Nat) (weights : List Nat) (positive : 0 < weights.sum)
    (coefficients : Nat → SignedRatio) :
    SignedRatio.Equiv ((reinforcedCountDistro 0 weights increment positive).occupancyCovarianceForm weights.length coefficients) SignedRatio.zero :=
  Distro.occupancyCovarianceForm_zero_total _ _ _ (fun atom member _ => (reinforcedCount_support 0 weights increment atom member).2)

theorem multivariateHypergeometric_covarianceForm_zero_trials (stocks : List Nat) (positive : 0 < binom stocks.sum 0)
    (coefficients : Nat → SignedRatio) :
    SignedRatio.Equiv ((multivariateHypergeometricDistro 0 stocks positive).occupancyCovarianceForm stocks.length coefficients) SignedRatio.zero :=
  Distro.occupancyCovarianceForm_zero_total _ _ _ (fun atom member _ => (multivariateHypergeometric_support 0 stocks atom member).2)

/-- Positive hypergeometric atoms respect each stock, even though overdrawn
zero-weight atoms remain present in the raw recursive record. -/
theorem multivariateHypergeometric_positive_within (n : Nat) (stocks : List Nat) (atom : List Nat × Nat)
    (member : atom ∈ multivariateHypergeometricAtoms n stocks) (positive : 0 < atom.2) :
    depletingCountsWithin atom.1 stocks := by
  induction stocks generalizing n atom with
  | nil =>
      by_cases zero : n = 0
      · subst n
        change atom ∈ [([], 1)] at member
        have same := List.mem_singleton.mp member
        cases same
        exact True.intro
      · rw [multivariateHypergeometricAtoms, if_neg zero] at member
        exact False.elim (List.not_mem_nil member)
  | cons stock stocks ih =>
      rcases List.mem_flatMap.mp member with ⟨used, _, tail⟩
      rcases List.mem_map.mp tail with ⟨rest, listed, same⟩
      cases same
      change 0 < binom stock used * rest.2 at positive
      exact ⟨hypergeometric_draws_le_total stock used (Nat.pos_of_mul_pos_right positive),
        ih (n - used) rest listed (Nat.pos_of_mul_pos_left positive)⟩

/-- A full-population sample equals the stock vector almost surely. -/
theorem multivariateHypergeometric_full_population (stocks : List Nat) (positive : 0 < binom stocks.sum stocks.sum) :
    (multivariateHypergeometricDistro stocks.sum stocks positive).AlmostSurely (fun counts => counts = stocks) := by
  intro atom member weight
  exact depletingCountsWithin_eq_of_sum atom.1 stocks
    (multivariateHypergeometric_positive_within stocks.sum stocks atom member weight)
    (multivariateHypergeometric_support stocks.sum stocks atom member).2

/-- Full-population sampling has zero covariance in every direction,
including empty and one-ball populations, without a total-minus-one denominator. -/
theorem multivariateHypergeometric_covarianceForm_full_population (stocks : List Nat)
    (positive : 0 < binom stocks.sum stocks.sum) (coefficients : Nat → SignedRatio) :
    SignedRatio.Equiv ((multivariateHypergeometricDistro stocks.sum stocks positive).occupancyCovarianceForm stocks.length coefficients)
      SignedRatio.zero :=
  Distro.occupancyCovarianceForm_zero_point _ _ _ stocks (multivariateHypergeometric_full_population stocks positive)

end Thesis.Probability.Distros
