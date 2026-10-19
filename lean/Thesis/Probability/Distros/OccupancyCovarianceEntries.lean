import Thesis.Probability.Distros.OccupancyDegenerate
import Thesis.Probability.Distros.ReinforcedVariance

namespace Thesis.Probability.Distros
open Combinatorics

/-- The common occupancy covariance pattern: a scaled categorical matrix,
with natural diagonal numerators and auxiliary signed off-diagonal entries. -/
def occupancyCovarianceEntry (weights : List Nat) (scale tail : Nat)
    (positive : 0 < weights.sum) (tailPositive : 0 < tail) (i j : Nat) : SignedRatio :=
  ⟨if i = j then ((scale * weights.getD i 0 * (weights.sum - weights.getD i 0) : Nat) : Int)
    else -((scale * weights.getD i 0 * weights.getD j 0 : Nat) : Int),
    weights.sum * weights.sum * tail, Nat.mul_pos (Nat.mul_pos positive positive) tailPositive⟩

theorem occupancyCovarianceEntry_scale (weights : List Nat) (scale tail : Nat)
    (positive : 0 < weights.sum) (tailPositive : 0 < tail) (i j : Nat) :
    SignedRatio.Equiv (occupancyCovarianceEntry weights scale tail positive tailPositive i j)
      (SignedRatio.mul ⟨(scale : Int), tail, tailPositive⟩
        (occupancyCovarianceEntry weights 1 1 positive Nat.zero_lt_one i j)) := by
  by_cases same : i = j <;>
    simp only [occupancyCovarianceEntry, same, if_true, if_false, SignedRatio.Equiv, SignedRatio.mul,
      Nat.mul_one, Nat.one_mul, Int.natCast_mul, Int.neg_mul, Int.mul_neg,
      Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

theorem reinforcedCount_rationalCovariance_entry (n increment : Nat) (weights : List Nat) (positive : 0 < weights.sum)
    (i j : Nat) (hi : i < weights.length) (hj : j < weights.length) :
    SignedRatio.Equiv ((reinforcedCountDistro n weights increment positive).rationalCovariance (countResponse i) (countResponse j))
      (occupancyCovarianceEntry weights (n * (weights.sum + increment * n)) (weights.sum + increment) positive (by omega) i j) := by
  by_cases same : i = j
  · subst j
    refine SignedRatio.equiv_trans (Distro.rationalVariance_nat _ _) ?_
    refine SignedRatio.equiv_trans (QProb.toSignedRatio_congr
      (reinforcedCount_coordinate_variance n increment weights positive i hi)) ?_
    simp only [occupancyCovarianceEntry, if_true, SignedRatio.Equiv, QProb.toSignedRatio,
      Int.natCast_mul, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  · refine SignedRatio.equiv_trans (Distro.rationalCovariance_ofNat _ _ _) ?_
    refine SignedRatio.equiv_trans (SignedMoment.toRatio_congr
      (reinforcedCount_covariance n increment weights positive i j hi hj same)) ?_
    simp only [occupancyCovarianceEntry, if_neg same, SignedRatio.Equiv, SignedMoment.toRatio,
      Int.natCast_mul, Int.neg_mul, Int.mul_neg, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

theorem reinforcedCount_one_covariance_entry (weights : List Nat) (positive : 0 < weights.sum)
    (i j : Nat) (hi : i < weights.length) (hj : j < weights.length) :
    SignedRatio.Equiv ((reinforcedCountDistro 1 weights 0 positive).rationalCovariance (countResponse i) (countResponse j))
      (occupancyCovarianceEntry weights 1 1 positive Nat.zero_lt_one i j) := by
  refine SignedRatio.equiv_trans (reinforcedCount_rationalCovariance_entry 1 0 weights positive i j hi hj) ?_
  by_cases same : i = j <;>
    simp only [occupancyCovarianceEntry, same, if_true, if_false, SignedRatio.Equiv,
      Nat.zero_mul, Nat.add_zero, Nat.mul_one, Nat.one_mul, Int.natCast_mul,
      Int.neg_mul, Int.mul_neg, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

theorem multivariateHypergeometric_rationalCovariance_entry (n : Nat) (stocks : List Nat)
    (positive : 0 < binom stocks.sum n) (population : 1 < stocks.sum)
    (i j : Nat) (hi : i < stocks.length) (hj : j < stocks.length) :
    SignedRatio.Equiv ((multivariateHypergeometricDistro n stocks positive).rationalCovariance (countResponse i) (countResponse j))
      (occupancyCovarianceEntry stocks (n * (stocks.sum - n)) (stocks.sum - 1) (by omega) (by omega) i j) := by
  by_cases same : i = j
  · subst j
    have variance := QProb.equiv_trans (multivariateHypergeometric_coordinate_hypergeometric n stocks positive i hi).variance
      (hypergeometric_variance (stocks.getD i 0) stocks.sum n (list_getD_le_sum _ _) positive population)
    refine SignedRatio.equiv_trans (Distro.rationalVariance_nat _ _) ?_
    refine SignedRatio.equiv_trans (QProb.toSignedRatio_congr variance) ?_
    simp only [occupancyCovarianceEntry, if_true, SignedRatio.Equiv, QProb.toSignedRatio,
      Int.natCast_mul, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  · refine SignedRatio.equiv_trans (multivariateHypergeometric_rationalCovariance n stocks positive population i j hi hj same) ?_
    simp only [occupancyCovarianceEntry, if_neg same, SignedRatio.Equiv,
      Int.natCast_mul, Int.neg_mul, Int.mul_neg, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

/-- Entrywise scalar identities lift to every finite covariance quadratic form. -/
theorem Distro.occupancyCovarianceForm_scale_entries (μ ν : Distro (List Nat)) (colours : Nat)
    (coefficients : Nat → SignedRatio) (factor : SignedRatio)
    (entries : ∀ i, i < colours → ∀ j, j < colours → SignedRatio.Equiv
      (μ.rationalCovariance (countResponse i) (countResponse j))
      (SignedRatio.mul factor (ν.rationalCovariance (countResponse i) (countResponse j)))) :
    SignedRatio.Equiv (μ.occupancyCovarianceForm colours coefficients)
      (SignedRatio.mul factor (ν.occupancyCovarianceForm colours coefficients)) := by
  let values := List.range colours
  let cell := fun i j => SignedRatio.mul (SignedRatio.mul (coefficients i) (coefficients j))
    (ν.rationalCovariance (countResponse i) (countResponse j))
  have rows (i : Nat) (within : i < colours) : SignedRatio.Equiv
      (SignedRatio.listSum (values.map (fun j => SignedRatio.mul (SignedRatio.mul (coefficients i) (coefficients j))
        (μ.rationalCovariance (countResponse i) (countResponse j)))))
      (SignedRatio.mul factor (SignedRatio.listSum (values.map (cell i)))) := by
    refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr_on_mem values _ (fun j => SignedRatio.mul factor (cell i j)) ?_) ?_
    · intro j member
      refine SignedRatio.equiv_trans (SignedRatio.mul_congr (SignedRatio.equiv_refl _) (entries i within j (List.mem_range.mp member))) ?_
      simp only [cell, SignedRatio.Equiv, SignedRatio.mul, Int.natCast_mul,
        Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    · simpa only [List.map_map, Function.comp_def] using
        SignedRatio.equiv_symm (SignedRatio.mul_listSum factor (values.map (cell i)))
  refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr_on_mem values _ _
    (fun i member => rows i (List.mem_range.mp member))) ?_
  simpa only [List.map_map, Function.comp_def] using SignedRatio.equiv_symm
    (SignedRatio.mul_listSum factor (values.map (fun i => SignedRatio.listSum (values.map (cell i)))))

/-- Reinforcement changes every covariance direction by the same scalar. -/
theorem reinforcedCount_covarianceForm_scaled (n increment : Nat) (weights : List Nat) (positive : 0 < weights.sum)
    (coefficients : Nat → SignedRatio) :
    SignedRatio.Equiv ((reinforcedCountDistro n weights increment positive).occupancyCovarianceForm weights.length coefficients)
      (SignedRatio.mul ⟨((n * (weights.sum + increment * n) : Nat) : Int), weights.sum + increment, by omega⟩
        ((reinforcedCountDistro 1 weights 0 positive).occupancyCovarianceForm weights.length coefficients)) := by
  apply Distro.occupancyCovarianceForm_scale_entries
  intro i hi j hj
  exact SignedRatio.equiv_trans (reinforcedCount_rationalCovariance_entry n increment weights positive i j hi hj)
    (SignedRatio.equiv_trans (occupancyCovarianceEntry_scale weights _ _ positive (by omega) i j)
      (SignedRatio.mul_congr (SignedRatio.equiv_refl _)
        (SignedRatio.equiv_symm (reinforcedCount_one_covariance_entry weights positive i j hi hj))))

/-- Finite-population sampling has the same coefficient geometry as one
categorical draw, multiplied by its finite-population variance factor. -/
theorem multivariateHypergeometric_covarianceForm_scaled (n : Nat) (stocks : List Nat)
    (positive : 0 < binom stocks.sum n) (population : 1 < stocks.sum) (coefficients : Nat → SignedRatio) :
    SignedRatio.Equiv ((multivariateHypergeometricDistro n stocks positive).occupancyCovarianceForm stocks.length coefficients)
      (SignedRatio.mul ⟨((n * (stocks.sum - n) : Nat) : Int), stocks.sum - 1, by omega⟩
        ((reinforcedCountDistro 1 stocks 0 (by omega)).occupancyCovarianceForm stocks.length coefficients)) := by
  apply Distro.occupancyCovarianceForm_scale_entries
  intro i hi j hj
  exact SignedRatio.equiv_trans (multivariateHypergeometric_rationalCovariance_entry n stocks positive population i j hi hj)
    (SignedRatio.equiv_trans (occupancyCovarianceEntry_scale stocks _ _ (by omega) (by omega) i j)
      (SignedRatio.mul_congr (SignedRatio.equiv_refl _)
        (SignedRatio.equiv_symm (reinforcedCount_one_covariance_entry stocks (by omega) i j hi hj))))

end Thesis.Probability.Distros
