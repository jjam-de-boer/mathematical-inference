import Thesis.Probability.Distros.OccupancyNullspace

namespace Thesis.Probability.Distros

/-- A covariance row applied to a finite coefficient vector. Index lists
may contain repetitions; each listed contribution has its original multiplicity. -/
def Distro.rationalCovarianceRow (μ : Distro Ω) (indices : List I)
    (responses : I → Ω → SignedRatio) (coefficients : I → SignedRatio) (i : I) : SignedRatio :=
  SignedRatio.listSum (indices.map (fun j => SignedRatio.mul (coefficients j)
    (μ.rationalCovariance (responses i) (responses j))))

theorem Distro.rationalCovariance_linearCombination_right (μ : Distro Ω) (indices : List I)
    (responses : I → Ω → SignedRatio) (coefficients : I → SignedRatio) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalCovariance f (rationalLinearCombination indices coefficients responses))
      (SignedRatio.listSum (indices.map (fun j => SignedRatio.mul (coefficients j)
        (μ.rationalCovariance f (responses j))))) :=
  SignedRatio.equiv_trans (μ.rationalCovariance_listSum_right indices f (fun j x => SignedRatio.mul (coefficients j) (responses j x)))
    (SignedRatio.listSum_map_congr indices _ _ (fun j => μ.rationalCovariance_scale_right (coefficients j) f (responses j)))

/-- A finite covariance quadratic form vanishes iff every listed row
annihilates the coefficient vector. No nonsingularity or positive-variance
hypothesis is needed, and the empty index list is included. -/
theorem Distro.rationalCovarianceForm_zero_iff_rows (μ : Distro Ω) (indices : List I)
    (responses : I → Ω → SignedRatio) (coefficients : I → SignedRatio) :
    (μ.rationalCovarianceForm indices responses coefficients).num = 0 ↔
      ∀ i ∈ indices, SignedRatio.Equiv (μ.rationalCovarianceRow indices responses coefficients i) SignedRatio.zero := by
  constructor
  · intro zero i _
    rcases (μ.rationalCovarianceForm_zero_iff indices responses coefficients).mp zero with ⟨c, constant⟩
    have same := μ.rationalCovariance_congr_positive (responses i) (responses i)
      (rationalLinearCombination indices coefficients responses) (fun _ => c)
      (fun _ _ _ => SignedRatio.equiv_refl _) constant
    exact SignedRatio.equiv_trans (SignedRatio.equiv_symm (μ.rationalCovariance_linearCombination_right indices responses coefficients (responses i)))
      (SignedRatio.equiv_trans same (SignedRatio.equiv_trans (μ.rationalCovariance_symm _ _)
        (μ.rationalCovariance_constant_left c (responses i))))
  · intro rows
    have expanded := μ.rationalCovariance_listSum_left indices
      (fun i x => SignedRatio.mul (coefficients i) (responses i x))
      (rationalLinearCombination indices coefficients responses)
    have terms := SignedRatio.listSum_map_congr_on_mem indices
      (fun i => μ.rationalCovariance (fun x => SignedRatio.mul (coefficients i) (responses i x))
        (rationalLinearCombination indices coefficients responses)) (fun _ => SignedRatio.zero) (by
      intro i member
      exact SignedRatio.equiv_trans (μ.rationalCovariance_scale_left (coefficients i) (responses i) _)
        (SignedRatio.equiv_trans (SignedRatio.mul_congr (SignedRatio.equiv_refl _)
          (SignedRatio.equiv_trans (μ.rationalCovariance_linearCombination_right indices responses coefficients (responses i)) (rows i member)))
          (SignedRatio.mul_zero _)))
    apply (SignedRatio.equiv_zero_iff _).mp
    exact SignedRatio.equiv_trans (SignedRatio.equiv_symm (μ.rationalVariance_linearCombination indices responses coefficients))
      (SignedRatio.equiv_trans expanded (SignedRatio.equiv_trans terms (SignedRatio.listSum_map_zero indices)))

/-- In fact a null covariance direction has zero covariance with every
rational observable, including responses outside the chosen index list. -/
theorem Distro.rationalCovariance_linearCombination_zero (μ : Distro Ω) (indices : List I)
    (responses : I → Ω → SignedRatio) (coefficients : I → SignedRatio)
    (zero : (μ.rationalCovarianceForm indices responses coefficients).num = 0) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalCovariance f (rationalLinearCombination indices coefficients responses)) SignedRatio.zero := by
  rcases (μ.rationalCovarianceForm_zero_iff indices responses coefficients).mp zero with ⟨c, constant⟩
  exact SignedRatio.equiv_trans (μ.rationalCovariance_congr_positive f f
    (rationalLinearCombination indices coefficients responses) (fun _ => c) (fun _ _ _ => SignedRatio.equiv_refl _) constant)
    (SignedRatio.equiv_trans (μ.rationalCovariance_symm _ _) (μ.rationalCovariance_constant_left c f))

theorem multinomial_covarianceRows_zero_iff (n : Nat) (weights : List Nat) (positive : 0 < weights.sum)
    (coefficients : Nat → SignedRatio) :
    (∀ i ∈ List.range weights.length, SignedRatio.Equiv
      ((multinomialDistro n weights positive).rationalCovarianceRow (List.range weights.length) countResponse coefficients i) SignedRatio.zero) ↔
      n = 0 ∨ CoefficientsConstantOnPositive weights coefficients :=
  (Distro.rationalCovarianceForm_zero_iff_rows _ _ _ _).symm.trans
    (multinomial_covarianceForm_zero_iff n weights positive coefficients)

theorem reinforcedCount_covarianceRows_zero_iff (n increment : Nat) (weights : List Nat) (positive : 0 < weights.sum)
    (coefficients : Nat → SignedRatio) :
    (∀ i ∈ List.range weights.length, SignedRatio.Equiv
      ((reinforcedCountDistro n weights increment positive).rationalCovarianceRow (List.range weights.length) countResponse coefficients i) SignedRatio.zero) ↔
      n = 0 ∨ CoefficientsConstantOnPositive weights coefficients :=
  (Distro.rationalCovarianceForm_zero_iff_rows _ _ _ _).symm.trans
    (reinforcedCount_covarianceForm_zero_iff n increment weights positive coefficients)

theorem multivariateHypergeometric_covarianceRows_zero_iff (n : Nat) (stocks : List Nat)
    (positive : 0 < Combinatorics.binom stocks.sum n) (coefficients : Nat → SignedRatio) :
    (∀ i ∈ List.range stocks.length, SignedRatio.Equiv
      ((multivariateHypergeometricDistro n stocks positive).rationalCovarianceRow (List.range stocks.length) countResponse coefficients i) SignedRatio.zero) ↔
      n = 0 ∨ n = stocks.sum ∨ CoefficientsConstantOnPositive stocks coefficients :=
  (Distro.rationalCovarianceForm_zero_iff_rows _ _ _ _).symm.trans
    (multivariateHypergeometric_covarianceForm_zero_iff n stocks positive coefficients)

end Thesis.Probability.Distros
