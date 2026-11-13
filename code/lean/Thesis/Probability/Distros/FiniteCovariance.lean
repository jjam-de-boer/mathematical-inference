import Thesis.Probability.Distros.RationalCovarianceAlgebra
import Thesis.Probability.Distros.RationalConcentration

namespace Thesis.Probability.Distros

/-- A finite rational linear combination of response observables. Index
lists need not be duplicate-free; every listed contribution is retained. -/
def rationalLinearCombination (indices : List I) (coefficients : I → SignedRatio)
    (responses : I → Ω → SignedRatio) (x : Ω) : SignedRatio :=
  SignedRatio.listSum (indices.map (fun i => SignedRatio.mul (coefficients i) (responses i x)))

/-- The covariance matrix as a quadratic form, expressed by explicit finite
sums rather than a quotient matrix representation. -/
def Distro.rationalCovarianceForm (μ : Distro Ω) (indices : List I)
    (responses : I → Ω → SignedRatio) (coefficients : I → SignedRatio) : SignedRatio :=
  SignedRatio.listSum (indices.map (fun i => SignedRatio.listSum (indices.map (fun j =>
    SignedRatio.mul (SignedRatio.mul (coefficients i) (coefficients j))
      (μ.rationalCovariance (responses i) (responses j))))))

theorem Distro.rationalCovariance_listSum_left (μ : Distro Ω) (indices : List I)
    (responses : I → Ω → SignedRatio) (g : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalCovariance (fun x => SignedRatio.listSum (indices.map (fun i => responses i x))) g)
      (SignedRatio.listSum (indices.map (fun i => μ.rationalCovariance (responses i) g))) := by
  induction indices with
  | nil => exact μ.rationalCovariance_constant_left SignedRatio.zero g
  | cons i indices ih =>
      exact SignedRatio.equiv_trans (μ.rationalCovariance_add_left (responses i)
        (fun x => SignedRatio.listSum (indices.map (fun j => responses j x))) g)
        (SignedRatio.add_congr (SignedRatio.equiv_refl _) ih)

theorem Distro.rationalCovariance_listSum_right (μ : Distro Ω) (indices : List I)
    (f : Ω → SignedRatio) (responses : I → Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalCovariance f (fun x => SignedRatio.listSum (indices.map (fun i => responses i x))))
      (SignedRatio.listSum (indices.map (fun i => μ.rationalCovariance f (responses i)))) :=
  SignedRatio.equiv_trans (μ.rationalCovariance_symm _ _)
    (SignedRatio.equiv_trans (μ.rationalCovariance_listSum_left indices responses f)
      (SignedRatio.listSum_map_congr indices _ _ (fun i => μ.rationalCovariance_symm (responses i) f)))

/-- The variance of a finite weighted sum equals its full covariance quadratic
form, including all diagonal and off-diagonal terms. -/
theorem Distro.rationalVariance_linearCombination (μ : Distro Ω) (indices : List I)
    (responses : I → Ω → SignedRatio) (coefficients : I → SignedRatio) :
    SignedRatio.Equiv (μ.rationalVariance (rationalLinearCombination indices coefficients responses))
      (μ.rationalCovarianceForm indices responses coefficients) := by
  refine SignedRatio.equiv_trans (μ.rationalCovariance_listSum_left indices
    (fun i x => SignedRatio.mul (coefficients i) (responses i x))
    (rationalLinearCombination indices coefficients responses)) ?_
  apply SignedRatio.listSum_map_congr
  intro i
  refine SignedRatio.equiv_trans (μ.rationalCovariance_listSum_right indices
    (fun x => SignedRatio.mul (coefficients i) (responses i x))
    (fun j x => SignedRatio.mul (coefficients j) (responses j x))) ?_
  apply SignedRatio.listSum_map_congr
  intro j
  exact SignedRatio.equiv_trans (μ.rationalCovariance_scale_left (coefficients i) (responses i)
    (fun x => SignedRatio.mul (coefficients j) (responses j x)))
    (SignedRatio.equiv_trans (SignedRatio.mul_congr (SignedRatio.equiv_refl _)
      (μ.rationalCovariance_scale_right (coefficients j) (responses i) (responses j)))
      (SignedRatio.equiv_symm (SignedRatio.mul_assoc _ _ _)))

/-- Every finite rational covariance matrix is positive semidefinite. -/
theorem Distro.rationalCovarianceForm_nonnegative (μ : Distro Ω) (indices : List I)
    (responses : I → Ω → SignedRatio) (coefficients : I → SignedRatio) :
    SignedRatio.Nonnegative (μ.rationalCovarianceForm indices responses coefficients) :=
  (SignedRatio.nonnegative_congr (μ.rationalVariance_linearCombination indices responses coefficients)).mp
    (μ.rationalVariance_nonnegative _)

/-- The null directions are precisely the weighted responses which are
almost-sure constants. Singular and zero-variance cases need no exception. -/
theorem Distro.rationalCovarianceForm_zero_iff (μ : Distro Ω) (indices : List I)
    (responses : I → Ω → SignedRatio) (coefficients : I → SignedRatio) :
    (μ.rationalCovarianceForm indices responses coefficients).num = 0 ↔
      ∃ c : SignedRatio, μ.AlmostSurely (fun x => SignedRatio.Equiv
        (rationalLinearCombination indices coefficients responses x) c) :=
  (SignedRatio.equiv_num_zero_iff (μ.rationalVariance_linearCombination indices responses coefficients)).symm.trans
    (μ.rationalVariance_zero_iff_constant _)

/-- An almost-sure zero response supplies an entire zero covariance row,
not merely one vanishing off-diagonal entry. -/
theorem Distro.rationalCovariance_zero_left_of_almostSurely (μ : Distro Ω) (f g : Ω → SignedRatio)
    (zero : μ.AlmostSurely (fun x => SignedRatio.Equiv (f x) SignedRatio.zero)) :
    SignedRatio.Equiv (μ.rationalCovariance f g) SignedRatio.zero :=
  SignedRatio.equiv_trans (μ.rationalCovariance_congr_positive f (fun _ => SignedRatio.zero) g g
    zero (fun _ _ _ => SignedRatio.equiv_refl _)) (μ.rationalCovariance_constant_left SignedRatio.zero g)

/-- Law equality transports every finite covariance quadratic form. -/
theorem Distro.SameLaw.rationalCovarianceForm {μ ν : Distro Ω} (same : μ.SameLaw ν) (indices : List I)
    (responses : I → Ω → SignedRatio) (coefficients : I → SignedRatio) :
    SignedRatio.Equiv (μ.rationalCovarianceForm indices responses coefficients)
      (ν.rationalCovarianceForm indices responses coefficients) :=
  SignedRatio.listSum_map_congr indices _ _ (fun i => SignedRatio.listSum_map_congr indices _ _
    (fun j => SignedRatio.mul_congr (SignedRatio.equiv_refl _) (same.rationalCovariance (responses i) (responses j))))

end Thesis.Probability.Distros
