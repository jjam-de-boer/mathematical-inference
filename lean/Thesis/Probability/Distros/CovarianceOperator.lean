import Thesis.Probability.Distros.CovarianceRows
import Thesis.Probability.Distros.RationalVectorSpace

namespace Thesis.Probability.Distros

private theorem linearCombination_add (indices : List I) (responses : I → A → SignedRatio)
    (first second : I → SignedRatio) (x : A) :
    SignedRatio.Equiv (rationalLinearCombination indices (fun i => SignedRatio.add (first i) (second i)) responses x)
      (SignedRatio.add (rationalLinearCombination indices first responses x) (rationalLinearCombination indices second responses x)) :=
  SignedRatio.equiv_trans (SignedRatio.listSum_map_congr indices _ _ (fun i => SignedRatio.add_mul _ _ _))
    (SignedRatio.listSum_map_add indices _ _)

private theorem linearCombination_scale (indices : List I) (responses : I → A → SignedRatio)
    (factor : SignedRatio) (coefficients : I → SignedRatio) (x : A) :
    SignedRatio.Equiv (rationalLinearCombination indices (fun i => SignedRatio.mul factor (coefficients i)) responses x)
      (SignedRatio.mul factor (rationalLinearCombination indices coefficients responses x)) :=
  SignedRatio.equiv_trans (SignedRatio.listSum_map_congr indices _ _ (fun i => SignedRatio.mul_assoc _ _ _))
    (SignedRatio.equiv_symm (by
      simpa only [List.map_map, Function.comp_def] using SignedRatio.mul_listSum factor
        (indices.map (fun i => SignedRatio.mul (coefficients i) (responses i x)))))

private theorem linearCombination_neg (indices : List I) (responses : I → A → SignedRatio)
    (coefficients : I → SignedRatio) (x : A) :
    SignedRatio.Equiv (rationalLinearCombination indices (fun i => SignedRatio.neg (coefficients i)) responses x)
      (SignedRatio.neg (rationalLinearCombination indices coefficients responses x)) :=
  SignedRatio.equiv_trans (SignedRatio.listSum_map_congr indices _ _ (fun i => SignedRatio.neg_mul _ _))
    (by simpa only [List.map_map, Function.comp_def] using SignedRatio.listSum_map_neg
      (indices.map (fun i => SignedRatio.mul (coefficients i) (responses i x))))

private theorem linearCombination_sub (indices : List I) (responses : I → A → SignedRatio)
    (first second : I → SignedRatio) (x : A) :
    SignedRatio.Equiv (rationalLinearCombination indices (fun i => SignedRatio.sub (first i) (second i)) responses x)
      (SignedRatio.sub (rationalLinearCombination indices first responses x) (rationalLinearCombination indices second responses x)) :=
  SignedRatio.equiv_trans (linearCombination_add indices responses first (fun i => SignedRatio.neg (second i)) x)
    (SignedRatio.add_congr (SignedRatio.equiv_refl _) (linearCombination_neg indices responses second x))

theorem Distro.rationalCovariance_congr_right (μ : Distro A) (f g h : A → SignedRatio)
    (same : ∀ x, SignedRatio.Equiv (g x) (h x)) :
    SignedRatio.Equiv (μ.rationalCovariance f g) (μ.rationalCovariance f h) :=
  μ.rationalCovariance_congr_positive f f g h (fun _ _ _ => SignedRatio.equiv_refl _) (fun atom _ _ => same atom.1)

theorem Distro.rationalCovariance_neg_right (μ : Distro A) (f g : A → SignedRatio) :
    SignedRatio.Equiv (μ.rationalCovariance f (fun x => SignedRatio.neg (g x))) (SignedRatio.neg (μ.rationalCovariance f g)) :=
  SignedRatio.equiv_trans (μ.rationalCovariance_congr_right f _ _ (fun x =>
    SignedRatio.equiv_symm (RationalLinear.minus_one_scaleInt (g x))))
    (SignedRatio.equiv_trans (μ.rationalCovariance_scale_right ⟨-1, 1, Nat.zero_lt_one⟩ f g)
      (RationalLinear.minus_one_scaleInt _))

theorem Distro.rationalCovariance_sub_right (μ : Distro A) (f g h : A → SignedRatio) :
    SignedRatio.Equiv (μ.rationalCovariance f (fun x => SignedRatio.sub (g x) (h x)))
      (SignedRatio.sub (μ.rationalCovariance f g) (μ.rationalCovariance f h)) :=
  SignedRatio.equiv_trans (μ.rationalCovariance_add_right f g (fun x => SignedRatio.neg (h x)))
    (SignedRatio.add_congr (SignedRatio.equiv_refl _) (μ.rationalCovariance_neg_right f h))

/-- The covariance matrix acts on rational coordinate vectors through the
existing bilinear covariance. Its row-sum specification is proved below. -/
def Distro.covarianceOperator (μ : Distro A) (responses : Fin n → A → SignedRatio) : RationalVector.Operator n n where
  apply := fun coefficients i => μ.rationalCovariance (responses i) (rationalLinearCombination (List.finRange n) coefficients responses)
  congr := by
    intro first second same i
    apply μ.rationalCovariance_congr_right
    intro x
    exact SignedRatio.listSum_map_congr (List.finRange n) _ _ (fun j =>
      SignedRatio.mul_congr (same j) (SignedRatio.equiv_refl _))
  zero := by
    intro i
    refine SignedRatio.equiv_trans (μ.rationalCovariance_congr_right (responses i) _ (fun _ => SignedRatio.zero) ?_)
      (SignedRatio.equiv_trans (μ.rationalCovariance_symm _ _) (μ.rationalCovariance_constant_left SignedRatio.zero (responses i)))
    intro x
    exact SignedRatio.equiv_trans (SignedRatio.listSum_map_congr (List.finRange n) _ (fun _ => SignedRatio.zero)
      (fun j => SignedRatio.zero_mul (responses j x))) (SignedRatio.listSum_map_zero _)
  add := by
    intro first second i
    exact SignedRatio.equiv_trans (μ.rationalCovariance_congr_right (responses i) _ _
      (linearCombination_add (List.finRange n) responses first second)) (μ.rationalCovariance_add_right _ _ _)
  scale := by
    intro factor coefficients i
    exact SignedRatio.equiv_trans (μ.rationalCovariance_congr_right (responses i) _ _
      (linearCombination_scale (List.finRange n) responses factor coefficients)) (μ.rationalCovariance_scale_right factor _ _)
  sub := by
    intro first second i
    exact SignedRatio.equiv_trans (μ.rationalCovariance_congr_right (responses i) _ _
      (linearCombination_sub (List.finRange n) responses first second)) (μ.rationalCovariance_sub_right _ _ _)

theorem Distro.covarianceOperator_row (μ : Distro A) (responses : Fin n → A → SignedRatio)
    (coefficients : RationalVector.Vector n) (i : Fin n) :
    SignedRatio.Equiv ((μ.covarianceOperator responses).apply coefficients i)
      (μ.rationalCovarianceRow (List.finRange n) responses coefficients i) :=
  μ.rationalCovariance_linearCombination_right (List.finRange n) responses coefficients (responses i)

/-- Extend only the coefficient representation, leaving every actual
category, including zero-weight categories, in the original finite space. -/
def natCoefficients (coefficients : RationalVector.Vector n) (i : Nat) : SignedRatio :=
  if within : i < n then coefficients ⟨i, within⟩ else SignedRatio.zero

theorem natCoefficients_fin (coefficients : RationalVector.Vector n) (i : Fin n) : natCoefficients coefficients i.val = coefficients i := by
  simp only [natCoefficients, dif_pos i.isLt]

theorem Distro.covarianceOperator_nat_row (μ : Distro A) (responses : Nat → A → SignedRatio)
    (coefficients : RationalVector.Vector n) (i : Fin n) :
    SignedRatio.Equiv ((μ.covarianceOperator (fun j : Fin n => responses j.val)).apply coefficients i)
      (μ.rationalCovarianceRow (List.range n) responses (natCoefficients coefficients) i.val) := by
  refine SignedRatio.equiv_trans (μ.covarianceOperator_row _ coefficients i) ?_
  have same := finRange_val_map n (fun j => SignedRatio.mul (natCoefficients coefficients j)
    (μ.rationalCovariance (responses i.val) (responses j)))
  change SignedRatio.Equiv (SignedRatio.listSum _) (SignedRatio.listSum _)
  rw [← same]
  apply SignedRatio.listSum_map_congr (List.finRange n)
  intro j
  rw [natCoefficients_fin]
  exact SignedRatio.equiv_refl _

end Thesis.Probability.Distros
