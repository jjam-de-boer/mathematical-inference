import Thesis.Probability.ConstructiveRealEntropyCurve
import Thesis.Probability.ConstructiveRealGibbsTiltEntropy

namespace Thesis.Probability.FiniteGibbsTilt
open ConstructiveReal

private abbrev Expression := RationalPolynomial.Expression 4
private def offsetExpr : Expression := .coordinate 0
private def energyExpr : Expression := .coordinate 1
private def parameterExpr : Expression := .coordinate 2
private def partitionExpr : Expression := .coordinate 3
private def gradientExpr : Expression := .sub (.constant SignedRatio.zero)
  (.add (.sub (.sub offsetExpr (.mul parameterExpr energyExpr)) partitionExpr) (.constant SignedRatio.one))
private def affineGradientExpr : Expression := .add (.sub (.mul parameterExpr energyExpr) offsetExpr)
  (.sub partitionExpr (.constant SignedRatio.one))

/-- The entropy gradient of the actual normalized Gibbs law has its affine
energy/offset form, derived from the probability logarithm. -/
theorem naturalGradient_affine (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) (i : Fin states) :
    Equiv (entropyNaturalGradient (family.mass parameter i) (family.massLower parameter i) (family.mass_positive parameter i))
      (add (sub (mul parameter (family.energy i)) (family.offset i)) (sub (family.logPartition parameter) one)) := by
  have logWeight : Equiv (family.logWeight parameter i) (sub (family.offset i) (mul parameter (family.energy i))) :=
    equiv_trans (add_congr (mul_neg _ _) (equiv_refl _)) (add_comm _ _)
  have logarithm := equiv_trans (family.mass_logarithm parameter i) (add_congr logWeight (equiv_refl _))
  have polynomial := RationalPolynomial.Expression.equalityCheck_sound_real gradientExpr affineGradientExpr (by decide +kernel)
    (fun j => if j = 0 then family.offset i else if j = 1 then family.energy i else if j = 2 then parameter else family.logPartition parameter)
  exact equiv_trans (neg_congr (add_congr logarithm (equiv_refl _))) (equiv_trans (equiv_symm (zero_add _)) polynomial)

/-- A normalized probability velocity cancels the partition/normalization
constant. The natural entropy first variation is parameter times the energy
probability variation minus the reference-offset variation. -/
theorem naturalGradient_pair (family : FiniteGibbsTilt states) (parameter : ConstructiveReal)
    (velocity : Fin states → ConstructiveReal)
    (tangent : Equiv (Distros.RationalLinear.realDot states (fun _ => 1) velocity) zero) :
    Equiv (FiniteLinear.pair states velocity (fun i => entropyNaturalGradient
      (family.mass parameter i) (family.massLower parameter i) (family.mass_positive parameter i)))
      (sub (mul parameter (FiniteLinear.pair states velocity family.energy)) (FiniteLinear.pair states velocity family.offset)) :=
  equiv_trans (FiniteLinear.pair_comm states _ _)
    (equiv_trans (FiniteLinear.pair_congr states _ _ velocity velocity (family.naturalGradient_affine parameter) (fun _ => equiv_refl _))
      (equiv_trans (FiniteLinear.pair_add_first states _ _ velocity)
        (equiv_trans (add_congr (FiniteLinear.pair_sub_first states _ _ velocity)
          (FiniteLinear.pair_constant_kernel states _ velocity tangent))
          (equiv_trans (add_zero _) (add_congr
            (equiv_trans (FiniteLinear.pair_scale_first states parameter family.energy velocity)
              (mul_congr (equiv_refl _) (FiniteLinear.pair_comm states _ _)))
            (neg_congr (FiniteLinear.pair_comm states _ _)))))))

/-- Entropy variation along any actual normalized probability path passing
through this Gibbs law. Positivity floors are obtained from the reference
family, and the tangent equation is derived from path normalization.
The neighboring path need not itself remain a Gibbs family. -/
def entropyCurve_hasDerivativeAt (family : FiniteGibbsTilt states) (parameter : ConstructiveReal)
    (path : Fin states → ConstructiveReal → UnitIntervalValue) (point : ConstructiveReal)
    (velocity : Fin states → ConstructiveReal)
    (derivatives : ∀ i, HasDerivativeAt (fun t => (path i t).value) point (velocity i))
    (normalized : ∀ t, Equiv (Distros.RationalLinear.realDot states (fun _ => 1) (fun i => (path i t).value)) one)
    (atGibbs : ∀ i, Equiv (path i point).value (family.mass parameter i)) :
    HasDerivativeAt (fun t => mul (realEntropySum ((List.finRange states).map (fun i => path i t))) lnTwo) point
      (sub (mul parameter (FiniteLinear.pair states velocity family.energy)) (FiniteLinear.pair states velocity family.offset)) := by
  have positive (i : Fin states) : LE (ofSignedRatio (family.massLower parameter i).toSignedRatio) (path i point).value :=
    (le_congr (equiv_refl _) (atGibbs i)).mpr (family.mass_positive parameter i)
  let derivative := ConstructiveReal.entropyCurve_hasDerivativeAt path point velocity derivatives (family.massLower parameter) positive
  have gradients (i : Fin states) : Equiv (entropyNaturalGradient (path i point).value (family.massLower parameter i) (positive i))
      (entropyNaturalGradient (family.mass parameter i) (family.massLower parameter i) (family.mass_positive parameter i)) :=
    neg_congr (add_congr (positiveLn_congr (atGibbs i) _ _ (positive i) (family.mass_positive parameter i)) (equiv_refl _))
  exact derivative.slope_congr (equiv_trans (FiniteLinear.pair_congr states velocity velocity _ _ (fun _ => equiv_refl _) gradients)
    (family.naturalGradient_pair parameter velocity (normalized_curve_velocity path point velocity derivatives normalized)))

end Thesis.Probability.FiniteGibbsTilt
