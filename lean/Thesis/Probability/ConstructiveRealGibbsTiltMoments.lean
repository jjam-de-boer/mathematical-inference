import Thesis.Probability.ConstructiveRealGibbsTiltDerivative
import Thesis.Probability.ConstructiveRealPolynomialExpression

namespace Thesis.Probability.FiniteGibbsTilt
open ConstructiveReal
open Distros.RationalLinear

theorem expectation_congr (family : FiniteGibbsTilt states) (parameter : ConstructiveReal)
    (first second : Fin states → ConstructiveReal) (same : ∀ i, Equiv (first i) (second i)) :
    Equiv (family.expectation parameter first) (family.expectation parameter second) :=
  FiniteLinear.pair_congr states first second _ _ same (fun _ => equiv_refl _)

theorem expectation_add (family : FiniteGibbsTilt states) (parameter : ConstructiveReal)
    (first second : Fin states → ConstructiveReal) :
    Equiv (family.expectation parameter (fun i => add (first i) (second i)))
      (add (family.expectation parameter first) (family.expectation parameter second)) :=
  FiniteLinear.pair_add_first states first second (family.mass parameter)

theorem expectation_sub (family : FiniteGibbsTilt states) (parameter : ConstructiveReal)
    (first second : Fin states → ConstructiveReal) :
    Equiv (family.expectation parameter (fun i => sub (first i) (second i)))
      (sub (family.expectation parameter first) (family.expectation parameter second)) :=
  FiniteLinear.pair_sub_first states first second (family.mass parameter)

theorem expectation_scale (family : FiniteGibbsTilt states) (parameter factor : ConstructiveReal)
    (observable : Fin states → ConstructiveReal) :
    Equiv (family.expectation parameter (fun i => mul factor (observable i)))
      (mul factor (family.expectation parameter observable)) :=
  FiniteLinear.pair_scale_first states factor observable (family.mass parameter)

theorem expectation_constant (family : FiniteGibbsTilt states) (parameter value : ConstructiveReal) :
    Equiv (family.expectation parameter (fun _ => value)) value :=
  equiv_trans (FiniteLinear.pair_congr states _ (fun _ => mul value one) _ _
    (fun _ => equiv_symm (mul_one value)) (fun _ => equiv_refl _))
    (equiv_trans (FiniteLinear.pair_scale_first states value (fun _ => one) (family.mass parameter))
      (equiv_trans (mul_congr (equiv_refl _) (equiv_trans
        (equiv_symm (FiniteLinear.realDot_pair states (fun _ => 1) (family.mass parameter))) (family.normalized parameter))) (mul_one value)))

theorem expectation_nonnegative (family : FiniteGibbsTilt states) (parameter : ConstructiveReal)
    (observable : Fin states → ConstructiveReal) (nonnegative : ∀ i, LE zero (observable i)) :
    LE zero (family.expectation parameter observable) := by
  apply listSum_nonnegative
  intro value member
  obtain ⟨i, _, same⟩ := List.mem_map.mp member
  cases same
  exact mul_nonnegative (nonnegative i) (family.mass_nonnegative parameter i)

theorem covariance_comm (family : FiniteGibbsTilt states) (parameter : ConstructiveReal)
    (first second : Fin states → ConstructiveReal) :
    Equiv (family.covariance parameter first second) (family.covariance parameter second first) :=
  add_congr (family.expectation_congr parameter _ _ (fun i => mul_comm _ _)) (neg_congr (mul_comm _ _))

private abbrev Expression := RationalPolynomial.Expression 2
private def valueExpr : Expression := .coordinate 0
private def meanExpr : Expression := .coordinate 1
private def centeredExpr : Expression := .mul (.sub valueExpr meanExpr) (.sub valueExpr meanExpr)
private def expandedExpr : Expression := .sub (.add (.mul valueExpr valueExpr) (.mul meanExpr meanExpr))
  (.mul (.add meanExpr meanExpr) valueExpr)

/-- Variance equals the expectation of the squared centered observable.
Normalization is used through the proved constant-expectation identity. -/
theorem variance_centered (family : FiniteGibbsTilt states) (parameter : ConstructiveReal)
    (observable : Fin states → ConstructiveReal) :
    Equiv (family.expectation parameter (fun i =>
      mul (sub (observable i) (family.expectation parameter observable)) (sub (observable i) (family.expectation parameter observable))))
      (family.covariance parameter observable observable) := by
  let mean := family.expectation parameter observable
  have pointwise (i : Fin states) : Equiv (mul (sub (observable i) mean) (sub (observable i) mean))
      (sub (add (mul (observable i) (observable i)) (mul mean mean)) (mul (add mean mean) (observable i))) :=
    RationalPolynomial.Expression.equalityCheck_sound_real centeredExpr expandedExpr (by decide +kernel)
      (fun j => if j = 0 then observable i else mean)
  have expanded := equiv_trans (family.expectation_congr parameter _ _ pointwise)
    (equiv_trans (family.expectation_sub parameter _ _) (add_congr
      (equiv_trans (family.expectation_add parameter _ _) (add_congr (equiv_refl _) (family.expectation_constant parameter (mul mean mean))))
      (neg_congr (family.expectation_scale parameter (add mean mean) observable))))
  exact equiv_trans expanded (RationalPolynomial.Expression.equalityCheck_sound_real
    (.sub (.add valueExpr (.mul meanExpr meanExpr)) (.mul (.add meanExpr meanExpr) meanExpr))
    (.sub valueExpr (.mul meanExpr meanExpr)) (by decide +kernel)
    (fun i => if i = 0 then family.expectation parameter (fun j => mul (observable j) (observable j)) else mean))

/-- Log-partition curvature is nonnegative: its variance formula is a proved
finite square expectation, including constant or redundant observables. -/
theorem variance_nonnegative (family : FiniteGibbsTilt states) (parameter : ConstructiveReal)
    (observable : Fin states → ConstructiveReal) : LE zero (family.covariance parameter observable observable) :=
  (le_congr (equiv_refl _) (family.variance_centered parameter observable)).mp
    (family.expectation_nonnegative parameter _ (fun i => square_nonnegative _))

theorem covariance_constant (family : FiniteGibbsTilt states) (parameter value : ConstructiveReal)
    (observable : Fin states → ConstructiveReal) :
    Equiv (family.covariance parameter (fun _ => value) observable) zero :=
  (sub_equiv_zero_iff _ _).mpr (equiv_trans (family.expectation_scale parameter value observable)
    (mul_congr (equiv_symm (family.expectation_constant parameter value)) (equiv_refl _)))

end Thesis.Probability.FiniteGibbsTilt
