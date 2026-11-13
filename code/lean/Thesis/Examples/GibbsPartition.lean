import Thesis.Probability.ConstructiveRealFittedGibbsCertificates

namespace Thesis.Examples.GibbsPartition
open Probability ConstructiveReal
open Probability.Distros.RationalLinear

/-- Repeated features are intentional. Reference weights 1 and 2 produce
an exactly rational nonuniform law at zero parameters. -/
private def family : FiniteGibbsFamily 2 2 := {
  nonempty := by decide
  reference i := if i = 0 then PositiveRatio.one else PositiveRatio.ofNat 2 (by decide)
  response _ i := if i = 1 then SignedRatio.one else SignedRatio.zero }
private def parameters : Fin 2 → ConstructiveReal := fun _ => zero
private def third : SignedRatio := ⟨1, 3, by decide⟩
private def twoThirds : SignedRatio := ⟨2, 3, by decide⟩
private def three : SignedRatio := ⟨3, 1, by decide⟩
private def variance : SignedRatio := ⟨2, 9, by decide⟩
private def rationalMass (i : Fin 2) : SignedRatio := if i = 0 then third else twoThirds

private theorem two_cases (i : Fin 2) : i = 0 ∨ i = 1 :=
  (by decide +kernel : ∀ j : Fin 2, j = 0 ∨ j = 1) i

private theorem partition_exact : Equiv (family.partition parameters) (ofSignedRatio three) := by
  have weights := listSum_map_congr (List.finRange 2) _ _ (fun i _ => family.weight_zero i)
  apply equiv_trans weights
  change Equiv (add one (add (ofSignedRatio (PositiveRatio.ofNat 2 (by decide)).toSignedRatio) zero)) (ofSignedRatio three)
  exact equiv_trans (add_congr (equiv_refl _) (add_zero _))
    (equiv_trans (ofSignedRatio_add _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel)))

private theorem inverse_exact : Equiv ((family.asTilt parameters).partitionInverse one) (ofSignedRatio third) :=
  inverse_unique (family.partition parameters) _ _
    ((family.partition parameters).mul_positiveInverse _ ((family.asTilt parameters).partition_positive one))
    (equiv_trans (mul_congr partition_exact (equiv_refl _))
      (equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel))))

private theorem mass_exact (i : Fin 2) : Equiv (family.mass parameters i) (ofSignedRatio (rationalMass i)) := by
  apply equiv_trans (mul_congr (family.weight_zero i) inverse_exact)
  apply equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr ?_)
  rcases two_cases i with rfl | rfl <;> decide +kernel

private def indicator (i : Fin 2) : ConstructiveReal := realInteger (if i = 1 then 1 else 0)
private theorem feature_indicator (j i : Fin 2) : Equiv (family.feature j i) (indicator i) := by
  by_cases last : i = 1
  · subst i; exact equiv_refl one
  · change Equiv (ofSignedRatio (if i = 1 then SignedRatio.one else SignedRatio.zero)) (realInteger (if i = 1 then 1 else 0))
    rw [if_neg last, if_neg last]
    exact equiv_refl zero

private theorem expectation_exact (j : Fin 2) : Equiv (family.expectation parameters (family.feature j)) (ofSignedRatio twoThirds) :=
  equiv_trans ((family.asTilt parameters).expectation_congr one _ _ (feature_indicator j))
    (equiv_trans (FiniteLinear.pair_unit 2 1 (family.mass parameters)) (mass_exact 1))

private theorem indicator_square (i : Fin 2) : Equiv (mul (indicator i) (indicator i)) (indicator i) := by
  by_cases last : i = 1
  · subst i; exact one_mul one
  · change Equiv (mul (realInteger (if i = 1 then 1 else 0)) (realInteger (if i = 1 then 1 else 0))) (realInteger (if i = 1 then 1 else 0))
    rw [if_neg last]
    exact zero_mul zero

private theorem covariance_exact (j k : Fin 2) : Equiv (family.covariance parameters (family.feature j) (family.feature k)) (ofSignedRatio variance) := by
  have product (i : Fin 2) : Equiv (mul (family.feature j i) (family.feature k i)) (family.feature j i) :=
    equiv_trans (mul_congr (feature_indicator j i) (feature_indicator k i))
      (equiv_trans (indicator_square i) (equiv_symm (feature_indicator j i)))
  have cross := equiv_trans ((family.asTilt parameters).expectation_congr one _ _ product) (expectation_exact j)
  exact equiv_trans (add_congr cross (neg_congr (mul_congr (expectation_exact j) (expectation_exact k))))
    (equiv_trans (add_congr (equiv_refl _) (neg_congr (ofSignedRatio_mul _ _)))
      (equiv_trans (ofSignedRatio_sub _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel))))

/-- The actual derivative has the independently calculated slope -2/3. -/
example (j : Fin 2) : HasDerivativeAt
    (fun t => family.logPartition (FiniteGibbsFamily.shift parameters (FiniteGibbsFamily.unitDirection j) t)) zero
      (ofSignedRatio (SignedRatio.neg twoThirds)) :=
  (family.logPartition_partial parameters j).slope_congr
    (equiv_trans (neg_congr (expectation_exact j)) (equiv_symm (ofSignedRatio_neg _)))

/-- Both mixed and diagonal natural-log curvature equal 2/9. -/
example (j k : Fin 2) : HasDerivativeAt
    (fun t => neg (family.expectation (FiniteGibbsFamily.shift parameters (FiniteGibbsFamily.unitDirection k) t) (family.feature j))) zero
      (ofSignedRatio variance) := (family.logPartition_mixed parameters j k).slope_congr (covariance_exact j k)

/-- Redundancy makes a genuine zero-curvature observable, although each
individual feature has positive variance. No strict-curvature claim is made. -/
example : Equiv (family.covariance parameters
    (fun i => sub (family.feature 0 i) (family.feature 1 i))
    (fun i => sub (family.feature 0 i) (family.feature 1 i))) zero := by
  have vanished (i : Fin 2) : Equiv (sub (family.feature 0 i) (family.feature 1 i)) zero :=
    (sub_equiv_zero_iff _ _).mpr (equiv_trans (feature_indicator 0 i) (equiv_symm (feature_indicator 1 i)))
  exact equiv_trans (family.covariance_observables_congr parameters _ (fun _ => zero) _ (fun _ => zero) vanished vanished)
    ((family.asTilt parameters).covariance_constant one zero (fun _ => zero))

/-- Reference weights affect entropy through the explicit log-reference
expectation, even at zero parameters and for repeated features. -/
example : Equiv (mul (family.entropy parameters) lnTwo)
    (sub (add (family.logPartition parameters)
      (FiniteLinear.pair 2 parameters (fun j => family.expectation parameters (family.feature j))))
      (family.expectation parameters family.logReference)) := family.entropy_partition parameters

end Thesis.Examples.GibbsPartition
