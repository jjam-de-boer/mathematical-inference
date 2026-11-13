import Thesis.Probability.ConstructiveProbabilityCurve
import Thesis.Probability.ConstructiveUniformElementary
import Thesis.Probability.FinitePhysicalEnsembles
import Thesis.Probability.ConstructiveRealLogInverse

namespace Thesis.Examples.BinaryGibbsCurve
open Probability ConstructiveReal
open Probability.Distros.RationalLinear

/-- A fixed-particle binary physical model with energies zero and one. -/
def model : FinitePhysicalModel 2 := {
  nonempty := by decide
  energy i := if i = 0 then SignedRatio.zero else SignedRatio.one
  particles _ := 1 }
def two : ConstructiveReal := ofSignedRatio ⟨2, 1, by decide⟩
def domain (t : ConstructiveReal) : Prop := LE one t ∧ LE t two
private theorem zero_le_one : LE zero one := (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
private def argument (t : ConstructiveReal) : ConstructiveReal := add (mul t (neg one)) zero
private theorem argument_negative (t : ConstructiveReal) : Equiv (argument t) (neg t) :=
  equiv_trans (add_zero _) (equiv_trans (mul_neg t one) (neg_congr (mul_one t)))
private def weight (t : ConstructiveReal) : ConstructiveReal := (argument t).exp
private def weightVelocity (t : ConstructiveReal) : ConstructiveReal := mul (neg one) (weight t)
private def denominator (t : ConstructiveReal) : ConstructiveReal := add one (weight t)
private theorem denominator_positive (t : ConstructiveReal) : LE one (denominator t) :=
  (le_congr (add_zero one) (equiv_refl _)).mp (add_le_add (le_refl one) (exp_nonnegative _))
private def inverse (t : ConstructiveReal) : ConstructiveReal := (denominator t).positiveInverse PositiveRatio.one (denominator_positive t)
private def firstVelocity (t : ConstructiveReal) : ConstructiveReal := mul (weight t) (mul (inverse t) (inverse t))
private def masses (i : Fin 2) (t : ConstructiveReal) : ConstructiveReal := if i = 0 then inverse t else sub one (inverse t)
private def velocities (i : Fin 2) (t : ConstructiveReal) : ConstructiveReal := if i = 0 then firstVelocity t else neg (firstVelocity t)

private theorem velocity_algebra (e p : ConstructiveReal) :
    Equiv (mul (mul (neg one) e) (neg (mul p p))) (mul e (mul p p)) :=
  equiv_trans (mul_congr (equiv_trans (neg_mul one e) (neg_congr (one_mul e))) (equiv_refl _))
    (equiv_trans (neg_mul e _) (equiv_trans (neg_congr (mul_neg e _)) (neg_neg _)))
private def weightDerivative (t : ConstructiveReal) : HasDerivativeAt weight t (weightVelocity t) :=
  exp_affine_hasDerivativeAt t (neg one) zero
private def denominatorDerivative (t : ConstructiveReal) : HasDerivativeAt denominator t (weightVelocity t) :=
  ((HasDerivativeAt.constant t one).add (weightDerivative t)).slope_congr (zero_add _)
private def inverseDerivative (t : ConstructiveReal) : HasDerivativeAt inverse t (firstVelocity t) :=
  (((denominatorDerivative t).chainWithin (positiveInverse_hasDerivativeWithinAt (denominator t) PositiveRatio.one (denominator_positive t))).unrestrict denominator_positive).slope_congr
    (velocity_algebra (weight t) (inverse t))

private theorem weight_zero (t : ConstructiveReal) : Equiv (model.canonical.weight t (0 : Fin 2)) one :=
  equiv_trans (exp_congr (equiv_trans (add_zero _) (equiv_trans (mul_neg _ zero)
    (equiv_trans (neg_congr (mul_zero _)) (equiv_symm (ofSignedRatio_neg SignedRatio.zero)))))) exp_zero
private theorem partition_eq (t : ConstructiveReal) : Equiv (model.canonical.partition t) (denominator t) := by
  change Equiv (add (model.canonical.weight t 0) (add (weight t) zero)) _
  exact add_congr (weight_zero t) (add_zero _)
private theorem inverse_eq (t : ConstructiveReal) : Equiv (model.canonical.partitionInverse t) (inverse t) :=
  positiveInverse_congr (partition_eq t) _ PositiveRatio.one (model.canonical.partition_positive t) (denominator_positive t)
private theorem mass_zero (t : ConstructiveReal) : Equiv (model.canonical.mass t (0 : Fin 2)) (inverse t) :=
  equiv_trans (mul_congr (weight_zero t) (inverse_eq t)) (one_mul _)
private theorem mass_one (t : ConstructiveReal) : Equiv (model.canonical.mass t (1 : Fin 2)) (sub one (inverse t)) := by
  have normalized := model.canonical.normalized t
  change Equiv (add (mul one (model.canonical.mass t 1)) (add (mul one (model.canonical.mass t 0)) zero)) one at normalized
  have sum : Equiv (add (inverse t) (model.canonical.mass t 1)) one :=
    equiv_trans (add_comm _ _) (equiv_trans (add_congr (equiv_refl _) (equiv_symm (mass_zero t)))
      (equiv_trans (equiv_symm (add_congr (one_mul _) (equiv_trans (add_congr (one_mul _) (equiv_refl zero)) (add_zero _)))) normalized))
  exact equiv_trans (equiv_symm (add_sub_cancel (inverse t) (model.canonical.mass t 1))) (add_congr sum (equiv_refl _))
private theorem masses_eq (t : ConstructiveReal) (i : Fin 2) : Equiv (masses i t) (model.canonical.mass t i) := by
  have cases := (by decide +kernel : ∀ j : Fin 2, j = 0 ∨ j = 1) i
  rcases cases with rfl | rfl
  · exact equiv_symm (mass_zero t)
  · exact equiv_symm (mass_one t)

private theorem argument_bounds (t : ConstructiveReal) (inside : domain t) : LE (neg two) (argument t) ∧ LE (argument t) zero := by
  have nonnegative := le_trans zero_le_one inside.1
  exact ⟨(le_congr (equiv_refl _) (argument_negative t)).mpr ((neg_le_neg_iff t two).mpr inside.2),
    (le_congr (argument_negative t) (equiv_symm (ofSignedRatio_neg SignedRatio.zero))).mpr ((neg_le_neg_iff zero t).mpr nonnegative)⟩
private theorem weight_upper (t : ConstructiveReal) (inside : domain t) : LE (weight t) one :=
  (le_congr (equiv_refl _) exp_zero).mp ((exp_le_exp_iff _ zero).mpr (argument_bounds t inside).2)
private theorem weight_lower (t : ConstructiveReal) (inside : domain t) : LE (ofSignedRatio (neg two).expLower.toSignedRatio) (weight t) :=
  le_trans (exp_lower (neg two)) ((exp_le_exp_iff _ _).mpr (argument_bounds t inside).1)
private theorem inverse_nonnegative (t : ConstructiveReal) : LE zero (inverse t) :=
  (denominator t).positiveInverse_nonnegative PositiveRatio.one (denominator_positive t)
private theorem inverse_upper (t : ConstructiveReal) : LE (inverse t) one :=
  (denominator t).positiveInverse_upper PositiveRatio.one (denominator_positive t)
private def half : PositiveRatio := ⟨1, 2, by decide, by decide⟩
private theorem inverse_lower (t : ConstructiveReal) (inside : domain t) : LE (ofSignedRatio half.toSignedRatio) (inverse t) := by
  have upper : LE (denominator t) two :=
    (le_congr (equiv_refl _) (equiv_trans (ofSignedRatio_add _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel)))).mp
      (add_le_add (le_refl one) (weight_upper t inside))
  have estimate := positiveInverse_antitone (denominator t) two PositiveRatio.one (PositiveRatio.ofNat 2 (by decide))
    (denominator_positive t) (le_refl two) upper
  exact (le_congr (ofPositiveRatio_inverse (PositiveRatio.ofNat 2 (by decide)) (PositiveRatio.ofNat 2 (by decide)) (le_refl two)) (equiv_refl _)).mp estimate
private def floor : PositiveRatio := (neg two).expLower.mul half
private theorem floor_le_half : LE (ofSignedRatio floor.toSignedRatio) (ofSignedRatio half.toSignedRatio) := by
  have twoNonnegative : LE zero two := (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
  have nonpositive : LE (neg two) zero :=
    (le_congr (equiv_refl _) (equiv_symm (ofSignedRatio_neg SignedRatio.zero))).mp ((neg_le_neg_iff zero two).mpr twoNonnegative)
  have lowerUnit := le_trans (exp_lower (neg two)) ((le_congr (equiv_refl _) exp_zero).mp ((exp_le_exp_iff _ _).mpr nonpositive))
  exact (le_congr (equiv_refl _) (one_mul _)).mp (mul_positive_lower one (ofSignedRatio half.toSignedRatio)
    (neg two).expLower half lowerUnit (le_refl _))
private theorem masses_positive (i : Fin 2) (t : ConstructiveReal) (inside : domain t) : LE (ofSignedRatio floor.toSignedRatio) (masses i t) := by
  have cases := (by decide +kernel : ∀ j : Fin 2, j = 0 ∨ j = 1) i
  rcases cases with rfl | rfl
  · exact le_trans floor_le_half (inverse_lower t inside)
  · have product := mul_positive_lower (weight t) (inverse t) (neg two).expLower half (weight_lower t inside) (inverse_lower t inside)
    have represented : Equiv (masses (1 : Fin 2) t) (mul (weight t) (inverse t)) :=
      equiv_trans (masses_eq t 1) (mul_congr (equiv_refl (weight t)) (inverse_eq t))
    exact (le_congr (equiv_refl _) (equiv_symm represented)).mp product

private def expDomain (x : ConstructiveReal) : Prop := LE (neg two) x ∧ LE x zero
private def weightUniform : UniformDerivativeWithin domain (fun t _ => weight t) (fun t _ => weightVelocity t) :=
  (exp_uniformDerivative expDomain (intervalMagnitudeBound (neg two) zero)
    (fun x hx precision fine => magnitude_bounded_of_interval x _ _ hx.1 hx.2 precision fine)).affine_pullback
      (neg one) zero argument_bounds
private def denominatorUniform : UniformDerivativeWithin domain (fun t _ => denominator t) (fun t _ => weightVelocity t) :=
  ((UniformDerivativeWithin.constant domain one).add weightUniform).slope_congr (fun _ _ => zero_add _)
private theorem weightVelocity_bounds (t : ConstructiveReal) (inside : domain t) :
    LE (neg one) (weightVelocity t) ∧ LE (weightVelocity t) zero := by
  have same : Equiv (weightVelocity t) (neg (weight t)) := equiv_trans (neg_mul one _) (neg_congr (one_mul _))
  exact ⟨(le_congr (equiv_refl _) (equiv_symm same)).mp ((neg_le_neg_iff _ _).mpr (weight_upper t inside)),
    (le_congr (equiv_symm same) (equiv_symm (ofSignedRatio_neg SignedRatio.zero))).mp
      ((neg_le_neg_iff zero (weight t)).mpr (exp_nonnegative _))⟩
private def inverseUniform : UniformDerivativeWithin domain (fun t _ => inverse t) (fun t _ => firstVelocity t) :=
  (denominatorUniform.chainWithin (positiveInverse_uniformDerivative PositiveRatio.one) (fun t _ => denominator_positive t)
    (intervalMagnitudeBound (neg one) zero) (inverseSlopeMagnitudeBound PositiveRatio.one)
    (fun t hx precision fine => magnitude_bounded_of_interval _ _ _ (weightVelocity_bounds t hx).1 (weightVelocity_bounds t hx).2 precision fine)
    (fun x hx precision fine => inverseSlope_magnitude_bounded x PositiveRatio.one hx precision fine)).slope_congr
      (fun t _ => velocity_algebra (weight t) (inverse t))
private def secondUniform : UniformDerivativeWithin domain (fun t _ => sub one (inverse t)) (fun t _ => neg (firstVelocity t)) :=
  ((UniformDerivativeWithin.constant domain one).add inverseUniform.neg).slope_congr (fun _ _ => zero_add _)
private theorem firstVelocity_bounds (t : ConstructiveReal) (inside : domain t) : LE zero (firstVelocity t) ∧ LE (firstVelocity t) one := by
  have squared : LE (mul (inverse t) (inverse t)) one :=
    (le_congr (equiv_refl _) (one_mul one)).mp (square_le_square (inverse_nonnegative t) (inverse_upper t))
  exact ⟨mul_nonnegative (exp_nonnegative _) (square_nonnegative _),
    (le_congr (equiv_refl _) (one_mul one)).mp (mul_le_mul (weight_upper t inside) squared (exp_nonnegative _) zero_le_one)⟩

/-- The actual varying binary Gibbs law is a regular probability curve.
All its coordinate, velocity, positivity and uniform remainder certificates
are constructed above; none is assumed as a fixture premise. -/
def curve : RegularProbabilityCurve 2 domain where
  mass := masses
  velocity := velocities
  pointDerivative i t _ := by
    by_cases first : i = 0
    · subst i
      exact inverseDerivative t
    · have second : i = 1 := ((by decide +kernel : ∀ j : Fin 2, j = 0 ∨ j = 1) i).resolve_left first
      subst i
      exact ((HasDerivativeAt.constant t one).add (inverseDerivative t).neg).slope_congr (zero_add _)
  normalized t := equiv_trans (realDot_congr_values 2 (fun _ => 1) _ _ (masses_eq t)) (model.canonical.normalized t)
  uniformDerivative i := by
    by_cases first : i = 0
    · subst i
      exact inverseUniform
    · have second : i = 1 := ((by decide +kernel : ∀ j : Fin 2, j = 0 ∨ j = 1) i).resolve_left first
      subst i
      exact secondUniform
  lower _ := floor
  positive := masses_positive
  bounded i t _ := (le_congr (masses_eq t i) (equiv_refl _)).mpr (model.canonical.probability t i).bounded
  velocityLower _ := neg one
  velocityUpper _ := one
  velocityBounds i t hx := by
    have cases := (by decide +kernel : ∀ j : Fin 2, j = 0 ∨ j = 1) i
    have first := firstVelocity_bounds t hx
    have negativeOne : LE (neg one) zero :=
      (le_congr (equiv_refl _) (equiv_symm (ofSignedRatio_neg SignedRatio.zero))).mp ((neg_le_neg_iff zero one).mpr zero_le_one)
    rcases cases with rfl | rfl
    · exact ⟨le_trans negativeOne first.1, first.2⟩
    · exact ⟨(neg_le_neg_iff _ _).mpr first.2, le_trans
        ((le_congr (equiv_refl _) (equiv_symm (ofSignedRatio_neg SignedRatio.zero))).mp ((neg_le_neg_iff _ _).mpr first.1)) zero_le_one⟩

theorem curve_is_gibbs (t : ConstructiveReal) (i : Fin 2) : Equiv (curve.mass i t) (model.canonical.mass t i) := masses_eq t i

example : UniformDerivativeWithin domain curve.entropy curve.bitRate := curve.entropy_uniformDerivative
example (t : ConstructiveReal) (inside : domain t) : Equiv (realDot 2 (fun _ => 1) (fun i => curve.velocity i t)) zero :=
  curve.normalized_velocity t inside

end Thesis.Examples.BinaryGibbsCurve
