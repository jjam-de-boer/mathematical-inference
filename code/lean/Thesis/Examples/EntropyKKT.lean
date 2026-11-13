import Thesis.Probability.ConstructiveRealFaceKKT
import Thesis.Probability.ConstructiveRealPolynomialExpression

namespace Thesis.Examples.EntropyKKT
open Probability Probability.Distros ConstructiveReal
open RationalLinear RationalEntropyProblem

private def lowerRow : RationalConstraint 2 :=
  ⟨fun i => if i = 1 then SignedRatio.neg SignedRatio.one else SignedRatio.zero, ⟨-4, 6, by decide⟩⟩
private def upperRow : RationalConstraint 2 :=
  ⟨fun i => if i = 1 then SignedRatio.one else SignedRatio.zero, SignedRatio.one⟩
private def problem : RationalEntropyProblem 2 := ⟨by decide, [lowerRow, upperRow, lowerRow]⟩
private instance : NeZero problem.rows.length := ⟨by decide +kernel⟩
private def vector : Fin 2 → SignedRatio := fun i => if i = 0 then ⟨2, 6, by decide⟩ else ⟨4, 6, by decide⟩
private def reference : problem.RealLaw := .ofRationalVector problem vector ⟨by decide +kernel, by decide +kernel⟩ (by decide +kernel)
private def floor : PositiveRatio := ⟨1, 6, by decide, by decide⟩

private theorem two_cases (index : Fin 2) : index = 0 ∨ index = 1 := by
  have closed : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide +kernel
  exact closed index

private theorem positive (index : Fin 2) : LE (ofSignedRatio floor.toSignedRatio) (reference.mass index).value := by
  apply (ofSignedRatio_le_iff _ _).mpr
  rcases two_cases index with rfl | rfl <;> decide +kernel

private def gradient (index : Fin 2) := entropyBitGradient (reference.mass index).value floor (positive index)
private def coefficients : Fin 3 → ConstructiveReal := fun row => realInteger (if row = 0 then 1 else 0)

private theorem score_eval (column : Fin 2) :
    Equiv (realRationalDot 3 (fun row => (problem.rows[row.val]).coefficients column) coefficients)
      (ofSignedRatio (lowerRow.coefficients column)) :=
  equiv_trans (realRationalDot_pair 3 _ coefficients)
    (equiv_trans (FiniteLinear.pair_comm 3 _ coefficients) (FiniteLinear.pair_unit 3 0 _))

private def two : PositiveRatio := .ofNat 2 (by decide)
private theorem double_mass : Equiv (reference.mass 1).value
    (mul (reference.mass 0).value (ofSignedRatio two.toSignedRatio)) :=
  equiv_trans ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel)) (equiv_symm (ofSignedRatio_mul _ _))

private theorem logarithm_increment : Equiv ((reference.mass 1).value.positiveLog2 floor (positive 1))
    (add ((reference.mass 0).value.positiveLog2 floor (positive 0)) one) := by
  have productPositive := mul_positive_lower (reference.mass 0).value (ofSignedRatio two.toSignedRatio) floor two (positive 0) (le_refl _)
  have first := positiveLog2_congr double_mass floor (floor.mul two) (positive 1) productPositive
  have product := positiveLog2_mul (reference.mass 0).value (ofSignedRatio two.toSignedRatio) floor two (positive 0) (le_refl _)
  have logTwo : Equiv ((ofSignedRatio two.toSignedRatio).positiveLog2 two (le_refl _)) one :=
    equiv_trans (positiveLog2_ofPositiveRatio two two (le_refl _)) (ExactLog.interpret_ofSignedRatio SignedRatio.one)
  exact equiv_trans first (equiv_trans product (add_congr (equiv_refl _) logTwo))

private theorem gradient_increment : Equiv (gradient 1) (add (gradient 0) (ofSignedRatio (lowerRow.coefficients 1))) := by
  let logarithm := (reference.mass 0).value.positiveLog2 floor (positive 0)
  let c := RationalLogSecant.limit
  have reorder : Equiv (add (add logarithm one) c) (add (add logarithm c) one) :=
    equiv_trans (add_assoc _ _ _) (equiv_trans (add_congr (equiv_refl _) (add_comm _ _)) (equiv_symm (add_assoc _ _ _)))
  exact equiv_trans (neg_congr (add_congr logarithm_increment (equiv_refl c)))
    (equiv_trans (neg_congr reorder) (equiv_trans (neg_add _ _)
      (add_congr (equiv_refl _) (equiv_symm (ofSignedRatio_neg SignedRatio.one)))))

/-- Only the active lower bound gets a nonzero coefficient: one bit. The
upper bound is loose, and a redundant lower occurrence gets coefficient zero. -/
private def certificate : problem.LagrangeCoefficients gradient where
  offset := gradient 0
  coefficient := coefficients
  represents column := by
    rcases two_cases column with rfl | rfl
    · exact equiv_trans (equiv_symm (add_zero (gradient 0)))
        (add_congr (equiv_refl _) (equiv_symm (score_eval 0)))
    · exact equiv_trans gradient_increment (add_congr (equiv_refl _) (equiv_symm (score_eval 1)))

private theorem row_exact (row : RationalConstraint 2) (above : row.Holds vector) (below : row.reverse.Holds vector) :
    Equiv (realRationalDot 2 row.coefficients (fun i => (reference.mass i).value)) (ofSignedRatio row.bound) :=
  ⟨(row.real_ofSignedRatio_iff vector).mpr above,
    (row.reverse_real_lower _).mp ((row.reverse.real_ofSignedRatio_iff vector).mpr below)⟩

private theorem activeSlack : Equiv (reference.rowSlack (0 : Fin 3)) zero :=
  (sub_equiv_zero_iff _ _).mpr (equiv_symm (row_exact lowerRow (by decide +kernel) (by decide +kernel)))

private theorem signed : certificate.KKTAt reference := by
  constructor
  · intro row
    by_cases active : row = 0
    · change LE zero (realInteger (if row = 0 then 1 else 0))
      rw [if_pos active]
      exact (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
    · change LE zero (realInteger (if row = 0 then 1 else 0))
      rw [if_neg active]
      exact le_refl zero
  · intro row
    by_cases active : row = 0
    · subst row
      exact equiv_trans (mul_congr (equiv_refl _) activeSlack) (mul_zero _)
    · change Equiv (mul (realInteger (if row = 0 then 1 else 0)) _) zero
      rw [if_neg active]
      exact zero_mul _

private def naturalCertificate : problem.LagrangeCoefficients
    (fun i => entropyNaturalGradient (reference.mass i).value floor (positive i)) :=
  certificate.scale lnTwo _ (fun i => entropyGradient_units (reference.mass i).value floor (positive i))

private theorem naturalSigned : naturalCertificate.KKTAt reference := by
  have factorPositive : LE zero lnTwo := le_trans
    ((ofSignedRatio_le_iff _ _).mpr ((SignedRatio.zero_le_iff_nonnegative _).mpr
      RationalLogSecant.limit.positiveInverseLower.signed_nonnegative)) lnTwo_lower
  exact signed.scale lnTwo factorPositive _ (fun i => entropyGradient_units (reference.mass i).value floor (positive i))

/-- The KKT theorem establishes the maximum; the fixture does not assume it. -/
private theorem maximal : reference.Maximal := reference.maximal_of_kkt (fun _ => floor) positive certificate signed
example : reference.Maximal := reference.maximal_of_natural_kkt (fun _ => floor) positive naturalCertificate naturalSigned

/-- A boundary competitor is feasible for the interval, so the global
conclusion is stronger than a local stationary-point calculation. -/
private def boundary : problem.RealLaw := .ofRationalVector problem
  (fun i => if i = 1 then SignedRatio.one else SignedRatio.zero) ⟨by decide +kernel, by decide +kernel⟩ (by decide +kernel)
example : LE boundary.entropy reference.entropy := maximal boundary

example (observed : problem.RealLaw) : LE (FiniteLinear.pair 2
    (fun i => sub (observed.mass i).value (reference.mass i).value) gradient) zero :=
  reference.maximum_variational maximal (fun _ => floor) positive observed

private def upperAtReference : RationalConstraint 2 := ⟨upperRow.coefficients, vector 1⟩
private theorem inactiveMargin : LE (ofSignedRatio (⟨1, 12, by decide, by decide⟩ : PositiveRatio).toSignedRatio) (reference.rowSlack (1 : Fin 3)) := by
  have evaluation := row_exact upperAtReference (by decide +kernel) (by decide +kernel)
  have slack : Equiv (reference.rowSlack (1 : Fin 3)) (ofSignedRatio (SignedRatio.sub upperRow.bound (vector 1))) :=
    equiv_trans (add_congr (equiv_refl _) (neg_congr evaluation)) (ofSignedRatio_sub _ _)
  exact (le_congr (equiv_refl _) slack).mpr ((ofSignedRatio_le_iff _ _).mpr (by decide +kernel))

example : Equiv (certificate.coefficient (1 : Fin 3)) zero :=
  signed.zero_of_positive_slack 1 ⟨1, 12, by decide, by decide⟩ inactiveMargin

example (other : problem.RealLaw) (optimal : other.Maximal) (index : Fin 2) :
    Equiv (other.mass index).value (reference.mass index).value := other.maximal_unique reference optimal maximal index

/-- The necessity theorem computes coefficients for the same redundant
interval fixture; no multiplier certificate is passed to the constructor. -/
private def computed := reference.kktMultipliers maximal (fun _ => floor) positive

private theorem computed_inactive : Equiv (computed.val.coefficient (1 : Fin 3)) zero :=
  computed.property.zero_of_positive_slack 1 ⟨1, 12, by decide, by decide⟩ inactiveMargin

private abbrev MultiplierExpression := RationalPolynomial.Expression 4
private def lambda0 : MultiplierExpression := .coordinate 0
private def lambda1 : MultiplierExpression := .coordinate 1
private def lambda2 : MultiplierExpression := .coordinate 2
private def offset : MultiplierExpression := .coordinate 3
private def affine0 : MultiplierExpression := .add offset
  (.add (.mul (.constant SignedRatio.zero) lambda2) (.add (.mul (.constant SignedRatio.zero) lambda1)
    (.add (.mul (.constant SignedRatio.zero) lambda0) (.constant SignedRatio.zero))))
private def affine1 : MultiplierExpression := .add offset
  (.add (.mul (.constant ⟨-1, 1, by decide⟩) lambda2) (.add (.mul (.constant SignedRatio.one) lambda1)
    (.add (.mul (.constant ⟨-1, 1, by decide⟩) lambda0) (.constant SignedRatio.zero))))

private theorem coefficient_gap (actual : problem.LagrangeCoefficients gradient) :
    Equiv (sub (gradient 0) (gradient 1))
      (sub (add (actual.coefficient (0 : Fin 3)) (actual.coefficient (2 : Fin 3))) (actual.coefficient (1 : Fin 3))) :=
  equiv_trans (add_congr (actual.represents 0) (neg_congr (actual.represents 1)))
    (RationalPolynomial.Expression.equalityCheck_sound_real (.sub affine0 affine1) (.sub (.add lambda0 lambda2) lambda1)
      (by decide +kernel) (fun i => if i = 0 then actual.coefficient 0 else if i = 1 then actual.coefficient 1
        else if i = 2 then actual.coefficient 2 else actual.offset))

private theorem actual_gap : Equiv (sub (gradient 0) (gradient 1)) one :=
  equiv_trans (add_congr (equiv_refl _) (neg_congr gradient_increment))
    (RationalPolynomial.Expression.equalityCheck_sound_real
      (.sub (.coordinate 0 : RationalPolynomial.Expression 1) (.add (.coordinate 0) (.constant ⟨-1, 1, by decide⟩)))
      (.constant SignedRatio.one) (by decide +kernel) (fun _ => gradient 0))

/-- Redundant active constraints need not have unique individual
multipliers. Their returned total is independently recovered as one bit,
and the genuinely inactive upper multiplier is proved zero above. -/
example : Equiv (add (computed.val.coefficient (0 : Fin 3)) (computed.val.coefficient (2 : Fin 3))) one := by
  have gap := equiv_trans (coefficient_gap computed.val)
    (equiv_trans (add_congr (equiv_refl _) (neg_congr computed_inactive))
      (equiv_trans (add_congr (equiv_refl _) (equiv_symm (ofSignedRatio_neg SignedRatio.zero))) (add_zero _)))
  exact equiv_trans (equiv_symm gap) actual_gap

example : reference.Maximal ↔ ∃ actual : problem.LagrangeCoefficients gradient, actual.KKTAt reference :=
  reference.maximal_iff_kkt (fun _ => floor) positive

end Thesis.Examples.EntropyKKT
