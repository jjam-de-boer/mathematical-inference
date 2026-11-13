import Thesis.Probability.ConstructiveRealPolynomialExpression
import Thesis.Probability.ConstructiveRealReciprocal
import Thesis.Probability.ConstructiveRealDistanceScaling

namespace Thesis.Probability.ConstructiveReal

private abbrev Expr := RationalPolynomial.Expression 2
private def v : Expr := .coordinate 0
private def r : Expr := .coordinate 1
private def expandedGap : Expr := .sub (.add (.mul v v) (.mul r r)) (.mul (.add r r) v)
private theorem square_gap (value radius : ConstructiveReal) :
    Equiv (mul (sub value radius) (sub value radius))
      (sub (add (mul value value) (mul radius radius)) (mul (add radius radius) value)) :=
  RationalPolynomial.Expression.equalityCheck_sound_real (.mul (.sub v r) (.sub v r)) expandedGap
    (by decide +kernel) (fun index => if index.val = 0 then value else radius)

private theorem square_upper (value : ConstructiveReal) (radius : PositiveRatio)
    (bounded : LE (mul value value) (mul (ofSignedRatio radius.toSignedRatio) (ofSignedRatio radius.toSignedRatio))) :
    LE value (ofSignedRatio radius.toSignedRatio) := by
  let r := ofSignedRatio radius.toSignedRatio
  have nonnegative := (le_congr (equiv_refl zero) (square_gap value r)).mp (square_nonnegative (sub value r))
  have comparison := (zero_le_sub_iff _ _).mp nonnegative
  have doubled : Equiv (add (mul r r) (mul r r)) (mul (add r r) r) := equiv_symm (add_mul r r r)
  have upper := (le_congr (equiv_refl _) doubled).mp (add_le_add bounded (le_refl (mul r r)))
  have radiusPositive : LE zero r := (ofSignedRatio_le_iff _ _).mpr
    ((SignedRatio.toSignedRatio_le_iff _ _).mpr (QProb.zero_le radius.toQProb))
  have lower : LE r (add r r) :=
    (le_congr (add_zero r) (equiv_refl _)).mp (add_le_add (le_refl r) radiusPositive)
  exact (mul_le_mul_positive_iff (add r r) radius lower value r).mp (le_trans comparison upper)

/-- A squared distance bound gives an actual rational distance certificate,
without square roots or a decision of the sign of the real difference. -/
theorem within_zero_of_square_le (value : ConstructiveReal) (radius : PositiveRatio)
    (bounded : LE (mul value value) (mul (ofSignedRatio radius.toSignedRatio) (ofSignedRatio radius.toSignedRatio))) :
    Within radius.toQProb value zero := by
  have upper := square_upper value radius bounded
  have negSquare : Equiv (mul (neg value) (neg value)) (mul value value) :=
    equiv_trans (neg_mul value (neg value)) (equiv_trans (neg_congr (mul_neg value value)) (neg_neg _))
  have lower := square_upper (neg value) radius ((le_congr negSquare (equiv_refl _)).mpr bounded)
  have shifted := add_le_add (le_refl value) lower
  have positive : LE zero (add value (ofSignedRatio radius.toSignedRatio)) :=
    (le_congr (add_neg value) (equiv_refl _)).mp shifted
  exact ⟨(le_congr (equiv_refl _) (zero_add _)).mpr upper, positive⟩

theorem within_of_square_sub_le (x y : ConstructiveReal) (radius : PositiveRatio)
    (bounded : LE (mul (sub x y) (sub x y))
      (mul (ofSignedRatio radius.toSignedRatio) (ofSignedRatio radius.toSignedRatio))) :
    Within radius.toQProb x y := by
  have close := within_zero_of_square_le (sub x y) radius bounded
  exact (within_sub_right_iff radius.toQProb y x y).mp
    ((within_congr (equiv_refl _) (equiv_symm ((sub_equiv_zero_iff y y).mpr (equiv_refl y)))).mp close)

/-- Vanishing squared distance separates real values constructively. -/
theorem equiv_of_square_sub_zero (x y : ConstructiveReal)
    (vanished : LE (mul (sub x y) (sub x y)) zero) : Equiv x y := by
  apply equiv_of_within_all
  intro radius
  exact within_of_square_sub_le x y radius (le_trans vanished (square_nonnegative _))

end Thesis.Probability.ConstructiveReal
