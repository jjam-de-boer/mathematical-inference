import Thesis.Probability.ConstructiveDerivativeWithin
import Thesis.Probability.ConstructiveRealDistanceAlgebra
import Thesis.Probability.ConstructiveRealDifferenceLimits

namespace Thesis.Probability.ConstructiveReal

private def sharedRadius (first second : PositiveRatio) : PositiveRatio :=
  if PositiveRatio.LE first second then first else second

private theorem sharedRadius_bounds (first second : PositiveRatio) :
    PositiveRatio.LE (sharedRadius first second) first ∧ PositiveRatio.LE (sharedRadius first second) second := by
  by_cases ordered : PositiveRatio.LE first second
  · simp only [sharedRadius, if_pos ordered]; exact ⟨PositiveRatio.le_refl _, ordered⟩
  · simp only [sharedRadius, if_neg ordered]; exact ⟨(PositiveRatio.le_total first second).resolve_left ordered, PositiveRatio.le_refl _⟩

private theorem negative_shift_increment (point : ConstructiveReal) (radius : PositiveRatio) :
    Equiv (sub (add point (neg (ofSignedRatio radius.toSignedRatio))) point) (neg (ofSignedRatio radius.toSignedRatio)) :=
  equiv_trans (add_congr (add_comm _ _) (equiv_refl _))
    (equiv_trans (add_assoc _ _ _) (equiv_trans (add_congr (equiv_refl _) (add_neg point)) (add_zero _)))

private theorem within_negative_shift (point : ConstructiveReal) (radius : PositiveRatio) :
    Within radius.toQProb point (add point (neg (ofSignedRatio radius.toSignedRatio))) := by
  have shifted := within_neg (within_positive_shift zero radius)
  have left : Equiv (neg zero) zero := equiv_symm (ofSignedRatio_neg SignedRatio.zero)
  have right : Equiv (neg (add zero (ofSignedRatio radius.toSignedRatio))) (neg (ofSignedRatio radius.toSignedRatio)) :=
    neg_congr (zero_add _)
  have centered := (within_congr left right).mp shifted
  exact (within_congr (add_zero point) (equiv_refl _)).mp
    ((within_add_left_iff _ point _ _).mpr centered)

/-- A maximum and a derivative remainder bound control the signed linear
increment. This uses closed order only; the slope is never compared by a test. -/
private theorem maximum_increment_le {domain : ConstructiveReal → Prop} {f : ∀ x, domain x → ConstructiveReal}
    {point slope : ConstructiveReal} {inside : domain point}
    (derivative : HasDerivativeWithinAt domain f point inside slope)
    (epsilon radius : PositiveRatio) (small : PositiveRatio.LE radius (derivative.modulus epsilon))
    (nearby : ConstructiveReal) (admitted : domain nearby) (close : Within radius.toQProb point nearby)
    (maximum : LE (f nearby admitted) (f point inside)) :
    LE (mul (sub nearby point) slope) (ofSignedRatio (QProb.mul epsilon.toQProb radius.toQProb).toSignedRatio) := by
  have remainder := (derivative.remainder epsilon radius small nearby admitted close).2
  have compared := le_trans remainder (add_le_add maximum (le_refl _))
  have translated := (le_congr (add_comm _ _) (add_comm _ _)).mp compared
  exact (add_le_add_right_iff _ _ (f point inside)).mp translated

namespace HasDerivativeWithinAt

/-- Constructive Fermat theorem. A local maximum has zero slope when an
explicit two-sided rational neighborhood belongs to the domain. The proof
samples positive and negative rational steps shared with the derivative
modulus. A maximum on an isolated or one-sided domain is not enough. -/
theorem slope_zero_of_local_maximum {domain : ConstructiveReal → Prop} {f : ∀ x, domain x → ConstructiveReal}
    {point slope : ConstructiveReal} {inside : domain point}
    (derivative : HasDerivativeWithinAt domain f point inside slope)
    (radius : PositiveRatio) (admitted : ∀ nearby, Within radius.toQProb point nearby → domain nearby)
    (maximum : ∀ nearby supplied, Within radius.toQProb point nearby → LE (f nearby supplied) (f point inside)) :
    Equiv slope zero := by
  have slopeBound (negative : Bool) : LE (if negative then neg slope else slope) zero := by
    apply le_of_forall_rational_error
    intro epsilon
    let step := sharedRadius radius (derivative.modulus epsilon)
    have bounds := sharedRadius_bounds radius (derivative.modulus epsilon)
    let h := ofSignedRatio step.toSignedRatio
    let nearby := if negative then add point (neg h) else add point h
    have close : Within step.toQProb point nearby := by
      cases negative
      · exact within_positive_shift point step
      · exact within_negative_shift point step
    have wider := within_mono close bounds.1
    have increment := maximum_increment_le derivative epsilon step bounds.2 nearby (admitted nearby wider) close
      (maximum nearby (admitted nearby wider) wider)
    have linear : Equiv (mul (sub nearby point) slope) (mul h (if negative then neg slope else slope)) := by
      cases negative
      · exact mul_congr (positive_shift_increment point step) (equiv_refl _)
      · exact equiv_trans (mul_congr (negative_shift_increment point step) (equiv_refl _))
          (equiv_trans (neg_mul _ _) (equiv_symm (mul_neg _ _)))
    have product : Equiv (ofSignedRatio (QProb.mul epsilon.toQProb step.toQProb).toSignedRatio)
        (mul h (ofSignedRatio epsilon.toSignedRatio)) := by
      rw [QProb.toSignedRatio_mul]
      exact equiv_trans (equiv_symm (ofSignedRatio_mul _ _)) (mul_comm _ _)
    have canceled := (mul_le_mul_positive_iff h step (le_refl _) _ _).mp ((le_congr linear product).mp increment)
    exact (le_congr (equiv_refl _) (equiv_symm (zero_add _))).mp canceled
  have upper := slopeBound false
  have lower := (neg_le_neg_iff zero slope).mp
    ((le_congr (equiv_refl _) (ofSignedRatio_neg SignedRatio.zero)).mp (slopeBound true))
  exact ⟨upper, lower⟩

end HasDerivativeWithinAt
end Thesis.Probability.ConstructiveReal
