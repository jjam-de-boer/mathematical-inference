import Thesis.Probability.ConstructiveDerivativeWithin
import Thesis.Probability.ConstructiveDerivativeScaling
import Thesis.Probability.ConstructiveRealPositiveNeighborhood

namespace Thesis.Probability.ConstructiveReal

private def commonRadius (a b : PositiveRatio) : PositiveRatio := if PositiveRatio.LE a b then a else b
private theorem commonRadius_bounds (a b : PositiveRatio) :
    PositiveRatio.LE (commonRadius a b) a ∧ PositiveRatio.LE (commonRadius a b) b := by
  by_cases ordered : PositiveRatio.LE a b
  · simp only [commonRadius, if_pos ordered]; exact ⟨PositiveRatio.le_refl _, ordered⟩
  · simp only [commonRadius, if_neg ordered]; exact ⟨(PositiveRatio.le_total a b).resolve_left ordered, PositiveRatio.le_refl _⟩

/-- A domain-relative derivative gives a total-function derivative when a
computed neighborhood is admitted and the actual function agrees there.
This consumes membership proofs; it never decides membership of arbitrary reals. -/
def HasDerivativeWithinAt.toLocalTotal {domain : ConstructiveReal → Prop} {f : ∀ x, domain x → ConstructiveReal}
    {point slope : ConstructiveReal} {inside : domain point}
    (derivative : HasDerivativeWithinAt domain f point inside slope) (g : ConstructiveReal → ConstructiveReal)
    (radius : PositiveRatio) (admitted : ∀ y, Within radius.toQProb point y → domain y)
    (atPoint : Equiv (f point inside) (g point))
    (nearby : ∀ y close, Equiv (f y (admitted y close)) (g y)) : HasDerivativeAt g point slope where
  modulus epsilon := commonRadius radius (derivative.modulus epsilon)
  remainder epsilon rho small y close := by
    have bounds := commonRadius_bounds radius (derivative.modulus epsilon)
    have wider := within_mono close (PositiveRatio.le_trans small bounds.1)
    exact (within_congr (nearby y wider) (add_congr atPoint (equiv_refl _))).mp
      (derivative.remainder epsilon rho (PositiveRatio.le_trans small bounds.2) y (admitted y wider) close)

namespace HasDerivativeAt

/-- A differentiable map with a certified positive value at the point has
a computed neighborhood inside the corresponding half-sized positive domain. -/
def positiveRadius {f : ConstructiveReal → ConstructiveReal} {point slope : ConstructiveReal}
    (derivative : HasDerivativeAt f point slope) (lower : PositiveRatio) : PositiveRatio :=
  commonRadius (derivative.modulus PositiveRatio.one) (lower.half.divideNat derivative.localLipschitzConstant derivative.localLipschitzConstant_pos)

theorem positive_near {f : ConstructiveReal → ConstructiveReal} {point slope : ConstructiveReal}
    (derivative : HasDerivativeAt f point slope) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) (f point)) (y : ConstructiveReal)
    (close : Within (derivative.positiveRadius lower).toQProb point y) :
    LE (ofSignedRatio lower.half.toSignedRatio) (f y) := by
  have bounds := commonRadius_bounds (derivative.modulus PositiveRatio.one)
    (lower.half.divideNat derivative.localLipschitzConstant derivative.localLipschitzConstant_pos)
  have changed := derivative.local_within (derivative.positiveRadius lower) bounds.1 y close
  have errorBound := QProb.le_congr (QProb.equiv_refl _)
    (PositiveRatio.divide_mul lower.half derivative.localLipschitzConstant derivative.localLipschitzConstant_pos)
    (QProb.mul_le_mul bounds.2 (QProb.le_refl (QProb.ofNat derivative.localLipschitzConstant)))
  exact positive_half_lower (f point) (f y) lower bounded (within_symm (within_mono changed errorBound))

end HasDerivativeAt
end Thesis.Probability.ConstructiveReal
