import Thesis.Probability.ConstructiveRealCauchy

namespace Thesis.Probability.ConstructiveReal

/-- Closeness to a value with a known positive rational lower bound keeps
the nearby value above half that bound. No real order decision is needed. -/
theorem positive_half_lower (x y : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) (close : Within lower.half.toQProb x y) :
    LE (ofSignedRatio lower.half.toSignedRatio) y := by
  have compared := le_trans bounded close.1
  have split : Equiv (ofSignedRatio lower.toSignedRatio)
      (add (ofSignedRatio lower.half.toSignedRatio) (ofSignedRatio lower.half.toSignedRatio)) :=
    equiv_symm (equiv_trans (ofSignedRatio_add _ _) ((ofSignedRatio_equiv_iff _ _).mpr lower.half_add_half))
  exact (add_le_add_right_iff _ _ _).mp ((le_congr split (equiv_refl _)).mp compared)

end Thesis.Probability.ConstructiveReal
