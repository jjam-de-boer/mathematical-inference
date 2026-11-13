import Thesis.Probability.LogMeanInequality
import Thesis.Probability.RationalAMGMEquality

namespace Thesis.Probability.RationalAMGM

/-- Equality in the inverse-mean Gibbs bound determines every positively
weighted ratio. This does not constrain any recorded zero-weight argument. -/
theorem eq_one_of_logMean_zero (items : List (PositiveRatio × Nat)) (den : Nat) (positive : 0 < den)
    (weightPositive : 0 < totalWeight items)
    (bounded : QProb.LE (weightedSum (inverses items)) (QProb.ofNat (totalWeight items)))
    (vanished : ExactLog.Equiv (logMean items den positive) ExactLog.zero) :
    ∀ item ∈ items, 0 < item.2 → PositiveRatio.Equiv item.1 PositiveRatio.one := by
  have rootZero := ExactLog.equiv_trans (ExactLog.equiv_symm (logMean_equiv_root items den positive)) vanished
  have productZero := (ExactLog.root_equiv_zero_iff _ _ _).mp rootZero
  have inverseProduct : PositiveRatio.Equiv (weightedProduct (inverses items)) PositiveRatio.one := by
    rw [weightedProduct_inverses]
    exact PositiveRatio.inv_congr productZero
  have each := eq_one_of_weightedProduct_equiv_one (inverses items)
    (by simpa only [totalWeight_inverses] using weightPositive)
    (by simpa only [totalWeight_inverses] using bounded) inverseProduct
  intro item member weight
  have inverseEqual := each (item.1.inv, item.2) (List.mem_map.mpr ⟨item, member, rfl⟩) weight
  simpa only [PositiveRatio.inv_inv] using PositiveRatio.inv_congr inverseEqual

end Thesis.Probability.RationalAMGM
