import Thesis.Probability.RationalAMGM
import Thesis.Probability.RationalNorm

namespace Thesis.Probability.RationalAMGM

/-- Multiply the values of a finite weighted family, retaining every weight
and occurrence, including zero multiplicities. -/
def multiplyValues (items : List (PositiveRatio × Nat)) (factor : PositiveRatio) : List (PositiveRatio × Nat) :=
  items.map (fun item => (item.1.mul factor, item.2))

theorem totalWeight_multiplyValues (items : List (PositiveRatio × Nat)) (factor : PositiveRatio) :
    totalWeight (multiplyValues items factor) = totalWeight items := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [multiplyValues, List.map_cons, totalWeight] at ih ⊢; rw [ih]

private theorem scale_mul (weight : Nat) (value factor : QProb) :
    QProb.Equiv (QProb.scale weight (QProb.mul value factor)) (QProb.mul (QProb.scale weight value) factor) := by
  simp only [QProb.Equiv, QProb.scale, QProb.mul]
  ac_rfl

theorem weightedSum_multiplyValues (items : List (PositiveRatio × Nat)) (factor : PositiveRatio) :
    QProb.Equiv (weightedSum (multiplyValues items factor)) (QProb.mul (weightedSum items) factor.toQProb) := by
  induction items with
  | nil => simp only [multiplyValues, List.map_nil, weightedSum, QProb.Equiv, QProb.mul, QProb.zero, Nat.zero_mul]
  | cons item rest ih =>
      exact QProb.equiv_trans (QProb.add_congr (scale_mul item.2 item.1.toQProb factor.toQProb) ih)
        (QProb.equiv_symm (QProb.add_mul_distrib _ _ _))

theorem weightedProduct_multiplyValues (items : List (PositiveRatio × Nat)) (factor : PositiveRatio) :
    weightedProduct (multiplyValues items factor) = (weightedProduct items).mul (factor.pow (totalWeight items)) := by
  induction items with
  | nil => simp only [multiplyValues, List.map_nil, weightedProduct, totalWeight, PositiveRatio.pow_zero, PositiveRatio.mul_one]
  | cons item rest ih =>
      simp only [multiplyValues, List.map_cons, weightedProduct, totalWeight] at ih ⊢
      rw [ih, PositiveRatio.mul_pow, PositiveRatio.pow_add]
      apply PositiveRatio.ext <;> simp only [PositiveRatio.mul] <;> ac_rfl

/-- Rational weighted AM–GM relative to any supplied positive arithmetic
upper mean. No positivity of total multiplicity is needed for this power form. -/
theorem weightedProduct_le_mean (items : List (PositiveRatio × Nat)) (mean : PositiveRatio)
    (bounded : QProb.LE (weightedSum items) (QProb.scale (totalWeight items) mean.toQProb)) :
    PositiveRatio.LE (weightedProduct items) (mean.pow (totalWeight items)) := by
  let normalized := multiplyValues items mean.inv
  have canceled : QProb.Equiv (QProb.mul (QProb.scale (totalWeight items) mean.toQProb) mean.inv.toQProb)
      (QProb.ofNat (totalWeight items)) := by
    simp only [QProb.Equiv, QProb.mul, QProb.scale, QProb.ofNat, PositiveRatio.toQProb, PositiveRatio.inv, Nat.mul_one]
    ac_rfl
  have arithmetic : QProb.LE (weightedSum normalized) (QProb.ofNat (totalWeight normalized)) := by
    rw [totalWeight_multiplyValues]
    exact QProb.le_congr (QProb.equiv_symm (weightedSum_multiplyValues items mean.inv)) canceled
      (QProb.mul_le_mul bounded (QProb.le_refl _))
  have compared := weightedProduct_le_one normalized arithmetic
  rw [weightedProduct_multiplyValues, ← PositiveRatio.inv_pow] at compared
  let power := mean.pow (totalWeight items)
  have multiplied := PositiveRatio.mul_le_mul compared (PositiveRatio.le_refl power)
  have cancellation : PositiveRatio.Equiv ((weightedProduct items).mul power.inv |>.mul power) (weightedProduct items) := by
    rw [PositiveRatio.mul_assoc, PositiveRatio.mul_comm power.inv power]
    exact PositiveRatio.equiv_trans (PositiveRatio.mul_congr (PositiveRatio.equiv_refl _) (PositiveRatio.mul_inv power))
      (by rw [PositiveRatio.mul_one]; exact PositiveRatio.equiv_refl _)
  rw [PositiveRatio.one_mul] at multiplied
  exact (PositiveRatio.le_congr cancellation (PositiveRatio.equiv_refl _)).mp multiplied

end Thesis.Probability.RationalAMGM
