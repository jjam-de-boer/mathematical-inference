import Thesis.Probability.RationalAMGM
import Thesis.Probability.ExactLogRoots

namespace Thesis.Probability.RationalAMGM

/-- Weighted logarithms with a common normalization denominator. -/
def logMean (items : List (PositiveRatio × Nat)) (den : Nat) (positive : 0 < den) : ExactLog :=
  ExactLog.listSum (items.map (fun item => ExactLog.root (item.1.pow item.2) den positive))

theorem logMean_equiv_root (items : List (PositiveRatio × Nat)) (den : Nat) (positive : 0 < den) :
    ExactLog.Equiv (logMean items den positive) (ExactLog.root (weightedProduct items) den positive) := by
  induction items with
  | nil => exact ExactLog.equiv_symm (ExactLog.root_one_equiv_zero den positive)
  | cons item rest ih =>
      exact ExactLog.equiv_trans (ExactLog.add_congr (ExactLog.equiv_refl _) ih)
        (ExactLog.root_add_equiv _ _ den positive)

def inverses (items : List (PositiveRatio × Nat)) : List (PositiveRatio × Nat) :=
  items.map (fun item => (item.1.inv, item.2))

theorem weightedProduct_inverses (items : List (PositiveRatio × Nat)) :
    weightedProduct (inverses items) = (weightedProduct items).inv := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [inverses, List.map_cons, weightedProduct, PositiveRatio.inv_mul, PositiveRatio.inv_pow] at ih ⊢
      rw [ih]

theorem totalWeight_inverses (items : List (PositiveRatio × Nat)) : totalWeight (inverses items) = totalWeight items := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [inverses, List.map_cons, totalWeight] at ih ⊢; rw [ih]

/-- A finite Gibbs bound proved through rational AM–GM, without calculus. -/
theorem logMean_le_zero (items : List (PositiveRatio × Nat)) (den : Nat) (positive : 0 < den)
    (bounded : QProb.LE (weightedSum items) (QProb.ofNat (totalWeight items))) :
    ExactLog.LE (logMean items den positive) ExactLog.zero := by
  apply (ExactLog.le_congr (logMean_equiv_root items den positive) (ExactLog.equiv_refl _)).mpr
  exact (ExactLog.root_le_zero_iff _ _ _).mpr (weightedProduct_le_one items bounded)

/-- The inverse-mean form gives nonnegativity of a normalized log sum.
Zero multiplicities are included and impose no contribution. -/
theorem logMean_nonnegative (items : List (PositiveRatio × Nat)) (den : Nat) (positive : 0 < den)
    (bounded : QProb.LE (weightedSum (inverses items)) (QProb.ofNat (totalWeight items))) :
    ExactLog.LE ExactLog.zero (logMean items den positive) := by
  have inverseBound : PositiveRatio.LE (weightedProduct items).inv PositiveRatio.one := by
    have result := weightedProduct_le_one (inverses items) (by simpa only [totalWeight_inverses] using bounded)
    simpa only [weightedProduct_inverses] using result
  have productBound : PositiveRatio.LE PositiveRatio.one (weightedProduct items) :=
    (PositiveRatio.inv_le_inv_iff (weightedProduct items) PositiveRatio.one).mp inverseBound
  apply (ExactLog.le_congr (ExactLog.equiv_refl _) (logMean_equiv_root items den positive)).mpr
  exact (ExactLog.zero_le_root_iff _ _ _).mpr productBound

end Thesis.Probability.RationalAMGM
