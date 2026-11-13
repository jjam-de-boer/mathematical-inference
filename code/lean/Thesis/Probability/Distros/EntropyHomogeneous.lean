import Thesis.Probability.Distros.EntropyGibbs

namespace Thesis.Probability

/-- Reciprocal positive mass with harmless value one at zero multiplicity. -/
def entropyRatio (p : QProb) : PositiveRatio :=
  if positive : 0 < p.num then ⟨p.den, p.num, p.den_pos, positive⟩ else PositiveRatio.one

theorem entropyTerm_root (p : QProb) : ExactLog.Equiv (entropyTerm p)
    (ExactLog.root ((entropyRatio p).pow p.num) p.den p.den_pos) := by
  by_cases positive : 0 < p.num
  · simp only [entropyTerm, entropyRatio, positive, ↓reduceDIte,
      ExactLog.scaleRatio, ExactLog.log, ExactLog.root, Nat.one_mul, PositiveRatio.inv]
    exact ExactLog.equiv_refl _
  · have zero : p.num = 0 := Nat.eq_zero_of_not_pos positive
    rw [entropyTerm_zero_num p zero]
    unfold entropyRatio
    rw [dif_neg positive, zero, PositiveRatio.pow_zero]
    exact ExactLog.equiv_symm (ExactLog.root_one_equiv_zero p.den p.den_pos)

namespace Distros

def Distro.entropyRatioItems [DecidableEq A] (μ : Distro A) (grid : EntropyGrid A) : List (PositiveRatio × Nat) :=
  grid.cells.map (fun value => (entropyRatio (μ.pmf value), (μ.pmf value).num))

/-- An equivalent common-degree entropy representation. This is useful for
executed certificates: summing unreduced roots does not inflate their degrees. -/
theorem Distro.entropy_homogeneous [DecidableEq A] (μ : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells)) :
    ExactLog.Equiv (μ.entropy grid support)
      (ExactLog.root (RationalAMGM.weightedProduct (μ.entropyRatioItems grid)) μ.record.den μ.record.den_pos) := by
  have terms : ExactLog.Equiv (μ.entropy grid support)
      (RationalAMGM.logMean (μ.entropyRatioItems grid) μ.record.den μ.record.den_pos) := by
    unfold Distro.entropy entropyRatioItems RationalAMGM.logMean
    rw [List.map_map]
    apply ExactLog.listSum_map_congr
    intro value _
    exact entropyTerm_root (μ.pmf value)
  exact ExactLog.equiv_trans terms (RationalAMGM.logMean_equiv_root _ _ _)

end Distros
end Thesis.Probability
