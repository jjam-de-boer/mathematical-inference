import Thesis.Probability.Distros.EntropyGibbsEquality
import Thesis.Probability.CrossEntropyValue

namespace Thesis.Probability.Distros

/-- Cross entropy in bits on the same explicit finite grid as entropy and KL. -/
def Distro.crossEntropy [DecidableEq A] (μ reference : Distro A) (grid : EntropyGrid A)
    (_support : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (_referenceSupport : reference.AlmostSurely (fun value => value ∈ grid.cells))
    (positive : reference.GridPositive grid) : ExactLog :=
  ExactLog.listSum (grid.cells.attach.map (fun cell =>
    crossEntropyTerm (μ.pmf cell.val) (reference.pmf cell.val) (positive cell.val cell.property)))

theorem Distro.relativeEntropy_cross_sub [DecidableEq A] (μ reference : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (referenceSupport : reference.AlmostSurely (fun value => value ∈ grid.cells))
    (positive : reference.GridPositive grid) :
    ExactLog.Equiv (μ.relativeEntropy reference grid support referenceSupport positive)
      (ExactLog.sub (μ.crossEntropy reference grid support referenceSupport positive) (μ.entropy grid support)) := by
  refine ExactLog.equiv_trans (ExactLog.listSum_map_congr grid.cells.attach _
    (fun cell => ExactLog.sub (crossEntropyTerm (μ.pmf cell.val) (reference.pmf cell.val) (positive cell.val cell.property))
      (entropyTerm (μ.pmf cell.val))) (fun cell _ => relativeEntropyTerm_cross_sub _ _ _)) ?_
  have distributed := ExactLog.listSum_map_sub grid.cells.attach
    (fun cell => crossEntropyTerm (μ.pmf cell.val) (reference.pmf cell.val) (positive cell.val cell.property))
    (fun cell => entropyTerm (μ.pmf cell.val))
  rw [List.attach_map_val (f := fun value => entropyTerm (μ.pmf value))] at distributed
  exact distributed

/-- The global Gibbs variational bound. A reference score supplies an upper
bound on entropy, with no stationarity or local-extremum premise. -/
theorem Distro.entropy_le_crossEntropy [DecidableEq A] (μ reference : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (referenceSupport : reference.AlmostSurely (fun value => value ∈ grid.cells))
    (positive : reference.GridPositive grid) :
    ExactLog.LE (μ.entropy grid support) (μ.crossEntropy reference grid support referenceSupport positive) := by
  have nonnegative := μ.relativeEntropy_nonnegative reference grid support referenceSupport positive
  have difference := (ExactLog.le_congr (ExactLog.equiv_refl _)
    (μ.relativeEntropy_cross_sub reference grid support referenceSupport positive)).mp nonnegative
  exact (ExactLog.zero_le_sub_iff _ _).mp difference

theorem Distro.crossEntropy_self [DecidableEq A] (μ : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells)) (positive : μ.GridPositive grid) :
    ExactLog.Equiv (μ.crossEntropy μ grid support support positive) (μ.entropy grid support) := by
  have vanished := ExactLog.equiv_trans
    (ExactLog.equiv_symm (μ.relativeEntropy_cross_sub μ grid support support positive))
    (μ.relativeEntropy_self grid support positive)
  exact (ExactLog.sub_equiv_zero_iff _ _).mp vanished

/-- A constant positive reference score integrates to that same exact log,
since the aggregated observed probabilities sum to one. -/
theorem Distro.crossEntropy_constant [DecidableEq A] (μ reference : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (referenceSupport : reference.AlmostSurely (fun value => value ∈ grid.cells))
    (positive : reference.GridPositive grid) (mass : QProb) (massPositive : 0 < mass.num)
    (constant : ∀ value ∈ grid.cells, QProb.Equiv (reference.pmf value) mass) :
    ExactLog.Equiv (μ.crossEntropy reference grid support referenceSupport positive)
      (ExactLog.log (PositiveRatio.inv ⟨mass.num, mass.den, massPositive, mass.den_pos⟩)) := by
  let score := ExactLog.log (PositiveRatio.inv ⟨mass.num, mass.den, massPositive, mass.den_pos⟩)
  have terms := ExactLog.listSum_map_congr grid.cells.attach
    (fun cell => crossEntropyTerm (μ.pmf cell.val) (reference.pmf cell.val) (positive cell.val cell.property))
    (fun cell => ExactLog.scaleRatio (μ.pmf cell.val) score)
    (fun cell _ => crossEntropyTerm_congr (QProb.equiv_refl _) (constant cell.val cell.property) _ _)
  rw [List.attach_map_val (f := fun value => ExactLog.scaleRatio (μ.pmf value) score)] at terms
  have distributed := ExactLog.listSum_scaleRatio_weights (grid.cells.map μ.pmf) score
  rw [List.map_map] at distributed
  have normalized := ExactLog.scaleRatio_weight_congr (μ.pmf_grid_normalization grid support) score
  rw [ExactLog.scaleRatio_one] at normalized
  exact ExactLog.equiv_trans terms (ExactLog.equiv_trans distributed normalized)

/-- Global optimality criterion: a feasible positive candidate maximizes
entropy among all laws with its cross entropy. No existence claim is made for
an exact rational optimizer of every constraint problem. -/
theorem Distro.entropy_le_of_crossEntropy_eq [DecidableEq A] (μ candidate : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (candidateSupport : candidate.AlmostSurely (fun value => value ∈ grid.cells))
    (positive : candidate.GridPositive grid)
    (fixed : ExactLog.Equiv (μ.crossEntropy candidate grid support candidateSupport positive)
      (candidate.crossEntropy candidate grid candidateSupport candidateSupport positive)) :
    ExactLog.LE (μ.entropy grid support) (candidate.entropy grid candidateSupport) := by
  have bound := μ.entropy_le_crossEntropy candidate grid support candidateSupport positive
  exact (ExactLog.le_congr (ExactLog.equiv_refl _)
    (ExactLog.equiv_trans fixed (candidate.crossEntropy_self grid candidateSupport positive))).mp bound

/-- The same global criterion has equality precisely at the candidate law. -/
theorem Distro.entropy_eq_of_crossEntropy_eq_iff [DecidableEq A] (μ candidate : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (candidateSupport : candidate.AlmostSurely (fun value => value ∈ grid.cells))
    (positive : candidate.GridPositive grid)
    (fixed : ExactLog.Equiv (μ.crossEntropy candidate grid support candidateSupport positive)
      (candidate.crossEntropy candidate grid candidateSupport candidateSupport positive)) :
    ExactLog.Equiv (μ.entropy grid support) (candidate.entropy grid candidateSupport) ↔ μ.SameLaw candidate := by
  constructor
  · intro entropyEqual
    have crossEqual := ExactLog.equiv_trans fixed (candidate.crossEntropy_self grid candidateSupport positive)
    have differenceZero := (ExactLog.sub_equiv_zero_iff _ _).mpr
      (ExactLog.equiv_trans crossEqual (ExactLog.equiv_symm entropyEqual))
    exact μ.sameLaw_of_relativeEntropy_zero candidate grid support candidateSupport positive
      (ExactLog.equiv_trans (μ.relativeEntropy_cross_sub candidate grid support candidateSupport positive) differenceZero)
  · intro same
    exact Distro.entropy_sameLaw same grid support candidateSupport

end Thesis.Probability.Distros
