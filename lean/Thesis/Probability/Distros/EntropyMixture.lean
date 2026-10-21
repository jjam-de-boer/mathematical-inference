import Thesis.Probability.Distros.EntropySupport
import Thesis.Probability.ExactLogConvex
import Thesis.Probability.RationalMixture

namespace Thesis.Probability.Distros

/-- A rational convex combination, retaining both original atom lists. -/
def Distro.mixture (μ ν : Distro A) (left right : Nat) (positive : 0 < left + right) : Distro A :=
  ⟨μ.record.mixture ν.record left right positive⟩

theorem Distro.mixture_support (μ ν : Distro A) (left right : Nat) (positive : 0 < left + right)
    (predicate : A → Prop) (first : μ.AlmostSurely predicate) (second : ν.AlmostSurely predicate) :
    (μ.mixture ν left right positive).AlmostSurely predicate := by
  intro atom member weight
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_map.mp member with ⟨original, listed, rfl⟩
    exact first original listed (Nat.pos_of_mul_pos_left weight)
  · rcases List.mem_map.mp member with ⟨original, listed, rfl⟩
    exact second original listed (Nat.pos_of_mul_pos_left weight)

theorem Distro.mixture_pmf [DecidableEq A] (μ ν : Distro A) (left right : Nat)
    (positive : 0 < left + right) (value : A) :
    QProb.Equiv ((μ.mixture ν left right positive).pmf value)
      (QProb.add (QProb.mul ⟨left, left + right, positive⟩ (μ.pmf value))
        (QProb.mul ⟨right, left + right, positive⟩ (ν.pmf value))) :=
  QProb.equiv_trans (μ.record.mixture_probVal ν.record left right positive _)
    (QProb.weightedPair_eq_sum left right positive _ _)

theorem Distro.mixture_pmf_num [DecidableEq A] (μ ν : Distro A) (left right : Nat)
    (positive : 0 < left + right) (value : A) :
    ((μ.mixture ν left right positive).pmf value).num =
      (left * ν.record.den) * (μ.pmf value).num + (right * μ.record.den) * (ν.pmf value).num :=
  μ.record.mixture_eventMass ν.record left right positive _

/-- Cross entropy is affine in the observed law, including zero masses. -/
theorem Distro.crossEntropy_mixture [DecidableEq A] (μ ν reference : Distro A) (grid : EntropyGrid A)
    (first : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (second : ν.AlmostSurely (fun value => value ∈ grid.cells))
    (referenceSupport : reference.AlmostSurely (fun value => value ∈ grid.cells))
    (referencePositive : reference.GridPositive grid)
    (left right : Nat) (positive : 0 < left + right) :
    ExactLog.Equiv ((μ.mixture ν left right positive).crossEntropy reference grid
      (μ.mixture_support ν left right positive _ first second) referenceSupport referencePositive)
      (ExactLog.add
        (ExactLog.scaleRatio ⟨left, left + right, positive⟩ (μ.crossEntropy reference grid first referenceSupport referencePositive))
        (ExactLog.scaleRatio ⟨right, left + right, positive⟩ (ν.crossEntropy reference grid second referenceSupport referencePositive))) := by
  let t : QProb := ⟨left, left + right, positive⟩
  let u : QProb := ⟨right, left + right, positive⟩
  let f := fun cell : {value // value ∈ grid.cells} => crossEntropyTerm (μ.pmf cell.val)
    (reference.pmf cell.val) (referencePositive cell.val cell.property)
  let g := fun cell : {value // value ∈ grid.cells} => crossEntropyTerm (ν.pmf cell.val)
    (reference.pmf cell.val) (referencePositive cell.val cell.property)
  have terms : ExactLog.Equiv
      ((μ.mixture ν left right positive).crossEntropy reference grid
        (μ.mixture_support ν left right positive _ first second) referenceSupport referencePositive)
      (ExactLog.listSum (grid.cells.attach.map (fun cell => ExactLog.add (ExactLog.scaleRatio t (f cell)) (ExactLog.scaleRatio u (g cell))))) := by
    apply ExactLog.listSum_map_congr
    intro cell _
    refine ExactLog.equiv_trans (crossEntropyTerm_congr (μ.mixture_pmf ν left right positive cell.val)
      (QProb.equiv_refl _) (referencePositive cell.val cell.property) (referencePositive cell.val cell.property)) ?_
    exact ExactLog.equiv_trans (ExactLog.scaleRatio_add_weight _ _ _)
      (by rw [← ExactLog.scaleRatio_mul, ← ExactLog.scaleRatio_mul]; exact ExactLog.equiv_refl _)
  have split := ExactLog.listSum_map_add grid.cells.attach (fun cell => ExactLog.scaleRatio t (f cell))
    (fun cell => ExactLog.scaleRatio u (g cell))
  have distributed (h : {value // value ∈ grid.cells} → ExactLog) (q : QProb) :=
    ExactLog.listSum_scaleRatio (grid.cells.attach.map h) q
  exact ExactLog.equiv_trans terms (ExactLog.equiv_trans split
    (ExactLog.add_congr (by simpa only [List.map_map, Function.comp_def] using distributed f t)
      (by simpa only [List.map_map, Function.comp_def] using distributed g u)))

theorem Distro.mixture_positive_left [DecidableEq A] (μ ν : Distro A) (left right : Nat)
    (positive : 0 < left + right) (leftPositive : 0 < left) (value : A)
    (mass : 0 < (μ.pmf value).num) : 0 < ((μ.mixture ν left right positive).pmf value).num := by
  rw [μ.mixture_pmf_num ν left right positive value]
  exact Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.mul_pos leftPositive ν.record.den_pos) mass) (Nat.le_add_right _ _)

theorem Distro.mixture_positive_right [DecidableEq A] (μ ν : Distro A) (left right : Nat)
    (positive : 0 < left + right) (rightPositive : 0 < right) (value : A)
    (mass : 0 < (ν.pmf value).num) : 0 < ((μ.mixture ν left right positive).pmf value).num := by
  rw [μ.mixture_pmf_num ν left right positive value]
  exact Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.mul_pos rightPositive μ.record.den_pos) mass) (Nat.le_add_left _ _)

theorem Distro.mixture_sameLaw_of_sameLaw (μ ν : Distro A) (left right : Nat)
    (positive : 0 < left + right) (same : μ.SameLaw ν) : (μ.mixture ν left right positive).SameLaw μ := by
  intro event
  exact QProb.equiv_trans (μ.record.mixture_probVal ν.record left right positive event)
    (QProb.equiv_trans (QProb.weightedPair_congr left right positive (QProb.equiv_refl _) (QProb.equiv_symm (same event)))
      (QProb.weightedPair_constant left right positive _))

end Thesis.Probability.Distros
