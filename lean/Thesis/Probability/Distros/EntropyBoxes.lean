import Thesis.Probability.ProbabilityBoxes
import Thesis.Probability.Distros.EntropyContinuity
import Thesis.Probability.Distros.EntropyMomentConvex

namespace Thesis.Probability.Distros

private def boxInterval [DecidableEq A] (cell : A) {size : Nat} (index : Fin (size + 1)) (positive : 0 < size) : MomentInterval A :=
  ⟨(fun value => if value = cell then 1 else 0),
    (ProbabilityBoxes.lower index positive).toSignedRatio, (ProbabilityBoxes.upper index positive).toSignedRatio⟩

private theorem boxInterval_mean [DecidableEq A] (μ : Distro A) (cell : A) {size : Nat}
    (index : Fin (size + 1)) (positive : 0 < size) :
    SignedRatio.Equiv ((boxInterval cell index positive).mean μ) (μ.pmf cell).toSignedRatio := by
  refine SignedRatio.equiv_trans (μ.rationalExpectation_congr _
    (fun value => if FiniteProbRecord.singletonEvent cell value then SignedRatio.one else SignedRatio.zero) ?_)
    (μ.rationalExpectation_indicator (FiniteProbRecord.singletonEvent cell))
  intro value
  by_cases same : value = cell <;>
    simp only [boxInterval, FiniteProbRecord.singletonEvent, same, decide_true, decide_false, if_true,
      Bool.false_eq_true, if_false, SignedRatio.one, SignedRatio.zero] <;> exact SignedRatio.equiv_refl _

private theorem boxInterval_holds [DecidableEq A] (μ : Distro A) (cell : A) {size : Nat}
    (index : Fin (size + 1)) (positive : 0 < size) :
    (boxInterval cell index positive).LawHolds μ ↔
      QProb.LE (ProbabilityBoxes.lower index positive) (μ.pmf cell) ∧
        QProb.LE (μ.pmf cell) (ProbabilityBoxes.upper index positive) := by
  have mean := boxInterval_mean μ cell index positive
  constructor
  · intro valid
    exact ⟨(SignedRatio.toSignedRatio_le_iff _ _).mp
        ((SignedRatio.le_congr (SignedRatio.equiv_refl _) mean).mp valid.1),
      (SignedRatio.toSignedRatio_le_iff _ _).mp
        ((SignedRatio.le_congr mean (SignedRatio.equiv_refl _)).mp valid.2)⟩
  · intro valid
    exact ⟨(SignedRatio.le_congr (SignedRatio.equiv_refl _) mean).mpr
        ((SignedRatio.toSignedRatio_le_iff _ _).mpr valid.1),
      (SignedRatio.le_congr mean (SignedRatio.equiv_refl _)).mpr
        ((SignedRatio.toSignedRatio_le_iff _ _).mpr valid.2)⟩

namespace PartialMomentProblem

/-- Add rational coordinate intervals to the existing problem. The original
grid, exact moments, interval rows, forced zeros and redundant rows remain. -/
def withBox [DecidableEq A] (problem : PartialMomentProblem A) (size : Nat) (positive : 0 < size)
    (indices : Fin problem.cells.length → Fin (size + 1)) : PartialMomentProblem A :=
  { problem with intervals := problem.intervals ++ (List.finRange problem.cells.length).map (fun i =>
      boxInterval (problem.cells.getD i.val problem.default) (indices i) positive) }

theorem admissible_withBox_iff [DecidableEq A] (problem : PartialMomentProblem A) (size : Nat) (positive : 0 < size)
    (indices : Fin problem.cells.length → Fin (size + 1)) (μ : Distro A) :
    (problem.withBox size positive indices).Admissible μ ↔ problem.Admissible μ ∧
      ∀ i, QProb.LE (ProbabilityBoxes.lower (indices i) positive) (μ.pmf (problem.cells.getD i.val problem.default)) ∧
        QProb.LE (μ.pmf (problem.cells.getD i.val problem.default)) (ProbabilityBoxes.upper (indices i) positive) := by
  constructor
  · intro valid
    refine ⟨⟨valid.1, fun constraint member => valid.2 constraint (List.mem_append_left _ member)⟩, ?_⟩
    intro i
    exact (boxInterval_holds μ _ _ positive).mp
      (valid.2 _ (List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)))
  · rintro ⟨valid, boxes⟩
    refine ⟨valid.1, ?_⟩
    intro constraint member
    rcases List.mem_append.mp member with old | new
    · exact valid.2 constraint old
    · rcases List.mem_map.mp new with ⟨i, _, rfl⟩
      exact (boxInterval_holds μ _ _ positive).mpr (boxes i)

/-- Every exactly feasible rational law lies in an explicitly enumerated
box. Its probability denominator is arbitrary. -/
theorem boxes_cover [DecidableEq A] (problem : PartialMomentProblem A) (size : Nat) (positive : 0 < size)
    (μ : Distro A) (valid : problem.Admissible μ) :
    ∃ indices ∈ ProbabilityBoxes.enumerate problem.cells.length size,
      (problem.withBox size positive indices).Admissible μ := by
  have bounded (i : Fin problem.cells.length) : (μ.pmf (problem.cells.getD i.val problem.default)).num ≤
      (μ.pmf (problem.cells.getD i.val problem.default)).den := by
    have mass := (μ.probVal_bounds (FiniteProbRecord.singletonEvent (problem.cells.getD i.val problem.default))).2
    simpa only [QProb.LE, QProb.one, Nat.one_mul, Nat.mul_one] using mass
  let indices := fun i => ProbabilityBoxes.locate (μ.pmf (problem.cells.getD i.val problem.default)) (bounded i) size
  refine ⟨indices, ProbabilityBoxes.enumerate_complete _ _ indices, (problem.admissible_withBox_iff size positive indices μ).mpr ⟨valid, ?_⟩⟩
  intro i
  exact ProbabilityBoxes.locate_bounds _ (bounded i) size positive

/-- Any two exactly feasible laws selected from the same box are close on
all original declared cells, even if their atom lists and denominators differ. -/
theorem same_box_close [DecidableEq A] (problem : PartialMomentProblem A) (size : Nat) (positive : 0 < size)
    (indices : Fin problem.cells.length → Fin (size + 1)) (μ ν : Distro A)
    (first : (problem.withBox size positive indices).Admissible μ)
    (second : (problem.withBox size positive indices).Admissible ν) :
    ∀ value ∈ problem.cells,
      QProb.LE (μ.pmf value) (QProb.add (ν.pmf value) (ProbabilityBoxes.width size positive)) ∧
      QProb.LE (ν.pmf value) (QProb.add (μ.pmf value) (ProbabilityBoxes.width size positive)) := by
  have firstBounds := (problem.admissible_withBox_iff size positive indices μ).mp first
  have secondBounds := (problem.admissible_withBox_iff size positive indices ν).mp second
  intro value member
  obtain ⟨i, within, same⟩ := List.getElem_of_mem member
  have label : problem.cells.getD i problem.default = value := by
    rw [← List.getElem_eq_getD (h := within) problem.default, same]
  have close := ProbabilityBoxes.same_box_close (indices ⟨i, within⟩) positive _ _
    (firstBounds.2 ⟨i, within⟩) (secondBounds.2 ⟨i, within⟩)
  rw [label] at close
  exact close

/-- Forget only the added interval rows, retaining the actual feasible law
and every declared cell of its record. -/
def forgetBox [DecidableEq A] (problem : PartialMomentProblem A) (size : Nat) (positive : 0 < size)
    (indices : Fin problem.cells.length → Fin (size + 1))
    (law : (problem.withBox size positive indices).CompatibleLaw) : problem.CompatibleLaw :=
  ⟨law.distro, law.support, (fun constraint member => law.moments constraint (List.mem_append_left _ member)), law.retains⟩

end PartialMomentProblem
end Thesis.Probability.Distros
