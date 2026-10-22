import Thesis.Probability.Distros.UncertaintyRefinement

namespace Thesis.Probability.UncertaintyMeasure
open ProbabilityVector

private theorem null_count (measure : UncertaintyMeasure) (counts : List Nat) (den : Nat)
    (positive : 0 < den) (mass : counts.sum = den) :
    ExactLog.Equiv (measure.value (ofCounts (0 :: counts) den positive (by simpa only [List.sum_cons, Nat.zero_add] using mass)))
      (measure.value (ofCounts counts den positive mass)) := by
  have same : SameMasses
      (ofCounts (0 :: counts) den positive (by simpa only [List.sum_cons, Nat.zero_add] using mass)).masses
      (ofCounts counts den positive mass).addNull.masses := by
    refine ⟨?_, sameMasses_refl _⟩
    simp only [QProb.Equiv, QProb.zero, Nat.zero_mul]
  exact ExactLog.equiv_trans (measure.representation _ _ same) (measure.null _)

/-- A finite zero-removal proof avoids the standard library's generic
existential decomposition of erasure, which imports classical choice. -/
private theorem perm_zero_erase (counts : List Nat) (member : 0 ∈ counts) :
    counts.Perm (0 :: counts.erase 0) := by
  induction counts with
  | nil => cases member
  | cons count tail ih =>
      cases count with
      | zero => exact List.Perm.refl _
      | succ count =>
          have inTail : 0 ∈ tail := by
            cases member with
            | tail _ listed => exact listed
          exact (List.Perm.cons _ (ih inTail)).trans (List.Perm.swap _ _ _)

private theorem erase_zero (measure : UncertaintyMeasure) (counts : List Nat) (den : Nat)
    (positive : 0 < den) (mass : counts.sum = den) (member : 0 ∈ counts)
    (remaining : (counts.erase 0).sum = den) :
    ExactLog.Equiv (measure.value (ofCounts counts den positive mass))
      (measure.value (ofCounts (counts.erase 0) den positive remaining)) := by
  have moved := measure.permutation (ofCounts counts den positive mass)
    (ofCounts (0 :: counts.erase 0) den positive (by simpa only [List.sum_cons, Nat.zero_add] using remaining))
    ((perm_zero_erase counts member).map (fun count => (⟨count, den, positive⟩ : QProb)))
  exact ExactLog.equiv_trans moved (null_count measure (counts.erase 0) den positive remaining)

private theorem erase_shorter (counts : List Nat) (member : 0 ∈ counts) :
    (counts.erase 0).length < counts.length := by
  induction counts with
  | nil => cases member
  | cons count tail ih =>
      cases count with
      | zero => exact Nat.lt_succ_self _
      | succ count =>
          have inTail : 0 ∈ tail := by
            cases member with
            | tail _ listed => exact listed
          exact Nat.succ_lt_succ (ih inTail)

/-- Null insertion and permutation extend refinement uniqueness to every
nonnegative count presentation. Zero cells are permitted anywhere in the
original vector; the theorem's input and conclusion retain that vector. -/
theorem counts_unique (first second : UncertaintyMeasure) (counts : List Nat)
    (den : Nat) (positive : 0 < den) (mass : counts.sum = den) :
    ExactLog.Equiv (first.value (ofCounts counts den positive mass)) (second.value (ofCounts counts den positive mass)) := by
  by_cases member : 0 ∈ counts
  · have remaining : (counts.erase 0).sum = den := by
      have summed := (perm_zero_erase counts member).sum_nat
      rw [mass, List.sum_cons, Nat.zero_add] at summed
      exact summed.symm
    exact ExactLog.equiv_trans (erase_zero first counts den positive mass member remaining)
      (ExactLog.equiv_trans (counts_unique first second (counts.erase 0) den positive remaining)
        (ExactLog.equiv_symm (erase_zero second counts den positive mass member remaining)))
  · exact positive_counts_unique first second counts den positive mass (fun count listed =>
      Nat.pos_of_ne_zero (fun zero => member (zero ▸ listed)))
termination_by counts.length
  decreasing_by exact erase_shorter counts member

/-- Uniqueness of rational uncertainty from the stated requirements. The
argument compares arbitrary admissible measures, without assuming either
one is already given by a logarithmic entropy formula. -/
theorem unique (first second : UncertaintyMeasure) (vector : ProbabilityVector) :
    ExactLog.Equiv (first.value vector) (second.value vector) := by
  let presentation := vector.countPresentation
  have firstSame := first.representation
    (ofCounts presentation.counts presentation.den presentation.den_pos presentation.mass) vector presentation.represents
  have secondSame := second.representation
    (ofCounts presentation.counts presentation.den presentation.den_pos presentation.mass) vector presentation.represents
  exact ExactLog.equiv_trans (ExactLog.equiv_symm firstSame)
    (ExactLog.equiv_trans (counts_unique first second presentation.counts presentation.den presentation.den_pos presentation.mass) secondSame)

/-- Shannon's formula is the unique uncertainty satisfying the explicit
rational grouping, ordering, representation and fair-bit requirements. -/
theorem characterization (measure : UncertaintyMeasure) (vector : ProbabilityVector) :
    ExactLog.Equiv (measure.value vector) vector.entropy := measure.unique UncertaintyMeasure.shannon vector

/-- The characterization agrees with the existing distribution entropy,
computed on aggregated observable cells and allowing null record outliers. -/
theorem distro_characterization [DecidableEq A] (measure : UncertaintyMeasure)
    (law : Distros.Distro A) (grid : Distros.EntropyGrid A)
    (support : law.AlmostSurely (fun value => value ∈ grid.cells)) :
    ExactLog.Equiv (measure.value (ofDistro law grid support)) (law.entropy grid support) := by
  have result := measure.characterization (ofDistro law grid support)
  rw [ofDistro_entropy] at result
  exact result

end Thesis.Probability.UncertaintyMeasure
