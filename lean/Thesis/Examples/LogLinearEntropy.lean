import Thesis.Probability.Distros.LogLinearEntropy
import Thesis.Probability.ConstructiveRealLogLinearOptimality
import Thesis.Probability.ExactLogPositiveEnclosure

namespace Thesis.Examples.LogLinearEntropy
open Probability Probability.Distros

private def negativeRow : MomentInterval Nat :=
  MomentInterval.exact (fun value => if value = 2 then -1 else 0) ⟨-1, 2, by decide⟩
private def problem : PartialMomentProblem Nat :=
  ⟨[0, 1, 2], 0, by decide, by decide, [negativeRow]⟩
private def candidate : Distro Nat := ⟨⟨[(0, 1), (1, 1), (2, 2), (99, 0)], 4, by decide, by decide⟩⟩
private theorem candidateSupport : candidate.AlmostSurely (fun value => value ∈ problem.cells) := by
  change ∀ atom ∈ candidate.record.atoms, 0 < atom.2 → atom.1 ∈ problem.cells
  decide +kernel
private theorem candidatePositive : candidate.GridPositive problem.entropyGrid := by
  change ∀ value ∈ problem.cells, 0 < (candidate.pmf value).num
  decide +kernel
private theorem candidateValid : problem.Admissible candidate := by
  refine ⟨candidateSupport, ?_⟩
  intro constraint member
  have same : constraint = negativeRow := List.mem_singleton.mp member
  subst constraint
  exact ⟨by decide +kernel, by decide +kernel⟩

private def reference : problem.LogLinearReference where
  reference := candidate
  support := candidateSupport
  positive := candidatePositive
  constraints := [negativeRow]
  listed := fun _ member => member
  exact := fun _ member => by
    have same := List.mem_singleton.mp member
    subst_vars
    exact SignedRatio.equiv_refl _
  coefficient := fun _ => ExactLog.ofQProb QProb.one
  offset := ExactLog.ofQProb QProb.one
  score := by
    intro value member
    change value ∈ [0, 1, 2] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide +kernel +revert

/-- The offset includes the minimum of the signed response, while null
outlier labels impose no new response/shift hypotheses. -/
example : problem.entropyGrid.responseShift negativeRow.response = 1 := by decide +kernel
example : problem.entropyGrid.shiftedResponse negativeRow.response 2 = 0 := by decide +kernel

/-- This is a global certificate over all exactly feasible rational laws,
with equality exactly at the same probability law as the candidate. -/
example (μ : Distro Nat) (valid : problem.Admissible μ) :
    ExactLog.LE (μ.entropy problem.entropyGrid valid.1) (candidate.entropy problem.entropyGrid candidateSupport) ∧
    (ExactLog.Equiv (μ.entropy problem.entropyGrid valid.1) (candidate.entropy problem.entropyGrid candidateSupport) ↔ μ.SameLaw candidate) :=
  reference.optimal candidateValid μ valid

private def retainedCandidate : problem.CompatibleLaw :=
  ⟨candidate, candidateSupport, candidateValid.2, by
    intro cell member
    change cell ∈ [0, 1, 2] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨1, by decide +kernel⟩
    · exact ⟨1, by decide +kernel⟩
    · exact ⟨2, by decide +kernel⟩⟩

/-- The same signed-moment reference now certifies all ideal competitors;
its explicit zero-weight outlier is still a presentation choice. -/
example (law : problem.RealCompatibleLaw) : ConstructiveReal.LE law.entropy
    (candidate.entropy problem.entropyGrid candidateSupport).interpret := reference.real_optimal candidateValid law

example : retainedCandidate.toReal.Maximal := reference.real_maximal candidateValid retainedCandidate rfl

example (law : problem.RealCompatibleLaw) (maximal : law.Maximal) (index : Fin problem.cells.length) :
    ConstructiveReal.Equiv (law.mass index).value (retainedCandidate.toReal.mass index).value :=
  reference.real_maximal_unique candidateValid retainedCandidate rfl law maximal index

end Thesis.Examples.LogLinearEntropy
