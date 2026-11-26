import Thesis.Probability.Distros.EntropyUniform
import Thesis.Probability.ExactLogRational

/-!
# Universal cardinality bounds and a nonuniform constrained comparison

Every law supported on the three-cell grid has entropy between zero and
`log2(3)`, with equality at the upper bound exactly for the uniform law.
The uniformity conclusion is equality of whole laws, not of raw records.

A separate positive candidate with masses `[1/4,1/4,1/2]` has entropy `3/2`.
The point-pair competitor retains a null outlier and has the same cross
entropy against that candidate. This supplied cross-entropy equality
licenses the nonuniform entropy bound; it is not a maximum over all laws
on the grid. A singleton mismatch excludes equality of the two entropies
through the theorem's law-equality criterion.
-/

namespace Thesis.Examples.EntropyBounds
open Probability Probability.Distros

private def grid : EntropyGrid Nat := ⟨[0, 1, 2], by decide⟩
private theorem nonempty : 0 < grid.cells.length := by decide

/-- Both finite entropy bounds hold for every supported rational law. -/
example (μ : Distro Nat) (support : μ.AlmostSurely (fun value => value ∈ grid.cells)) :
    ExactLog.LE ExactLog.zero (μ.entropy grid support) ∧
    ExactLog.LE (μ.entropy grid support) (ExactLog.log ⟨3, 1, by decide, by decide⟩) :=
  ⟨μ.entropy_nonnegative grid support, μ.entropy_le_log_card grid support nonempty⟩

example : ExactLog.Equiv ((grid.uniform nonempty).entropy grid (grid.uniform_support nonempty))
    (ExactLog.log ⟨3, 1, by decide, by decide⟩) := grid.uniform_entropy nonempty

example (μ : Distro Nat) (support : μ.AlmostSurely (fun value => value ∈ grid.cells)) :
    ExactLog.Equiv (μ.entropy grid support) (ExactLog.log ⟨3, 1, by decide, by decide⟩) ↔
      μ.SameLaw (grid.uniform nonempty) := μ.entropy_eq_log_card_iff grid support nonempty

private def candidate : Distro Nat := ⟨⟨[(0, 1), (1, 1), (2, 2)], 4, by decide, by decide⟩⟩
private def competitor : Distro Nat := ⟨⟨[(0, 1), (2, 1), (99, 0)], 2, by decide, by decide⟩⟩
private theorem candidateSupport : candidate.AlmostSurely (fun value => value ∈ grid.cells) := by
  change ∀ atom ∈ candidate.record.atoms, 0 < atom.2 → atom.1 ∈ grid.cells
  decide +kernel
private theorem competitorSupport : competitor.AlmostSurely (fun value => value ∈ grid.cells) := by
  change ∀ atom ∈ competitor.record.atoms, 0 < atom.2 → atom.1 ∈ grid.cells
  decide +kernel
private theorem candidatePositive : candidate.GridPositive grid := by
  change ∀ value ∈ grid.cells, 0 < (candidate.pmf value).num
  decide +kernel
private theorem fixedCrossEntropy :
    ExactLog.Equiv (competitor.crossEntropy candidate grid competitorSupport candidateSupport candidatePositive)
      (candidate.crossEntropy candidate grid candidateSupport candidateSupport candidatePositive) := by
  decide +kernel

/-- A nonuniform candidate also gives a global entropy certificate. The
competitor retains a zero-weight outlier outside the declared grid. -/
example : ExactLog.LE (competitor.entropy grid competitorSupport) (candidate.entropy grid candidateSupport) :=
  competitor.entropy_le_of_crossEntropy_eq candidate grid competitorSupport candidateSupport candidatePositive fixedCrossEntropy

example : ExactLog.Equiv (candidate.entropy grid candidateSupport)
    (ExactLog.ofSignedRatio ⟨3, 2, by decide⟩) := by decide +kernel

example : ¬ ExactLog.Equiv (competitor.entropy grid competitorSupport) (candidate.entropy grid candidateSupport) := by
  intro equal
  have laws := (competitor.entropy_eq_of_crossEntropy_eq_iff candidate grid competitorSupport
    candidateSupport candidatePositive fixedCrossEntropy).mp equal
  have mismatch : ¬ QProb.Equiv (competitor.pmf 1) (candidate.pmf 1) := by decide +kernel
  exact mismatch (laws (FiniteProbRecord.singletonEvent 1))

end Thesis.Examples.EntropyBounds
