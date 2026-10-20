import Thesis.Probability.Distros.Entropy
import Thesis.Probability.ExactLogEnclosure

namespace Thesis.Examples.Entropy
open Probability Probability.Distros

private def grid : EntropyGrid Nat := ⟨[0, 1], by decide⟩
private def reversed : EntropyGrid Nat := ⟨[1, 0], by decide⟩
private def extended : EntropyGrid Nat := ⟨[99, 0, 1], by decide⟩
private def fair : Distro Nat := ⟨⟨[(0, 1), (1, 1)], 2, by decide, by decide⟩⟩
private def split : Distro Nat := ⟨⟨[(1, 2), (0, 1), (99, 0), (0, 1)], 4, by decide, by decide⟩⟩
private def point : Distro Nat := ⟨⟨[(0, 1)], 1, by decide, by decide⟩⟩
private def prior : Distro Nat := ⟨⟨[(0, 1), (1, 3)], 4, by decide, by decide⟩⟩
private def oneBit : Probability.ExactLog := Probability.ExactLog.ofSignedRatio ⟨1, 1, by decide⟩

private theorem fairSupport : fair.AlmostSurely (fun x => x ∈ grid.cells) := by
  change ∀ atom ∈ fair.record.atoms, 0 < atom.2 → atom.1 ∈ grid.cells
  decide +kernel
private theorem splitSupport : split.AlmostSurely (fun x => x ∈ grid.cells) := by
  change ∀ atom ∈ split.record.atoms, 0 < atom.2 → atom.1 ∈ grid.cells
  decide +kernel
private theorem pointSupport : point.AlmostSurely (fun x => x ∈ grid.cells) := by
  change ∀ atom ∈ point.record.atoms, 0 < atom.2 → atom.1 ∈ grid.cells
  decide +kernel
private theorem priorSupport : prior.AlmostSurely (fun x => x ∈ grid.cells) := by
  change ∀ atom ∈ prior.record.atoms, 0 < atom.2 → atom.1 ∈ grid.cells
  decide +kernel
private theorem fairPositive : fair.GridPositive grid := by
  change ∀ x ∈ grid.cells, 0 < (fair.pmf x).num
  decide +kernel
private theorem priorPositive : prior.GridPositive grid := by
  change ∀ x ∈ grid.cells, 0 < (prior.pmf x).num
  decide +kernel

/-- Duplicate occurrences are aggregated. The null outlier stays outside the
grid; both denominator rescaling and record reordering preserve the law. -/
private theorem fair_split : fair.SameLaw split := by
  intro event
  cases first : event 0 <;> cases second : event 1 <;>
    simp [fair, split, FiniteProbRecord.probVal, FiniteProbRecord.eventMass, first, second, QProb.Equiv]

example : Probability.ExactLog.Equiv (fair.entropy grid fairSupport) oneBit := by decide +kernel
example : Probability.ExactLog.Equiv (split.entropy grid splitSupport) oneBit := by decide +kernel
example : Probability.ExactLog.Equiv (fair.entropy grid fairSupport) (split.entropy grid splitSupport) :=
  Distro.entropy_sameLaw fair_split grid fairSupport splitSupport
example : Probability.ExactLog.Equiv (point.entropy grid pointSupport) Probability.ExactLog.zero := by decide +kernel

private theorem reversedSupport : fair.AlmostSurely (fun x => x ∈ reversed.cells) := by
  change ∀ atom ∈ fair.record.atoms, 0 < atom.2 → atom.1 ∈ reversed.cells
  decide +kernel
example : Probability.ExactLog.Equiv (fair.entropy grid fairSupport) (fair.entropy reversed reversedSupport) :=
  fair.entropy_grid_perm grid reversed (List.Perm.swap ..) fairSupport reversedSupport

private theorem extendedSupport : fair.AlmostSurely (fun x => x ∈ extended.cells) := by
  change ∀ atom ∈ fair.record.atoms, 0 < atom.2 → atom.1 ∈ extended.cells
  decide +kernel
example : Probability.ExactLog.Equiv (fair.entropy extended extendedSupport) (fair.entropy grid fairSupport) :=
  fair.entropy_add_null_cell grid extended 99 rfl fairSupport extendedSupport (by decide +kernel)

example : Probability.ExactLog.Equiv
    (fair.relativeEntropy fair grid fairSupport fairSupport fairPositive) Probability.ExactLog.zero := by decide +kernel
example : Probability.ExactLog.Equiv
    (point.relativeEntropy fair grid pointSupport fairSupport fairPositive) oneBit := by decide +kernel
/-- Unequal positive reference weights give a nonintegral, exact symbolic KL. -/
example : Probability.ExactLog.Equiv
    (fair.relativeEntropy prior grid fairSupport priorSupport priorPositive)
    ⟨⟨4, 3, by decide, by decide⟩, 2, by decide⟩ := by decide +kernel

end Thesis.Examples.Entropy
