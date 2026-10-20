import Thesis.Probability.Distros.EntropyGibbs

namespace Thesis.Examples.EntropyGibbs
open Probability Probability.Distros

private def grid : EntropyGrid Nat := ⟨[0, 1, 2], by decide⟩
private def observed : Distro Nat := ⟨⟨[(0, 1), (99, 0)], 1, by decide, by decide⟩⟩
private def prior : Distro Nat := ⟨⟨[(2, 1), (0, 1), (1, 1)], 3, by decide, by decide⟩⟩
private theorem observedSupport : observed.AlmostSurely (fun value => value ∈ grid.cells) := by
  change ∀ atom ∈ observed.record.atoms, 0 < atom.2 → atom.1 ∈ grid.cells
  decide +kernel
private theorem priorSupport : prior.AlmostSurely (fun value => value ∈ grid.cells) := by
  change ∀ atom ∈ prior.record.atoms, 0 < atom.2 → atom.1 ∈ grid.cells
  decide +kernel
private theorem priorPositive : prior.GridPositive grid := by
  change ∀ value ∈ grid.cells, 0 < (prior.pmf value).num
  decide +kernel

/-- The global theorem includes two zero observed cells and a retained null
outlier, with no additional positive-observation hypothesis. -/
example : ExactLog.LE ExactLog.zero (observed.relativeEntropy prior grid observedSupport priorSupport priorPositive) :=
  observed.relativeEntropy_nonnegative prior grid observedSupport priorSupport priorPositive
example : ExactLog.Equiv (observed.relativeEntropy prior grid observedSupport priorSupport priorPositive)
    (ExactLog.log ⟨3, 1, by decide, by decide⟩) := by decide +kernel

/-- Nontrivial rational AM–GM is derived from natural multiplicities. -/
example : PositiveRatio.LE (RationalAMGM.weightedProduct [(⟨2, 3, by decide, by decide⟩, 1),
    (⟨4, 3, by decide, by decide⟩, 1)]) PositiveRatio.one :=
  RationalAMGM.weightedProduct_le_one _ (by decide +kernel)
/-- A recorded positive argument of zero multiplicity imposes no contribution. -/
example : PositiveRatio.LE (RationalAMGM.weightedProduct [(⟨100, 1, by decide, by decide⟩, 0)]) PositiveRatio.one :=
  RationalAMGM.weightedProduct_le_one _ (by decide +kernel)

end Thesis.Examples.EntropyGibbs
