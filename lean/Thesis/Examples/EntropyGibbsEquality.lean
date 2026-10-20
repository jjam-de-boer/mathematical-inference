import Thesis.Probability.Distros.EntropyGibbsEquality

namespace Thesis.Examples.EntropyGibbsEquality
open Probability Probability.Distros

private def grid : EntropyGrid Nat := ⟨[0, 1], by decide⟩
private def prior : Distro Nat := ⟨⟨[(0, 1), (1, 1)], 2, by decide, by decide⟩⟩
private def split : Distro Nat := ⟨⟨[(1, 2), (99, 0), (0, 1), (0, 1)], 4, by decide, by decide⟩⟩
private def point : Distro Nat := ⟨⟨[(0, 1)], 1, by decide, by decide⟩⟩
private theorem priorSupport : prior.AlmostSurely (fun value => value ∈ grid.cells) := by
  change ∀ atom ∈ prior.record.atoms, 0 < atom.2 → atom.1 ∈ grid.cells
  decide +kernel
private theorem splitSupport : split.AlmostSurely (fun value => value ∈ grid.cells) := by
  change ∀ atom ∈ split.record.atoms, 0 < atom.2 → atom.1 ∈ grid.cells
  decide +kernel
private theorem pointSupport : point.AlmostSurely (fun value => value ∈ grid.cells) := by
  change ∀ atom ∈ point.record.atoms, 0 < atom.2 → atom.1 ∈ grid.cells
  decide +kernel
private theorem priorPositive : prior.GridPositive grid := by
  change ∀ value ∈ grid.cells, 0 < (prior.pmf value).num
  decide +kernel
private theorem split_sameLaw : split.SameLaw prior := by
  intro event
  cases first : event 0 <;> cases second : event 1 <;>
    simp [split, prior, FiniteProbRecord.probVal, FiniteProbRecord.eventMass, first, second, QProb.Equiv]

/-- The equality condition concerns laws, not literal records or atom lists. -/
example : ExactLog.Equiv (split.relativeEntropy prior grid splitSupport priorSupport priorPositive) ExactLog.zero :=
  (split.relativeEntropy_equiv_zero_iff prior grid splitSupport priorSupport priorPositive).mpr split_sameLaw

/-- A missing observed cell with positive reference mass cannot hide in the
equality case, even though its KL contribution is itself zero. -/
example : ¬ ExactLog.Equiv (point.relativeEntropy prior grid pointSupport priorSupport priorPositive) ExactLog.zero := by
  intro vanished
  have laws := (point.relativeEntropy_equiv_zero_iff prior grid pointSupport priorSupport priorPositive).mp vanished
  have mismatch : ¬ QProb.Equiv (point.pmf 1) (prior.pmf 1) := by decide +kernel
  exact mismatch (laws (FiniteProbRecord.singletonEvent 1))

/-- Equality restricts every positive multiplicity; a zero-weight outlier
is deliberately left unrestricted by the general rational theorem. -/
example : ∀ item ∈ ([(⟨100, 1, by decide, by decide⟩, 0), (PositiveRatio.one, 3)] : List (PositiveRatio × Nat)),
    0 < item.2 → PositiveRatio.Equiv item.1 PositiveRatio.one :=
  RationalAMGM.eq_one_of_weightedProduct_equiv_one _ (by decide) (by decide +kernel) (by decide +kernel)

end Thesis.Examples.EntropyGibbsEquality
