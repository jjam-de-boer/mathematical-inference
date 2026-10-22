import Thesis.Probability.Distros.UncertaintyUniform

namespace Thesis.Examples.UncertaintyMeasure
open Probability Probability.ProbabilityVector

private def point : ProbabilityVector := ⟨[QProb.one], by decide⟩
private def thirds : ProbabilityVector := ⟨[⟨2, 3, by decide⟩, ⟨1, 3, by decide⟩], by decide⟩
private def quarters : ProbabilityVector := ⟨[⟨1, 4, by decide⟩, ⟨3, 4, by decide⟩], by decide⟩
private def choice : Compound :=
  ⟨[(⟨1, 2, by decide⟩, point), (⟨1, 2, by decide⟩, thirds), (QProb.zero, quarters)], by decide⟩

/-- The standard three-way grouping example retains both null coordinates
created by its additional zero-probability branch. -/
example : choice.refined.masses.length = 5 := by decide +kernel
example : ExactLog.Equiv choice.refined.entropy
    (ExactLog.root ⟨432, 1, by decide, by decide⟩ 6 (by decide)) := by decide +kernel

example : ExactLog.Equiv (Probability.UncertaintyMeasure.shannon.value choice.refined)
    (ExactLog.add (Probability.UncertaintyMeasure.shannon.value choice.outer)
      (ExactLog.listSum (choice.branches.map (fun branch =>
        ExactLog.scaleRatio branch.1 (Probability.UncertaintyMeasure.shannon.value branch.2))))) :=
  Probability.UncertaintyMeasure.shannon.grouping choice

private def rescaledFair : ProbabilityVector := ⟨[⟨2, 4, by decide⟩, ⟨3, 6, by decide⟩], by decide⟩
example : ExactLog.Equiv (Probability.UncertaintyMeasure.shannon.value rescaledFair)
    (Probability.UncertaintyMeasure.shannon.value (uniform 2 (by decide))) :=
  Probability.UncertaintyMeasure.shannon.representation _ _ (by decide +kernel)

example : ExactLog.Equiv rescaledFair.addNull.entropy (ExactLog.log ⟨2, 1, by decide, by decide⟩) := by decide +kernel

/-- These laws hold for every measure satisfying the abstract requirements,
not merely for the already selected Shannon formula. -/
example (measure : Probability.UncertaintyMeasure) :
    ExactLog.Equiv (measure.value (uniform 1 (by decide))) ExactLog.zero := measure.uniform_one
example (measure : Probability.UncertaintyMeasure) :
    ExactLog.Equiv (measure.value (uniform 729 (by decide)))
      (ExactLog.scaleNat 6 (measure.value (uniform 3 (by decide)))) := measure.uniform_pow 3 6 (by decide)

private def grid : Distros.EntropyGrid Nat := ⟨[0, 1], by decide⟩
private def split : Distros.Distro Nat := ⟨⟨[(0, 1), (1, 2), (99, 0), (0, 1)], 4, by decide, by decide⟩⟩
private theorem support : split.AlmostSurely (fun value => value ∈ grid.cells) := by
  change ∀ atom ∈ split.record.atoms, 0 < atom.2 → atom.1 ∈ grid.cells
  decide +kernel

/-- The vector bridge reads aggregated observable masses, with two states
rather than four atom occurrences. -/
example : (ofDistro split grid support).masses.length = 2 := by decide +kernel
example : (ofDistro split grid support).entropy = split.entropy grid support := ofDistro_entropy split grid support
example : ExactLog.Equiv (ofDistro split grid support).entropy
    (ExactLog.log ⟨2, 1, by decide, by decide⟩) := by decide +kernel

end Thesis.Examples.UncertaintyMeasure
