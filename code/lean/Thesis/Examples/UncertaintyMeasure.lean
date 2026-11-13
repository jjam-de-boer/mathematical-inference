import Thesis.Probability.ExactLogRational
import Thesis.Probability.Distros.UncertaintyCharacterization

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

/-- The logarithm of a uniform space is derived for an arbitrary measure;
its specification contains no logarithm formula for general cardinalities. -/
example (measure : Probability.UncertaintyMeasure) (size : Nat) (positive : 0 < size) :
    ExactLog.Equiv (measure.value (uniform size positive))
      (ExactLog.log (PositiveRatio.ofNat size positive)) := measure.uniform_log size positive

example (measure : Probability.UncertaintyMeasure) :
    ExactLog.LE (ExactLog.ofSignedRatio ⟨158, 100, by decide⟩)
      (measure.value (uniform 3 (by decide))) := by
  have lower : ExactLog.LE (ExactLog.ofSignedRatio ⟨158, 100, by decide⟩)
      (ExactLog.log (PositiveRatio.ofNat 3 (by decide))) := by decide +kernel
  exact (ExactLog.le_congr (ExactLog.equiv_refl _) (ExactLog.equiv_symm (measure.uniform_log 3 (by decide)))).mp lower

/-- The common denominator is constructed from the actual unreduced
entries, and the two coordinates remain separate observable alternatives. -/
example : rescaledFair.countPresentation.den = 24 := by decide +kernel
example : rescaledFair.countPresentation.counts = [12, 12] := by decide +kernel

private def boundary : ProbabilityVector :=
  ⟨[⟨0, 7, by decide⟩, ⟨2, 4, by decide⟩, QProb.zero, ⟨3, 6, by decide⟩, ⟨0, 19, by decide⟩], by decide⟩

/-- Every admissible measure assigns one bit to this boundary vector,
including all three declared null coordinates and unequal denominators. -/
example (measure : Probability.UncertaintyMeasure) : ExactLog.Equiv (measure.value boundary)
    (ExactLog.log ⟨2, 1, by decide, by decide⟩) :=
  ExactLog.equiv_trans (measure.characterization boundary) (by decide +kernel)

example (first second : Probability.UncertaintyMeasure) (vector : ProbabilityVector) :
    ExactLog.Equiv (first.value vector) (second.value vector) := first.unique second vector

example (measure : Probability.UncertaintyMeasure) : ExactLog.Equiv (measure.value choice.refined)
    (ExactLog.root ⟨432, 1, by decide, by decide⟩ 6 (by decide)) :=
  ExactLog.equiv_trans (measure.characterization choice.refined) (by decide +kernel)

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

example (measure : Probability.UncertaintyMeasure) :
    ExactLog.Equiv (measure.value (ofDistro split grid support)) (split.entropy grid support) :=
  measure.distro_characterization split grid support

end Thesis.Examples.UncertaintyMeasure
