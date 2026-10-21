import Thesis.Probability.Distros.EntropyConcavity
import Thesis.Probability.ExactLogRational

namespace Thesis.Examples.EntropyConcavity
open Probability Probability.Distros

private def grid : EntropyGrid Nat := ⟨[0, 1, 2], by decide⟩
private def first : Distro Nat := ⟨⟨[(0, 1), (99, 0)], 1, by decide, by decide⟩⟩
private def second : Distro Nat := ⟨⟨[(1, 1)], 1, by decide, by decide⟩⟩
private def split : Distro Nat := ⟨⟨[(88, 0), (0, 1), (0, 2)], 3, by decide, by decide⟩⟩
private theorem firstSupport : first.AlmostSurely (fun value => value ∈ grid.cells) := by
  change ∀ atom ∈ first.record.atoms, 0 < atom.2 → atom.1 ∈ grid.cells
  decide +kernel
private theorem secondSupport : second.AlmostSurely (fun value => value ∈ grid.cells) := by
  change ∀ atom ∈ second.record.atoms, 0 < atom.2 → atom.1 ∈ grid.cells
  decide +kernel
private theorem splitSupport : split.AlmostSurely (fun value => value ∈ grid.cells) := by
  change ∀ atom ∈ split.record.atoms, 0 < atom.2 → atom.1 ∈ grid.cells
  decide +kernel
private theorem different : ¬ first.SameLaw second := by
  intro same
  have mismatch : ¬ QProb.Equiv (first.pmf 0) (second.pmf 0) := by decide +kernel
  exact mismatch (same (FiniteProbRecord.singletonEvent 0))
private theorem sameSplit : first.SameLaw split := by
  intro event
  cases selected : event 0 <;>
    simp [first, split, FiniteProbRecord.probVal, FiniteProbRecord.eventMass, selected, QProb.Equiv]

/-- The shared zero cell `2` remains in the grid. Null outliers and unrelated
input denominators are retained by the mixture constructor. -/
example : ExactLog.Equiv ((first.mixture second 1 1 (by decide)).entropy grid
    (first.mixture_support second 1 1 (by decide) _ firstSupport secondSupport))
    (ExactLog.ofSignedRatio ⟨1, 1, by decide⟩) := by decide +kernel

example : ¬ ExactLog.LE ((first.mixture second 1 2 (by decide)).entropy grid
    (first.mixture_support second 1 2 (by decide) _ firstSupport secondSupport))
    (ExactLog.add (ExactLog.scaleRatio ⟨1, 3, by decide⟩ (first.entropy grid firstSupport))
      (ExactLog.scaleRatio ⟨2, 3, by decide⟩ (second.entropy grid secondSupport))) :=
  first.entropy_strict_concave second grid firstSupport secondSupport 1 2 (by decide) (by decide) (by decide) different

/-- Entropy equality depends on laws rather than literal atom records. -/
example : ExactLog.Equiv
    (ExactLog.add (ExactLog.scaleRatio ⟨2, 5, by decide⟩ (first.entropy grid firstSupport))
      (ExactLog.scaleRatio ⟨3, 5, by decide⟩ (split.entropy grid splitSupport)))
    ((first.mixture split 2 3 (by decide)).entropy grid
      (first.mixture_support split 2 3 (by decide) _ firstSupport splitSupport)) :=
  (first.entropy_mixture_comparison split grid firstSupport splitSupport 2 3 (by decide) (by decide) (by decide)).2.mpr sameSplit

end Thesis.Examples.EntropyConcavity
