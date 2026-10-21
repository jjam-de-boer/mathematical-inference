import Thesis.Probability.Distros.EntropyMomentConvex

namespace Thesis.Examples.EntropyMoments
open Probability Probability.Distros

private def meanOne : MomentInterval Nat := MomentInterval.exact (fun x => (x : Int)) SignedRatio.one
private def zeroLast : MomentInterval Nat := MomentInterval.exact (fun x => if x = 3 then 1 else 0) SignedRatio.zero
private def signedBand : MomentInterval Nat := ⟨(fun x => if x = 0 then -2 else 1), ⟨-1, 1, by decide⟩, SignedRatio.one⟩
private def redundant : MomentInterval Nat := MomentInterval.exact (fun _ => -3) ⟨-3, 1, by decide⟩
private def problem : PartialMomentProblem Nat :=
  ⟨[0, 1, 2, 3], 0, by decide, by decide, [meanOne, zeroLast, signedBand, redundant, redundant]⟩
private def first : Distro Nat := ⟨⟨[(0, 1), (2, 1), (88, 0)], 2, by decide, by decide⟩⟩
private def second : Distro Nat := ⟨⟨[(1, 3), (99, 0)], 3, by decide, by decide⟩⟩
private theorem firstValid : problem.Admissible first := by
  constructor
  · change ∀ atom ∈ first.record.atoms, 0 < atom.2 → atom.1 ∈ problem.cells
    decide +kernel
  · intro constraint member
    change constraint ∈ [meanOne, zeroLast, signedBand, redundant, redundant] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by decide +kernel, by decide +kernel⟩
private theorem secondValid : problem.Admissible second := by
  constructor
  · change ∀ atom ∈ second.record.atoms, 0 < atom.2 → atom.1 ∈ problem.cells
    decide +kernel
  · intro constraint member
    change constraint ∈ [meanOne, zeroLast, signedBand, redundant, redundant] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by decide +kernel, by decide +kernel⟩

/-- Exact mean, signed interval, forced zero and repeated rows are preserved
by the same mixture to which the entropy-concavity theorem applies. -/
example : problem.Admissible (first.mixture second 1 2 (by decide)) :=
  problem.admissible_mixture first second firstValid secondValid 1 2 (by decide)

example : QProb.Equiv ((first.mixture second 1 2 (by decide)).pmf 1) ⟨2, 3, by decide⟩ := by decide +kernel
example : QProb.Equiv ((first.mixture second 1 2 (by decide)).pmf 3) QProb.zero := by decide +kernel

/-- The uniqueness interface quantifies over all exactly feasible rational
laws, rather than a supplied denominator grid or a finite candidate list. -/
example (μ ν : Distro Nat) (first : problem.Admissible μ) (second : problem.Admissible ν)
    (maxFirst : ∀ ρ (valid : problem.Admissible ρ),
      ExactLog.LE (ρ.entropy problem.entropyGrid valid.1) (μ.entropy problem.entropyGrid first.1))
    (maxSecond : ∀ ρ (valid : problem.Admissible ρ),
      ExactLog.LE (ρ.entropy problem.entropyGrid valid.1) (ν.entropy problem.entropyGrid second.1)) : μ.SameLaw ν :=
  problem.entropy_maximum_unique μ ν first second maxFirst maxSecond

end Thesis.Examples.EntropyMoments
