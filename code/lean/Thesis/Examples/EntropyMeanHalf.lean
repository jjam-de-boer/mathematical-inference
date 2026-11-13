import Thesis.Probability.Distros.LogLinearEntropy
import Thesis.Probability.Distros.EntropyOptimize
import Thesis.Probability.Distros.EntropyHomogeneous

namespace Thesis.Examples.EntropyMeanHalf
open Probability Probability.Distros

private def meanHalf : MomentInterval Nat := MomentInterval.exact (fun value => (value : Int)) ⟨1, 2, by decide⟩
private def redundant : MomentInterval Nat := MomentInterval.exact (fun _ => -3) ⟨-3, 1, by decide⟩

/-- The original three outcomes with exact mean one half and redundant rows. -/
def problem : PartialMomentProblem Nat :=
  ⟨[0, 1, 2], 0, by decide, by decide, [meanHalf, redundant, redundant]⟩

/-- An exactly feasible rational approximation, with a split atom and null
outlier deliberately retained in its presentation. -/
def candidate : Distro Nat := ⟨⟨[(0, 31), (1, 26), (0, 31), (2, 12), (99, 0)], 100, by decide, by decide⟩⟩
private theorem candidateSupport : candidate.AlmostSurely (fun value => value ∈ problem.cells) := by
  change ∀ atom ∈ candidate.record.atoms, 0 < atom.2 → atom.1 ∈ problem.cells
  decide +kernel
private theorem candidateMoments : ∀ constraint ∈ problem.intervals, constraint.LawHolds candidate := by
  intro constraint member
  change constraint ∈ [meanHalf, redundant, redundant] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> exact ⟨by decide +kernel, by decide +kernel⟩

def anchor : problem.CompatibleLaw := ⟨candidate, candidateSupport, candidateMoments, by
  intro value member
  change value ∈ [0, 1, 2] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨31, by decide⟩
  · exact ⟨26, by decide⟩
  · exact ⟨12, by decide⟩⟩

private def reference : Distro Nat := ⟨⟨[(0, 900), (1, 390), (2, 169), (88, 0)], 1459, by decide, by decide⟩⟩
private theorem referenceSupport : reference.AlmostSurely (fun value => value ∈ problem.cells) := by
  change ∀ atom ∈ reference.record.atoms, 0 < atom.2 → atom.1 ∈ problem.cells
  decide +kernel
private theorem referencePositive : reference.GridPositive problem.entropyGrid := by
  change ∀ value ∈ problem.cells, 0 < (reference.pmf value).num
  decide +kernel
private def coefficient : ExactLog := ExactLog.log ⟨30, 13, by decide, by decide⟩
private def offset : ExactLog := ExactLog.log ⟨1459, 900, by decide, by decide⟩
private def scoreCertificate : problem.LogLinearReference where
  reference := reference
  support := referenceSupport
  positive := referencePositive
  constraints := [meanHalf]
  listed := by
    intro constraint member
    have same := List.mem_singleton.mp member
    subst constraint
    exact List.mem_cons_self ..
  exact := by
    intro constraint member
    have same := List.mem_singleton.mp member
    subst constraint
    exact SignedRatio.equiv_refl _
  coefficient := fun _ => coefficient
  offset := offset
  score := by
    intro value member
    change value ∈ [0, 1, 2] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide +kernel +revert

private def candidateEntropy : ExactLog := ExactLog.root
  ⟨100 ^ 100, 62 ^ 62 * 26 ^ 26 * 12 ^ 12, by decide +kernel, by decide +kernel⟩ 100 (by decide)
private theorem candidateEntropy_spec : ExactLog.Equiv (candidate.entropy problem.entropyGrid candidateSupport) candidateEntropy := by
  have homogeneous := candidate.entropy_homogeneous problem.entropyGrid candidateSupport
  have represented : ExactLog.root (RationalAMGM.weightedProduct (candidate.entropyRatioItems problem.entropyGrid))
      candidate.record.den candidate.record.den_pos = candidateEntropy := by
    apply ExactLog.ext
    · apply PositiveRatio.ext <;> decide +kernel
    · rfl
  rw [represented] at homogeneous
  exact homogeneous

private def crossEntropyBound : ExactLog := ExactLog.root ⟨2128681, 351000, by decide, by decide⟩ 2 (by decide)
private theorem crossEntropy_spec : ExactLog.Equiv
    (candidate.crossEntropy reference problem.entropyGrid candidateSupport referenceSupport referencePositive) crossEntropyBound := by
  have expanded := scoreCertificate.crossEntropy_affine candidate candidateSupport
  change ExactLog.Equiv _ (ExactLog.add offset (ExactLog.add
    (ExactLog.scaleRatio (candidate.expectNat (problem.entropyGrid.shiftedResponse meanHalf.response)) coefficient) ExactLog.zero)) at expanded
  rw [ExactLog.add_zero] at expanded
  have mean : QProb.Equiv (candidate.expectNat (problem.entropyGrid.shiftedResponse meanHalf.response)) ⟨1, 2, by decide⟩ := by decide +kernel
  have reduced := ExactLog.add_congr (ExactLog.equiv_refl offset) (ExactLog.scaleRatio_weight_congr mean coefficient)
  have closed : ExactLog.Equiv (ExactLog.add offset (ExactLog.scaleRatio ⟨1, 2, by decide⟩ coefficient)) crossEntropyBound := by decide +kernel
  exact ExactLog.equiv_trans expanded (ExactLog.equiv_trans reduced closed)

private theorem lowerBound : ExactLog.LE (ExactLog.ofQProb ⟨2599, 2000, by decide⟩) candidateEntropy := by decide +kernel
private theorem upperBound : ExactLog.LE crossEntropyBound (ExactLog.ofQProb ⟨2601, 2000, by decide⟩) := by decide +kernel

/-- Exactly feasible mean `1/2`, with the universal entropy interval
`[1.2995, 1.3005]` bits. Its width is exactly `1/1000`. The upper bound ranges
over every feasible rational law, not a finite sample of competitors. -/
def certificate : problem.EntropyCertificate ⟨1, 1000, by decide⟩ where
  law := anchor
  lower := ⟨2599, 2000, by decide⟩
  upper := ⟨2601, 2000, by decide⟩
  lower_bound := (ExactLog.le_congr (ExactLog.equiv_refl _) (ExactLog.equiv_symm candidateEntropy_spec)).mp lowerBound
  global_bound := by
    intro μ valid
    have bound := scoreCertificate.entropy_upper anchor μ valid
    have closed := (ExactLog.le_congr (ExactLog.equiv_refl _) crossEntropy_spec).mp bound
    exact ExactLog.le_trans closed upperBound
  gap := by decide +kernel

/-- The auxiliary positive reference has a different mean. Its role is a
global upper certificate, not an assumed feasible exact maximizer. -/
example : ¬ SignedRatio.Equiv (meanHalf.mean reference) ⟨1, 2, by decide⟩ := by decide +kernel

example : QProb.LE (QProb.sub certificate.upper certificate.lower certificate.lower_le_upper)
    ⟨1, 1000, by decide⟩ := certificate.width_bound

/-- The general total algorithm also supplies an exactly feasible certified
approximation at every positive rational error. Its exhaustive fallback can
be expensive; the concrete certificate above avoids enumerating that cover. -/
def approximate (epsilon : QProb) (positive : 0 < epsilon.num) : problem.EntropyCertificate epsilon :=
  problem.certifyEntropy anchor epsilon positive

end Thesis.Examples.EntropyMeanHalf
