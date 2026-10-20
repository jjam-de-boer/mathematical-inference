import Thesis.Probability.Distros.Entropy
import Thesis.Probability.Distros.PositiveSupport
import Thesis.Probability.EntropyRatios
import Thesis.Probability.LogMeanInequality

namespace Thesis.Probability.Distros

/-- Aggregated singleton probabilities normalize on every distinct grid
containing the positive support, regardless of additional null atom labels. -/
theorem Distro.pmf_grid_normalization [DecidableEq A] (μ : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells)) :
    QProb.Equiv (QProb.listSum (grid.cells.map μ.pmf)) QProb.one := by
  refine QProb.equiv_trans (QProb.equiv_symm (μ.record.probVal_membership_equiv_listSum grid.cells grid.distinct)) ?_
  refine QProb.equiv_trans (μ.probVal_congr_positive (FiniteProbRecord.membershipEvent grid.cells) topEvent ?_) μ.normalization
  intro atom member weight
  simp only [FiniteProbRecord.membershipEvent, support atom member weight, decide_true, topEvent]

/-- The original common-denominator singleton numerators sum to the original
record denominator, even for records that split observable outcomes. -/
theorem Distro.pmf_grid_numerator_sum [DecidableEq A] (μ : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells)) :
    (grid.cells.map (fun value => (μ.pmf value).num)).sum = μ.record.den := by
  have represented := QProb.listSum_mk_same_den μ.record.den μ.record.den_pos
    (grid.cells.map (fun value => (μ.pmf value).num))
  have same : QProb.Equiv (QProb.listSum (grid.cells.map μ.pmf))
      ⟨(grid.cells.map (fun value => (μ.pmf value).num)).sum, μ.record.den, μ.record.den_pos⟩ := by
    simpa only [List.map_map, Distro.pmf, FiniteProbRecord.probVal] using represented
  have normalized := QProb.equiv_trans (QProb.equiv_symm same) (μ.pmf_grid_normalization grid support)
  simpa only [QProb.Equiv, QProb.one, Nat.mul_one, Nat.one_mul] using normalized

/-- Multiplicities are observed singleton numerators, not atom-occurrence
weights. A retained zero-mass grid cell receives multiplicity zero. -/
def Distro.relativeRatioItems [DecidableEq A] (μ reference : Distro A) (grid : EntropyGrid A)
    (positive : reference.GridPositive grid) : List (PositiveRatio × Nat) :=
  grid.cells.attach.map (fun cell =>
    (relativeRatio (μ.pmf cell.val) (reference.pmf cell.val) (positive cell.val cell.property), (μ.pmf cell.val).num))

theorem Distro.relativeRatioItems_weight [DecidableEq A] (μ reference : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells)) (positive : reference.GridPositive grid) :
    RationalAMGM.totalWeight (μ.relativeRatioItems reference grid positive) = μ.record.den := by
  rw [relativeRatioItems, RationalAMGM.totalWeight_map,
    List.attach_map_val (f := fun value => (μ.pmf value).num)]
  exact μ.pmf_grid_numerator_sum grid support

theorem Distro.relativeEntropy_logMean [DecidableEq A] (μ reference : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (referenceSupport : reference.AlmostSurely (fun value => value ∈ grid.cells))
    (positive : reference.GridPositive grid) :
    ExactLog.Equiv (μ.relativeEntropy reference grid support referenceSupport positive)
      (RationalAMGM.logMean (μ.relativeRatioItems reference grid positive) μ.record.den μ.record.den_pos) := by
  unfold relativeEntropy RationalAMGM.logMean relativeRatioItems
  rw [List.map_map]
  apply ExactLog.listSum_map_congr
  intro cell _
  exact relativeEntropyTerm_root _ _ _

/-- Finite KL nonnegativity for arbitrary rational laws and a positive
reference law, proved by rational AM–GM on the aggregated likelihood ratios. -/
theorem Distro.relativeEntropy_nonnegative [DecidableEq A] (μ reference : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (referenceSupport : reference.AlmostSurely (fun value => value ∈ grid.cells))
    (positive : reference.GridPositive grid) :
    ExactLog.LE ExactLog.zero (μ.relativeEntropy reference grid support referenceSupport positive) := by
  have arithmetic : QProb.LE
      (RationalAMGM.weightedSum (RationalAMGM.inverses (μ.relativeRatioItems reference grid positive)))
      (QProb.ofNat (RationalAMGM.totalWeight (μ.relativeRatioItems reference grid positive))) := by
    rw [μ.relativeRatioItems_weight reference grid support positive]
    unfold relativeRatioItems RationalAMGM.inverses
    rw [List.map_map, RationalAMGM.weightedSum_map]
    have compared := QProb.listSum_map_mono grid.cells.attach
      (fun cell => QProb.scale (μ.pmf cell.val).num
        (relativeRatio (μ.pmf cell.val) (reference.pmf cell.val) (positive cell.val cell.property)).inv.toQProb)
      (fun cell => QProb.scale μ.record.den (reference.pmf cell.val))
      (fun cell _ => inverse_relativeRatio_bound _ _ _)
    have scaled : QProb.Equiv
        (QProb.listSum (grid.cells.attach.map (fun cell => QProb.scale μ.record.den (reference.pmf cell.val))))
        (QProb.ofNat μ.record.den) := by
      rw [List.attach_map_val (f := fun value => QProb.scale μ.record.den (reference.pmf value))]
      have distributed := QProb.listSum_scale (grid.cells.map reference.pmf) μ.record.den
      rw [List.map_map] at distributed
      refine QProb.equiv_trans distributed ?_
      have normalized := QProb.scale_congr μ.record.den (reference.pmf_grid_normalization grid referenceSupport)
      exact QProb.equiv_trans normalized (by simp only [QProb.Equiv, QProb.scale, QProb.one, QProb.ofNat, Nat.mul_one])
    exact QProb.le_congr (QProb.equiv_refl _) scaled compared
  have result := RationalAMGM.logMean_nonnegative (μ.relativeRatioItems reference grid positive)
    μ.record.den μ.record.den_pos arithmetic
  exact (ExactLog.le_congr (ExactLog.equiv_refl _)
    (μ.relativeEntropy_logMean reference grid support referenceSupport positive)).mpr result

end Thesis.Probability.Distros
