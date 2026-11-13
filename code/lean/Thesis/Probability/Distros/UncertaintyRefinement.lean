import Thesis.Probability.Distros.UncertaintyUniformUniqueness
import Thesis.Probability.Distros.ProbabilityVectorCounts

namespace Thesis.Probability.UncertaintyMeasure
open ProbabilityVector

private def countRefinement (counts : List Nat) (den : Nat) (positive : 0 < den) (mass : counts.sum = den)
    (nonzero : ∀ count ∈ counts, 0 < count) : Compound where
  branches := counts.attach.map (fun entry => (⟨entry.val, den, positive⟩,
    uniform entry.val (nonzero entry.val entry.property)))
  normalized := by
    simp only [List.map_map, Function.comp_def]
    rw [List.attach_map_val (f := fun count : Nat => (⟨count, den, positive⟩ : QProb))]
    exact (ofCounts counts den positive mass).normalized

private theorem countRefinement_outer (counts : List Nat) (den : Nat) (positive : 0 < den) (mass : counts.sum = den)
    (nonzero : ∀ count ∈ counts, 0 < count) :
    (countRefinement counts den positive mass nonzero).outer = ofCounts counts den positive mass := by
  apply ProbabilityVector.ext
  simp only [Compound.outer, countRefinement, ofCounts, List.map_map, Function.comp_def]
  exact List.attach_map_val (f := fun count : Nat => (⟨count, den, positive⟩ : QProb))

private theorem countRefinement_length (counts : List Nat) (den : Nat) (positive : 0 < den) (mass : counts.sum = den)
    (nonzero : ∀ count ∈ counts, 0 < count) :
    (countRefinement counts den positive mass nonzero).refined.masses.length = den := by
  simp only [Compound.refined, countRefinement, uniform, List.length_flatMap, List.map_map,
    List.length_map, List.length_replicate, Function.comp_def]
  rw [List.attach_map_val (f := fun count : Nat => count), List.map_id']
  exact mass

private theorem countRefinement_uniform (counts : List Nat) (den : Nat) (positive : 0 < den) (mass : counts.sum = den)
    (nonzero : ∀ count ∈ counts, 0 < count) :
    SameMasses (countRefinement counts den positive mass nonzero).refined.masses (uniform den positive).masses := by
  have same := sameMasses_replicate (countRefinement counts den positive mass nonzero).refined.masses
    (⟨1, den, positive⟩ : QProb) (by
      intro probability member
      rcases List.mem_flatMap.mp member with ⟨branch, listed, inside⟩
      rcases List.mem_map.mp listed with ⟨entry, _, rfl⟩
      simp only [uniform, List.map_replicate] at inside
      have equal := List.eq_of_mem_replicate inside
      subst probability
      simp only [QProb.Equiv, QProb.mul, Nat.mul_one, Nat.one_mul]
      ac_rfl)
  rw [countRefinement_length counts den positive mass nonzero] at same
  exact same

/-- Grouping a uniform refinement forces agreement at every strictly
positive count presentation, for any two admissible uncertainty measures. -/
theorem positive_counts_unique (first second : UncertaintyMeasure) (counts : List Nat)
    (den : Nat) (positive : 0 < den) (mass : counts.sum = den) (nonzero : ∀ count ∈ counts, 0 < count) :
    ExactLog.Equiv (first.value (ofCounts counts den positive mass)) (second.value (ofCounts counts den positive mass)) := by
  let choice := countRefinement counts den positive mass nonzero
  have uniformMasses := countRefinement_uniform counts den positive mass nonzero
  have firstToUniform := first.representation choice.refined (uniform den positive) uniformMasses
  have secondToUniform := second.representation choice.refined (uniform den positive) uniformMasses
  have refinedSame := ExactLog.equiv_trans firstToUniform
    (ExactLog.equiv_trans (first.uniform_unique second den positive) (ExactLog.equiv_symm secondToUniform))
  have grouped := ExactLog.equiv_trans (ExactLog.equiv_symm (first.grouping choice))
    (ExactLog.equiv_trans refinedSame (second.grouping choice))
  have conditional : ExactLog.Equiv
      (ExactLog.listSum (choice.branches.map (fun branch => ExactLog.scaleRatio branch.1 (first.value branch.2))))
      (ExactLog.listSum (choice.branches.map (fun branch => ExactLog.scaleRatio branch.1 (second.value branch.2)))) := by
    apply ExactLog.listSum_map_congr
    intro branch member
    rcases List.mem_map.mp member with ⟨entry, _, rfl⟩
    exact ExactLog.scaleRatio_value_congr _ (first.uniform_unique second entry.val (nonzero entry.val entry.property))
  have aligned := ExactLog.equiv_trans grouped
    (ExactLog.add_congr (ExactLog.equiv_refl _) (ExactLog.equiv_symm conditional))
  have bounds := (ExactLog.equiv_iff_le _ _).mp aligned
  have result := (ExactLog.equiv_iff_le (first.value choice.outer) (second.value choice.outer)).mpr
    ⟨(ExactLog.add_le_add_right_iff _ _ _).mp bounds.1, (ExactLog.add_le_add_right_iff _ _ _).mp bounds.2⟩
  rw [countRefinement_outer counts den positive mass nonzero] at result
  exact result

end Thesis.Probability.UncertaintyMeasure
