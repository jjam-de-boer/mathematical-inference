import Thesis.Probability.Distros.RationalPolya
import Thesis.Probability.Distros.PositiveSupport

namespace Thesis.Probability.Distros

private theorem probabilityGrid_mass_positive (bound : Nat) (probabilities : Nat → QProb)
    (normalized : QProb.Equiv (QProb.listSum ((List.range (bound + 1)).map probabilities)) QProb.one) :
    0 < (rationalUrnWeights ((List.range (bound + 1)).map probabilities)).sum := by
  rw [rationalUrnWeights_sum]
  have same : (QProb.listSum ((List.range (bound + 1)).map probabilities)).num =
      (QProb.listSum ((List.range (bound + 1)).map probabilities)).den := by
    simpa only [QProb.Equiv, QProb.one, Nat.mul_one, Nat.one_mul] using normalized
  rw [same]
  exact (QProb.listSum _).den_pos

/-- A normalized rational table becomes a genuine finite probability record
by common-denominator clearing. There is one atom for every grid cell, even
when that cell has zero mass; no filtering or unit-cell expansion occurs. -/
def probabilityGrid (bound : Nat) (probabilities : Nat → QProb)
    (normalized : QProb.Equiv (QProb.listSum ((List.range (bound + 1)).map probabilities)) QProb.one) : Distro Nat :=
  (listCategoricalDistro (rationalUrnWeights ((List.range (bound + 1)).map probabilities))
    (probabilityGrid_mass_positive bound probabilities normalized)).map (fun i => i.val)

private theorem probabilityGrid_weights_length (bound : Nat) (probabilities : Nat → QProb) :
    (rationalUrnWeights ((List.range (bound + 1)).map probabilities)).length = bound + 1 := by
  rw [rationalUrnWeights_length, List.length_map, List.length_range]

private theorem probabilityGrid_table_getD (bound : Nat) (probabilities : Nat → QProb) (value : Nat) (within : value ≤ bound) :
    (((List.range (bound + 1)).map probabilities).getD value QProb.zero) = probabilities value := by
  rw [← List.getElem_eq_getD (h := by simpa only [List.length_map, List.length_range] using Nat.lt_succ_of_le within) QProb.zero]
  simp only [List.getElem_map, List.getElem_range]

theorem probabilityGrid_bounded (bound : Nat) (probabilities : Nat → QProb)
    (normalized : QProb.Equiv (QProb.listSum ((List.range (bound + 1)).map probabilities)) QProb.one) :
    (probabilityGrid bound probabilities normalized).AlmostSurely (fun value => value ≤ bound) := by
  intro atom member _
  change atom ∈ (finWeighted (rationalUrnWeights ((List.range (bound + 1)).map probabilities)).length
    (fun i => (rationalUrnWeights ((List.range (bound + 1)).map probabilities)).getD i.val 0)).map
      (fun atom => (atom.1.val, atom.2)) at member
  rcases List.mem_map.mp member with ⟨source, _, same⟩
  cases same
  have within : source.1.val < bound + 1 := by
    simpa only [probabilityGrid_weights_length] using source.1.isLt
  omega

/-- Every table probability is recovered at its actual grid cell. -/
theorem probabilityGrid_pmf (bound : Nat) (probabilities : Nat → QProb)
    (normalized : QProb.Equiv (QProb.listSum ((List.range (bound + 1)).map probabilities)) QProb.one)
    (value : Nat) (within : value ≤ bound) :
    QProb.Equiv ((probabilityGrid bound probabilities normalized).pmf value) (probabilities value) := by
  let table := (List.range (bound + 1)).map probabilities
  let weights := rationalUrnWeights table
  have positive := probabilityGrid_mass_positive bound probabilities normalized
  let index : Fin weights.length := ⟨value, by rw [probabilityGrid_weights_length]; omega⟩
  have events : (fun i : Fin weights.length => FiniteProbRecord.singletonEvent value i.val) =
      FiniteProbRecord.singletonEvent index := by
    funext i
    simp only [FiniteProbRecord.singletonEvent, Fin.ext_iff]
    rfl
  refine QProb.equiv_trans (Distro.map_pmf (listCategoricalDistro weights positive) (fun i => i.val) value) ?_
  rw [events]
  have cell := categorical_pmf weights.length (fun i => weights.getD i.val 0)
    (by rw [finWeight_getD_sum]; exact positive) index
  change QProb.Equiv ((listCategoricalDistro weights positive).pmf index)
    ⟨weights.getD value 0, (listCategoricalDistro weights positive).record.den, _⟩ at cell
  have actual : QProb.Equiv ((listCategoricalDistro weights positive).pmf index)
      ⟨weights.getD value 0, weights.sum, positive⟩ := by
    simpa only [listCategorical_den] using cell
  refine QProb.equiv_trans actual ?_
  have same : (QProb.listSum table).num = (QProb.listSum table).den := by
    simpa only [QProb.Equiv, QProb.one, Nat.mul_one, Nat.one_mul] using normalized
  have representation := rationalUrnWeights_parameter table value
  rw [probabilityGrid_table_getD bound probabilities value within] at representation
  change QProb.Equiv (⟨(rationalUrnWeights table).getD value 0, (rationalUrnWeights table).sum, positive⟩ : QProb) _
  change (rationalUrnWeights table).getD value 0 * (probabilities value).den =
    (probabilities value).num * (rationalUrnWeights table).sum
  rw [rationalUrnWeights_sum, same]
  exact representation

private theorem finWeighted_cell_mem (n : Nat) (weights : Fin n → Nat) (index : Fin n) :
    (index, weights index) ∈ finWeighted n weights := by
  induction n with
  | zero => exact False.elim (Nat.not_lt_zero _ index.isLt)
  | succ n ih =>
      rw [finWeighted]
      by_cases earlier : index.val < n
      · let old : Fin n := ⟨index.val, earlier⟩
        have same : old.castSucc = index := Fin.ext rfl
        apply List.mem_append_left
        apply List.mem_map.mpr
        refine ⟨(old, weights old.castSucc), ih (fun i => weights i.castSucc) old, ?_⟩
        change (old.castSucc, weights old.castSucc) = (index, weights index)
        rw [same]
      · have same : index = Fin.last n := Fin.ext (by simp only [Fin.val_last]; have upper := index.isLt; omega)
        rw [same]
        exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Every declared grid cell has an occurrence in the constructed record,
including cells of zero probability. -/
theorem probabilityGrid_retains (bound : Nat) (probabilities : Nat → QProb)
    (normalized : QProb.Equiv (QProb.listSum ((List.range (bound + 1)).map probabilities)) QProb.one)
    (value : Nat) (within : value ≤ bound) :
    ∃ weight, (value, weight) ∈ (probabilityGrid bound probabilities normalized).record.atoms := by
  let weights := rationalUrnWeights ((List.range (bound + 1)).map probabilities)
  let index : Fin weights.length := ⟨value, by rw [probabilityGrid_weights_length]; omega⟩
  refine ⟨weights.getD value 0, ?_⟩
  change (value, weights.getD value 0) ∈
    (finWeighted weights.length (fun i => weights.getD i.val 0)).map (fun atom => (atom.1.val, atom.2))
  exact List.mem_map.mpr ⟨(index, weights.getD index.val 0), finWeighted_cell_mem _ _ index, rfl⟩

end Thesis.Probability.Distros
