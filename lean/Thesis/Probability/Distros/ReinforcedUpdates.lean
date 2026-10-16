import Thesis.Probability.Distros.ReinforcedConditioning
import Thesis.Probability.Distros.ReinforcedExchangeability
import Thesis.Probability.Distros.RationalPolya
namespace Thesis.Probability.Distros
open Combinatorics

theorem colourCounts_sum (colours : Nat) (word : List Nat)
    (valid : ∀ colour ∈ word, colour < colours) : (colourCounts colours word).sum = word.length := by
  induction word with
  | nil => simp only [colourCounts, List.sum_replicate_nat, Nat.mul_zero, List.length_nil]
  | cons colour word ih =>
      rw [colourCounts, sum_modify_add _ colour 1 (by rw [colourCounts_length]; exact valid colour (List.mem_cons_self ..)),
        ih (fun other member => valid other (List.mem_cons_of_mem _ member)), List.length_cons]

theorem eventMass_positive_witness (atoms : List (Ω × Nat)) (event : Event Ω)
    (positive : 0 < FiniteProbRecord.eventMass atoms event) :
    ∃ atom ∈ atoms, event atom.1 = true ∧ 0 < atom.2 := by
  induction atoms with
  | nil => change 0 < 0 at positive; omega
  | cons atom atoms ih =>
      by_cases selected : event atom.1 = true
      · by_cases weight : 0 < atom.2
        · exact ⟨atom, List.mem_cons_self .., selected, weight⟩
        · have tail : 0 < FiniteProbRecord.eventMass atoms event := by
            simp only [FiniteProbRecord.eventMass, selected, if_true] at positive
            omega
          rcases ih tail with ⟨value, member, evidence, weight⟩
          exact ⟨value, List.mem_cons_of_mem _ member, evidence, weight⟩
      · have tail : 0 < FiniteProbRecord.eventMass atoms event := by
          simpa only [FiniteProbRecord.eventMass, selected, if_false] using positive
        rcases ih tail with ⟨value, member, evidence, weight⟩
        exact ⟨value, List.mem_cons_of_mem _ member, evidence, weight⟩

theorem reinforcedCountsSupported_shape (m : Nat) (alphas counts : List Nat) (increment : Nat)
    (supported : reinforcedCountsSupported m alphas increment counts) :
    counts.length = alphas.length ∧ counts.sum = m := by
  rcases eventMass_positive_witness (reinforcedUrnAtoms m alphas increment)
    (fun word => decide (colourCounts alphas.length word = counts)) supported with ⟨atom, member, selected, _⟩
  have same : colourCounts alphas.length atom.1 = counts := of_decide_eq_true selected
  have shape := reinforcedUrn_word_support m alphas increment atom member
  rw [← same]
  exact ⟨colourCounts_length _ _, (colourCounts_sum _ _ shape.2).trans shape.1⟩

theorem reinforcedCountsSupported_iff_pmf (m : Nat) (alphas counts : List Nat) (increment : Nat)
    (positive : 0 < alphas.sum) :
    reinforcedCountsSupported m alphas increment counts ↔
      0 < ((reinforcedCountDistro m alphas increment positive).pmf counts).num := by
  have mapped := (reinforcedUrnDistro m alphas increment positive).map_probVal (colourCounts alphas.length)
    (FiniteProbRecord.singletonEvent counts)
  have law := reinforcedUrn_count_correspondence m alphas increment positive (FiniteProbRecord.singletonEvent counts)
  exact QProb.equiv_num_pos_iff (QProb.equiv_trans (QProb.equiv_symm mapped) law)

theorem reinforcedUrn_one_colour (alphas : List Nat) (increment : Nat) (positive : 0 < alphas.sum)
    (i : Nat) (within : i < alphas.length) :
    QProb.Equiv ((reinforcedUrnDistro 1 alphas increment positive).pmf [i])
      ⟨alphas.getD i 0, alphas.sum, positive⟩ := by
  change FiniteProbRecord.eventMass (reinforcedUrnAtoms [i].length alphas increment)
      (FiniteProbRecord.singletonEvent [i]) * alphas.sum =
    alphas.getD i 0 * (reinforcedUrnDistro 1 alphas increment positive).record.den
  rw [reinforcedUrn_word_mass alphas increment [i] (by
    intro colour member; have eq := List.mem_singleton.mp member; subst colour; exact within), reinforcedUrn_den]
  simp only [reinforcedWordWeight, stepRising, Nat.mul_one]

/-- The predictive probability after observing a count vector, expressed
in the original parameter units and the number of observed draws. -/
theorem reinforced_next_after_counts (m : Nat) (alphas counts : List Nat) (increment : Nat)
    (positive : 0 < alphas.sum) (supported : reinforcedCountsSupported m alphas increment counts)
    (i : Nat) (within : i < alphas.length) :
    QProb.Equiv ((reinforcedCountsContinuation m 1 alphas counts increment positive
      (reinforcedCountsSupported_shape m alphas counts increment supported).1 supported).pmf [i])
      ⟨alphas.getD i 0 + increment * counts.getD i 0, alphas.sum + increment * m, by omega⟩ := by
  have shape := reinforcedCountsSupported_shape m alphas counts increment supported
  refine QProb.equiv_trans (reinforcedCountsContinuation_updated m 1 alphas counts increment positive shape.1 supported
    (FiniteProbRecord.singletonEvent [i])) ?_
  have next := reinforcedUrn_one_colour (reinforcedState increment alphas counts) increment
    (by rw [reinforcedState_sum _ _ _ shape.1]; omega) i (by rw [reinforcedState_length]; exact within)
  simpa only [reinforcedState_getD _ _ _ shape.1 i within, reinforcedState_sum _ _ _ shape.1, shape.2] using next

/-- The same sufficient-count update at unit reinforcement. -/
theorem multicolourPolya_counts_updated (m n : Nat) (alphas counts : List Nat)
    (positive : 0 < alphas.sum) (supported : reinforcedCountsSupported m alphas 1 counts) :
    (reinforcedCountsContinuation m n alphas counts 1 positive
      (reinforcedCountsSupported_shape m alphas counts 1 supported).1 supported).SameLaw
      (multicolourPolyaDistro n (reinforcedState 1 alphas counts)
        (by rw [reinforcedState_sum _ _ _ (reinforcedCountsSupported_shape m alphas counts 1 supported).1]; omega)) := by
  simpa only [reinforcedUrn_one] using reinforcedCountsContinuation_updated m n alphas counts 1 positive
    (reinforcedCountsSupported_shape m alphas counts 1 supported).1 supported

end Thesis.Probability.Distros
