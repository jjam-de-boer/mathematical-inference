import Thesis.Probability.Distros.ReinforcedConditioning
import Thesis.Probability.Distros.ReinforcedExchangeability
import Thesis.Probability.Distros.RationalPolya
import Thesis.Probability.FiniteRecordSupport
namespace Thesis.Probability.Distros
open Combinatorics

/-- Compatibility order of the witness fields. Positivity is proved once
for arbitrary finite records; this wrapper merely reorders its conjunction. -/
theorem eventMass_positive_witness (atoms : List (Ω × Nat)) (event : Event Ω)
    (positive : 0 < FiniteProbRecord.eventMass atoms event) :
    ∃ atom ∈ atoms, event atom.1 = true ∧ 0 < atom.2 := by
  rcases (FiniteProbRecord.eventMass_pos_iff_exists_atom atoms event).mp positive with
    ⟨atom, listed, weight, selected⟩
  exact ⟨atom, listed, selected, weight⟩

theorem reinforcedCountsSupported_shape (m : Nat) (alphas counts : List Nat) (increment : Nat)
    (supported : reinforcedCountsSupported m alphas increment counts) :
    counts.length = alphas.length ∧ counts.sum = m := by
  rcases (FiniteProbRecord.eventMass_pos_iff_exists_atom (reinforcedUrnAtoms m alphas increment)
    (fun word => decide (colourCounts alphas.length word = counts))).mp supported with ⟨atom, member, _, selected⟩
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
