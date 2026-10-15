import Thesis.Probability.Distros.ReinforcedUrn
import Thesis.Probability.Distros.CategoricalAggregation
namespace Thesis.Probability.Distros

/-- Grouping every draw of a reinforced urn gives the urn with summed
initial group weights and the same reinforcement increment. -/
theorem reinforcedUrn_aggregation (n groups : Nat) (alphas labels : List Nat) (increment : Nat)
    (positive : 0 < alphas.sum) (dimension : labels.length = alphas.length)
    (within : ∀ label ∈ labels, label < groups) :
    ((reinforcedUrnDistro n alphas increment positive).map (List.map (fun colour => labels.getD colour 0))).SameLaw
      (reinforcedUrnDistro n (aggregateCounts groups labels alphas) increment
        (by rw [aggregateCounts_sum groups labels alphas dimension within]; exact positive)) := by
  induction n generalizing alphas with
  | zero => intro event; exact QProb.equiv_refl _
  | succ n ih =>
      intro event
      let grouped := aggregateCounts groups labels alphas
      have groupPositive : 0 < grouped.sum := by
        rw [aggregateCounts_sum groups labels alphas dimension within]; exact positive
      let mappedWord := List.map (fun colour => labels.getD colour 0)
      let continuation (j : Nat) : QProb :=
        (reinforcedUrnDistro n (grouped.modify j (fun a => a + increment)) increment
          (Nat.lt_of_lt_of_le groupPositive (sum_modify_add_ge grouped j increment))).record.probVal
            (fun word => event (j :: word))
      have tails (i : Fin alphas.length) :
          QProb.Equiv
            ((reinforcedUrnDistro n (alphas.modify i.val (fun a => a + increment)) increment
              (by rw [sum_modify_add alphas i.val increment i.isLt]; omega)).record.probVal
                (fun word => event (mappedWord (i.val :: word))))
            (continuation (labels.getD i.val 0)) := by
        have hp : 0 < (alphas.modify i.val (fun a => a + increment)).sum := by
          rw [sum_modify_add alphas i.val increment i.isLt]; omega
        have tailLaw := ih (alphas.modify i.val (fun a => a + increment)) hp
          (by simpa only [List.length_modify] using dimension)
        simp only [aggregateCounts_modify groups labels alphas dimension i.val increment i.isLt] at tailLaw
        refine QProb.equiv_trans (QProb.equiv_symm
          ((reinforcedUrnDistro n (alphas.modify i.val (fun a => a + increment)) increment hp).map_probVal
            mappedWord (fun word => event (labels.getD i.val 0 :: word)))) ?_
        exact tailLaw (fun word => event (labels.getD i.val 0 :: word))
      refine QProb.equiv_trans
        ((reinforcedUrnDistro (n + 1) alphas increment positive).map_probVal mappedWord event) ?_
      refine QProb.equiv_trans (reinforcedUrn_first_step n alphas increment positive (fun word => event (mappedWord word))) ?_
      refine QProb.equiv_trans ((listCategoricalDistro alphas positive).expectation_congr _ _ tails) ?_
      have headLaw := categorical_aggregation groups alphas labels positive dimension within
      have transport := headLaw.expectation continuation
      simp only [Distro.expectation_map] at transport
      refine QProb.equiv_trans transport ?_
      exact QProb.equiv_symm (reinforcedUrn_first_step n grouped increment groupPositive event)

theorem reinforcedUrn_word_support (n : Nat) (alphas : List Nat) (increment : Nat) (atom : List Nat × Nat)
    (member : atom ∈ reinforcedUrnAtoms n alphas increment) :
    atom.1.length = n ∧ ∀ colour ∈ atom.1, colour < alphas.length := by
  induction n generalizing alphas atom with
  | zero =>
      simp only [reinforcedUrnAtoms, List.mem_singleton] at member
      cases member
      exact ⟨rfl, fun _ member => nomatch member⟩
  | succ n ih =>
      rcases List.mem_flatMap.mp member with ⟨head, _, tail⟩
      rcases List.mem_map.mp tail with ⟨rest, hr, eq⟩
      cases eq
      have support := ih (alphas.modify head.1.val (fun a => a + increment)) rest hr
      simp only [List.length_modify] at support
      refine ⟨by simp only [List.length_cons, support.1], fun colour member => ?_⟩
      rcases List.mem_cons.mp member with eq | member
      · subst colour; exact head.1.isLt
      · exact support.2 colour member

theorem aggregateCounts_zeros (groups : Nat) (labels : List Nat) :
    aggregateCounts groups labels (List.replicate labels.length 0) = List.replicate groups 0 := by
  induction labels with
  | nil => rfl
  | cons label labels ih => simp only [List.length_cons, List.replicate_succ, aggregateCounts, ih, modify_add_zero]

theorem aggregateCounts_colourCounts (groups colours : Nat) (labels word : List Nat)
    (dimension : labels.length = colours) (valid : ∀ colour ∈ word, colour < colours) :
    aggregateCounts groups labels (colourCounts colours word) =
      colourCounts groups (word.map (fun colour => labels.getD colour 0)) := by
  induction word with
  | nil => rw [colourCounts, ← dimension, aggregateCounts_zeros]; rfl
  | cons colour word ih =>
      simp only [colourCounts, List.map_cons]
      rw [aggregateCounts_modify groups labels _ (dimension.trans (colourCounts_length colours word).symm)
        colour 1 (by simpa only [colourCounts_length] using valid colour (List.mem_cons_self ..)),
        ih (fun i member => valid i (List.mem_cons_of_mem _ member))]

/-- Every category partition gives the reinforced count law with summed
initial weights, retaining the same increment and every event probability. -/
theorem reinforcedCount_aggregation (n groups : Nat) (alphas labels : List Nat) (increment : Nat)
    (positive : 0 < alphas.sum) (dimension : labels.length = alphas.length)
    (within : ∀ label ∈ labels, label < groups) :
    ((reinforcedCountDistro n alphas increment positive).map (aggregateCounts groups labels)).SameLaw
      (reinforcedCountDistro n (aggregateCounts groups labels alphas) increment
        (by rw [aggregateCounts_sum groups labels alphas dimension within]; exact positive)) := by
  let grouped := aggregateCounts groups labels alphas
  have groupPositive : 0 < grouped.sum := by
    rw [aggregateCounts_sum groups labels alphas dimension within]; exact positive
  have old := ((reinforcedUrn_count_correspondence n alphas increment positive).symm).map (aggregateCounts groups labels)
  rw [Distro.map_comp] at old
  have regroup := (reinforcedUrnDistro n alphas increment positive).sameLaw_maps_on_support
    (fun word => aggregateCounts groups labels (colourCounts alphas.length word))
    (fun word => colourCounts groups (word.map (fun colour => labels.getD colour 0)))
    (fun atom member => aggregateCounts_colourCounts groups alphas.length labels atom.1 dimension
      (reinforcedUrn_word_support n alphas increment atom member).2)
  have word := (reinforcedUrn_aggregation n groups alphas labels increment positive dimension within).map (colourCounts groups)
  rw [Distro.map_comp] at word
  have new := reinforcedUrn_count_correspondence n grouped increment groupPositive
  simp only [grouped, aggregateCounts_length] at new
  exact old.trans (regroup.trans (word.trans new))

/-- Dirichlet-multinomial coarsening sums all parameters in each group,
including zero weights and empty destination categories. -/
theorem dirichletMultinomial_aggregation (n groups : Nat) (alphas labels : List Nat)
    (positive : 0 < alphas.sum) (dimension : labels.length = alphas.length)
    (within : ∀ label ∈ labels, label < groups) :
    ((dirichletMultinomialDistro n alphas positive).map (aggregateCounts groups labels)).SameLaw
      (dirichletMultinomialDistro n (aggregateCounts groups labels alphas)
        (by rw [aggregateCounts_sum groups labels alphas dimension within]; exact positive)) := by
  simpa only [reinforcedCount_one] using reinforcedCount_aggregation n groups alphas labels 1 positive dimension within

theorem coordinateLabels_within (length index : Nat) :
    ∀ label ∈ coordinateArguments 0 length index, label < 2 := by
  induction length generalizing index with
  | zero => intro label member; cases member
  | succ length ih =>
      intro label member
      cases index with
      | zero =>
          simp only [coordinateArguments, List.mem_cons, List.mem_replicate] at member
          rcases member with eq | ⟨_, eq⟩ <;> omega
      | succ index =>
          rcases List.mem_cons.mp member with eq | member
          · omega
          · exact ih index label member

theorem aggregateCounts_all_complement (counts : List Nat) :
    aggregateCounts 2 (List.replicate counts.length 1) counts = [0, counts.sum] := by
  induction counts with
  | nil => rfl
  | cons count counts ih =>
      simp only [List.length_cons, List.replicate_succ, aggregateCounts, ih,
        List.modify_succ_cons, List.modify_zero_cons, List.sum_cons]
      congr 2 <;> omega

theorem aggregateCounts_coordinate (counts : List Nat) (index : Nat) (within : index < counts.length) :
    aggregateCounts 2 (coordinateArguments 0 counts.length index) counts =
      [counts.getD index 0, counts.sum - counts.getD index 0] := by
  induction counts generalizing index with
  | nil => simp only [List.length_nil] at within; omega
  | cons count counts ih => cases index with
      | zero =>
          simp only [coordinateArguments, aggregateCounts, aggregateCounts_all_complement,
            List.modify_zero_cons, List.getD_cons_zero, List.sum_cons, Nat.zero_add, Nat.add_sub_cancel_left]
      | succ index =>
          have bound : index < counts.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using within
          simp only [coordinateArguments, aggregateCounts, ih index bound, List.modify_succ_cons,
            List.modify_zero_cons, List.getD_cons_succ, List.sum_cons]
          have h := list_getD_le_sum counts index
          congr 2 <;> omega

/-- Every colour count has its beta-binomial marginal, including zero
selected weight and the deterministic one-colour case. -/
theorem dirichletMultinomial_coordinate_betaBinomial (n : Nat) (alphas : List Nat) (positive : 0 < alphas.sum)
    (index : Nat) (within : index < alphas.length) :
    (dirichletMultinomialCoordinate n alphas positive index).SameLaw
      (betaBinomialNatDistroOfTotal n (alphas.getD index 0) (alphas.sum - alphas.getD index 0)
        (by have h := list_getD_le_sum alphas index; omega)) := by
  let labels := coordinateArguments 0 alphas.length index
  have dimension : labels.length = alphas.length := coordinateArguments_length _ _ _
  have bounds : ∀ label ∈ labels, label < 2 := coordinateLabels_within alphas.length index
  have grouped := dirichletMultinomial_aggregation n 2 alphas labels positive dimension bounds
  have weights : aggregateCounts 2 labels alphas = [alphas.getD index 0, alphas.sum - alphas.getD index 0] :=
    aggregateCounts_coordinate alphas index within
  simp only [weights] at grouped
  apply (NatDistro.sameLaw_iff_events _ _).mpr
  intro event
  let μ := dirichletMultinomialDistro n alphas positive
  refine QProb.equiv_trans (μ.probVal_congr_on_support _
    (fun counts => event ((aggregateCounts 2 labels counts).getD 0 0)) ?_) ?_
  · intro atom member
    have support := dirichletMultinomial_support n alphas atom member
    change event (atom.1.getD index 0) = event ((aggregateCounts 2 labels atom.1).getD 0 0)
    have identity : aggregateCounts 2 labels atom.1 = [atom.1.getD index 0, atom.1.sum - atom.1.getD index 0] := by
      change aggregateCounts 2 (coordinateArguments 0 alphas.length index) atom.1 = _
      rw [← support.1, aggregateCounts_coordinate atom.1 index (by omega)]
    rw [identity]
    rfl
  · refine QProb.equiv_trans (QProb.equiv_symm (μ.map_probVal (aggregateCounts 2 labels)
      (fun counts => event (counts.getD 0 0)))) ?_
    refine QProb.equiv_trans (grouped (fun counts => event (counts.getD 0 0))) ?_
    exact (NatDistro.sameLaw_iff_events _ _).mp
      (dirichletMultinomial_two_coordinate n (alphas.getD index 0) (alphas.sum - alphas.getD index 0)
        (by have h := list_getD_le_sum alphas index; omega)) event

theorem dirichletMultinomial_coordinate_mean (n : Nat) (alphas : List Nat) (positive : 0 < alphas.sum)
    (index : Nat) (within : index < alphas.length) :
    QProb.Equiv (mean (dirichletMultinomialCoordinate n alphas positive index))
      ⟨n * alphas.getD index 0, alphas.sum, positive⟩ := by
  refine QProb.equiv_trans (dirichletMultinomial_coordinate_betaBinomial n alphas positive index within).mean ?_
  have beta := betaBinomialOfTotal_mean n (alphas.getD index 0) (alphas.sum - alphas.getD index 0)
    (by have h := list_getD_le_sum alphas index; omega)
  simpa only [Nat.add_sub_of_le (list_getD_le_sum alphas index)] using beta

theorem dirichletMultinomial_coordinate_variance (n : Nat) (alphas : List Nat) (positive : 0 < alphas.sum)
    (index : Nat) (within : index < alphas.length) :
    QProb.Equiv (variance (dirichletMultinomialCoordinate n alphas positive index))
      ⟨n * alphas.getD index 0 * (alphas.sum - alphas.getD index 0) * (alphas.sum + n),
        alphas.sum * alphas.sum * (alphas.sum + 1),
        Nat.mul_pos (Nat.mul_pos positive positive) (Nat.succ_pos _)⟩ := by
  refine QProb.equiv_trans (dirichletMultinomial_coordinate_betaBinomial n alphas positive index within).variance ?_
  have beta := betaBinomialOfTotal_variance n (alphas.getD index 0) (alphas.sum - alphas.getD index 0)
    (by have h := list_getD_le_sum alphas index; omega)
  simpa only [Nat.add_sub_of_le (list_getD_le_sum alphas index)] using beta

end Thesis.Probability.Distros
