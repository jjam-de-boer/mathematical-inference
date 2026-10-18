import Thesis.Probability.Distros.DepletingSupport
import Thesis.Probability.Distros.HypergeometricAggregation

namespace Thesis.Probability.Distros
open Combinatorics

private theorem modify_add_one_sub_one (values : List Nat) (index : Nat) :
    (values.modify index (fun x => x + 1)).modify index (fun x => x - 1) = values := by
  induction values generalizing index with
  | nil => rfl
  | cons value values ih => cases index with
      | zero => simp only [List.modify_zero_cons, Nat.add_sub_cancel]
      | succ index => simp only [List.modify_succ_cons, ih]

private theorem modify_sub_one_add_one (values : List Nat) (index : Nat)
    (within : index < values.length) (positive : 0 < values.getD index 0) :
    (values.modify index (fun x => x - 1)).modify index (fun x => x + 1) = values := by
  induction values generalizing index with
  | nil => simp only [List.length_nil] at within; omega
  | cons value values ih => cases index with
      | zero =>
          change (value - 1 + 1) :: values = value :: values
          have bound : 1 ≤ value := positive
          rw [Nat.sub_add_cancel bound]
      | succ index =>
          simp only [List.modify_succ_cons]
          rw [ih index (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using within) positive]

/-- Removing one genuinely available ball commutes with category merging.
No such assertion is needed for a zero-weight transition. -/
theorem aggregateCounts_remove_one (groups : Nat) (labels stocks : List Nat)
    (dimension : labels.length = stocks.length) (index : Nat) (within : index < stocks.length)
    (positive : 0 < stocks.getD index 0) :
    aggregateCounts groups labels (stocks.modify index (fun stock => stock - 1)) =
      (aggregateCounts groups labels stocks).modify (labels.getD index 0) (fun stock => stock - 1) := by
  have restored := modify_sub_one_add_one stocks index within positive
  have grouped := aggregateCounts_modify groups labels (stocks.modify index (fun stock => stock - 1))
    (by simpa only [List.length_modify] using dimension) index 1
    (by simpa only [List.length_modify] using within)
  rw [restored] at grouped
  rw [grouped, modify_add_one_sub_one]

private theorem finWeighted_member_weight (n : Nat) (w : Fin n → Nat) (atom : Fin n × Nat)
    (member : atom ∈ finWeighted n w) : atom.2 = w atom.1 := by
  induction n generalizing w atom with
  | zero => simp only [finWeighted, List.not_mem_nil] at member
  | succ n ih =>
      rw [finWeighted] at member
      rcases List.mem_append.mp member with prefix | last
      · rcases List.mem_map.mp prefix with ⟨old, listed, same⟩
        cases same
        exact ih (fun i => w i.castSucc) old listed
      · have same := List.mem_singleton.mp last
        cases same
        rfl

private theorem categorical_natIntegral_dot (weights args : List Nat) (dimension : args.length = weights.length) :
    natIntegral (finWeighted weights.length (fun i => weights.getD i.val 0))
      (fun i => args.getD i.val 0) = weightedNatArgument weights args := by
  rw [natIntegral_finWeighted]
  have same := natSum_congr (n := weights.length)
    (f := fun i => finWeight (fun j : Fin weights.length => weights.getD j.val 0) i * args.getD i 0)
    (g := fun i => weights.getD i 0 * args.getD i 0)
    (fun i within => by simp only [finWeight, dif_pos within])
  rw [same, weightedNatArgument_sum weights args dimension]

/-- Raw categorical integration coarsens even at total mass zero. -/
theorem categorical_natIntegral_aggregation (groups : Nat) (stocks labels : List Nat)
    (dimension : labels.length = stocks.length) (within : ∀ label ∈ labels, label < groups) (f : Nat → Nat) :
    natIntegral (finWeighted stocks.length (fun i => stocks.getD i.val 0))
      (fun i => f (labels.getD i.val 0)) =
    natIntegral (finWeighted (aggregateCounts groups labels stocks).length
      (fun j => (aggregateCounts groups labels stocks).getD j.val 0)) (fun j => f j.val) := by
  let args := natTabulate f groups
  have first : (fun i : Fin stocks.length => f (labels.getD i.val 0)) =
      (fun i => (labels.map f).getD i.val 0) := by
    funext i
    exact (getD_map_on_lt labels f i.val (by rw [dimension]; exact i.isLt)).symm
  have second : (fun j : Fin (aggregateCounts groups labels stocks).length => f j.val) =
      (fun j => args.getD j.val 0) := by
    funext j
    exact (natTabulate_getD f groups j.val (by simpa only [aggregateCounts_length] using j.isLt)).symm
  have selected : labels.map (fun label => args.getD label 0) = labels.map f := by
    apply List.map_congr_left
    intro label member
    exact natTabulate_getD f groups label (within label member)
  rw [first, second, categorical_natIntegral_dot _ _ (by rw [List.length_map, dimension]),
    categorical_natIntegral_dot _ _ (by rw [natTabulate_length, aggregateCounts_length]),
    weightedNatArgument_aggregate groups labels stocks args dimension (natTabulate_length f groups) within, selected]

/-- Every ordered-path event coarsens on the original raw weighted records.
The identity includes zero stocks and horizons above the population size. -/
theorem multicolourDepleting_eventMass_aggregation (n groups : Nat) (stocks labels : List Nat)
    (dimension : labels.length = stocks.length) (within : ∀ label ∈ labels, label < groups)
    (event : Event (List Nat)) :
    FiniteProbRecord.eventMass (multicolourDepletingAtoms n stocks)
      (fun word => event (word.map (fun colour => labels.getD colour 0))) =
    FiniteProbRecord.eventMass (multicolourDepletingAtoms n (aggregateCounts groups labels stocks)) event := by
  induction n generalizing stocks event with
  | zero => rfl
  | succ n ih =>
      let grouped := aggregateCounts groups labels stocks
      let continuation := fun j => FiniteProbRecord.eventMass
        (multicolourDepletingAtoms n (grouped.modify j (fun stock => stock - 1))) (fun word => event (j :: word))
      rw [multicolourDepletingAtoms, multicolourDepletingAtoms, eventMass_flatMap, eventMass_flatMap]
      have rows : (finWeighted stocks.length (fun i => stocks.getD i.val 0)).map
          (fun head => FiniteProbRecord.eventMass
            ((multicolourDepletingAtoms n (stocks.modify head.1.val (fun stock => stock - 1))).map
              (fun rest => (head.1.val :: rest.1, head.2 * rest.2)))
            (fun word => event (word.map (fun colour => labels.getD colour 0)))) =
          (finWeighted stocks.length (fun i => stocks.getD i.val 0)).map
            (fun head => head.2 * continuation (labels.getD head.1.val 0)) := by
        apply List.map_congr_left
        intro head member
        rw [FiniteProbRecord.eventMass_map_weight]
        have weight : head.2 = stocks.getD head.1.val 0 :=
          finWeighted_member_weight _ _ head member
        by_cases zero : head.2 = 0
        · simp only [zero, Nat.zero_mul]
        · have positive : 0 < stocks.getD head.1.val 0 := by rw [← weight]; omega
          have tail := ih (stocks.modify head.1.val (fun stock => stock - 1))
            (by simpa only [List.length_modify] using dimension)
            (fun word => event (labels.getD head.1.val 0 :: word))
          rw [aggregateCounts_remove_one groups labels stocks dimension head.1.val head.1.isLt positive] at tail
          simpa only [List.map_cons, continuation, grouped] using congrArg (fun mass => head.2 * mass) tail
      rw [rows, ← natIntegral_eq_sum]
      rw [categorical_natIntegral_aggregation groups stocks labels dimension within continuation]
      rw [natIntegral_eq_sum]
      apply congrArg List.sum
      apply List.map_congr_left
      intro head _
      rw [FiniteProbRecord.eventMass_map_weight]
      rfl

/-- Merging every draw gives the complete removal-path law with summed
stocks, retaining empty destination groups and zero-stock categories. -/
theorem multicolourDepleting_aggregation (n groups : Nat) (stocks labels : List Nat)
    (available : n ≤ stocks.sum) (dimension : labels.length = stocks.length)
    (within : ∀ label ∈ labels, label < groups) :
    ((multicolourDepletingDistro n stocks available).map (List.map (fun colour => labels.getD colour 0))).SameLaw
      (multicolourDepletingDistro n (aggregateCounts groups labels stocks)
        (by rw [aggregateCounts_sum groups labels stocks dimension within]; exact available)) := by
  intro event
  change FiniteProbRecord.eventMass
      ((multicolourDepletingAtoms n stocks).map (fun atom => (atom.1.map (fun colour => labels.getD colour 0), atom.2))) event *
      (multicolourDepletingDistro n (aggregateCounts groups labels stocks) _).record.den =
    FiniteProbRecord.eventMass (multicolourDepletingAtoms n (aggregateCounts groups labels stocks)) event *
      (multicolourDepletingDistro n stocks available).record.den
  rw [FiniteProbRecord.eventMass_map_labels, multicolourDepleting_den, multicolourDepleting_den,
    multicolourDepleting_eventMass_aggregation n groups stocks labels dimension within event,
    aggregateCounts_sum groups labels stocks dimension within]

end Thesis.Probability.Distros
