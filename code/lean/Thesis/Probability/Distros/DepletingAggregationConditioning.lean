import Thesis.Probability.Distros.DepletingAggregation
import Thesis.Probability.FiniteRecordSupport

namespace Thesis.Probability.Distros

/-- Every positive ordered history leaves the same grouped stocks whether
its removals are performed before or after merging categories. -/
theorem aggregateCounts_depletingUpdate (groups : Nat) (labels stocks history : List Nat)
    (dimension : labels.length = stocks.length)
    (valid : ∀ colour ∈ history, colour < stocks.length)
    (positive : 0 < depletingWordWeight stocks history) :
    aggregateCounts groups labels (depletingUpdate stocks history) =
      depletingUpdate (aggregateCounts groups labels stocks) (history.map (fun colour => labels.getD colour 0)) := by
  induction history generalizing stocks with
  | nil => rfl
  | cons colour history ih =>
      change 0 < stocks.getD colour 0 *
        depletingWordWeight (stocks.modify colour (fun stock => stock - 1)) history at positive
      have head : 0 < stocks.getD colour 0 := Nat.pos_of_mul_pos_right positive
      have tail : 0 < depletingWordWeight (stocks.modify colour (fun stock => stock - 1)) history :=
        Nat.pos_of_mul_pos_left positive
      change aggregateCounts groups labels
          (depletingUpdate (stocks.modify colour (fun stock => stock - 1)) history) = _
      rw [ih (stocks.modify colour (fun stock => stock - 1))
        (by simpa only [List.length_modify] using dimension)
        (fun other member => by simpa only [List.length_modify] using valid other (List.mem_cons_of_mem _ member)) tail]
      rw [aggregateCounts_remove_one groups labels stocks dimension colour (valid colour (List.mem_cons_self ..)) head]
      rfl

/-- Feasible observed counts make remaining-stock subtraction commute with
category merging. Feasibility prevents subtraction from discarding overdraws. -/
theorem aggregateCounts_depletingState_supported (m groups : Nat) (stocks labels counts : List Nat)
    (dimension : labels.length = stocks.length) (supported : depletingCountsSupported m stocks counts) :
    aggregateCounts groups labels (depletingState stocks counts) =
      depletingState (aggregateCounts groups labels stocks) (aggregateCounts groups labels counts) := by
  rcases (FiniteProbRecord.eventMass_pos_iff_exists_atom (multicolourDepletingAtoms m stocks)
    (fun word => decide (colourCounts stocks.length word = counts))).mp supported with ⟨atom, member, weight, selected⟩
  have observed : colourCounts stocks.length atom.1 = counts := of_decide_eq_true selected
  have valid := (multicolourDepletingAtoms_support m stocks atom member).2
  have wordPositive : 0 < depletingWordWeight stocks atom.1 := by
    rw [depletingWordWeight_kernel stocks atom.1 valid]
    exact multicolourDepletingAtoms_kernel_positive m stocks atom member weight
  have regroup := aggregateCounts_depletingUpdate groups labels stocks atom.1 dimension valid wordPositive
  have coarseCounts := aggregateCounts_colourCounts groups stocks.length labels atom.1 dimension valid
  rw [observed] at coarseCounts
  rw [depletingUpdate_counts stocks atom.1, observed,
    depletingUpdate_counts (aggregateCounts groups labels stocks) (atom.1.map (fun colour => labels.getD colour 0)),
    aggregateCounts_length, ← coarseCounts] at regroup
  exact regroup

/-- Positive fine-count evidence gives positive evidence for its grouped
counts, including empty destination groups and zero-stock categories. -/
theorem depletingCountsSupported_aggregation (m groups : Nat) (stocks labels counts : List Nat)
    (dimension : labels.length = stocks.length) (within : ∀ label ∈ labels, label < groups)
    (supported : depletingCountsSupported m stocks counts) :
    depletingCountsSupported m (aggregateCounts groups labels stocks) (aggregateCounts groups labels counts) := by
  rcases (FiniteProbRecord.eventMass_pos_iff_exists_atom (multicolourDepletingAtoms m stocks)
    (fun word => decide (colourCounts stocks.length word = counts))).mp supported with ⟨atom, member, weight, selected⟩
  have observed : colourCounts stocks.length atom.1 = counts := of_decide_eq_true selected
  have valid := (multicolourDepletingAtoms_support m stocks atom member).2
  have accepted : colourCounts groups (atom.1.map (fun colour => labels.getD colour 0)) =
      aggregateCounts groups labels counts := by
    rw [← aggregateCounts_colourCounts groups stocks.length labels atom.1 dimension valid, observed]
  have positive : 0 < FiniteProbRecord.eventMass (multicolourDepletingAtoms m stocks)
      (fun word => decide (colourCounts groups (word.map (fun colour => labels.getD colour 0)) =
        aggregateCounts groups labels counts)) :=
    (FiniteProbRecord.eventMass_pos_iff_exists_atom _ _).mpr ⟨atom, member, weight, decide_eq_true accepted⟩
  have regroup := multicolourDepleting_eventMass_aggregation m groups stocks labels dimension within
    (fun word => decide (colourCounts groups word = aggregateCounts groups labels counts))
  change 0 < FiniteProbRecord.eventMass (multicolourDepletingAtoms m (aggregateCounts groups labels stocks))
    (fun word => decide (colourCounts (aggregateCounts groups labels stocks).length word = aggregateCounts groups labels counts))
  rw [aggregateCounts_length, ← regroup]
  exact positive

/-- The actual count-conditioned future path law commutes with category
merging: observing fine counts and then merging future draws gives exactly
the future law conditioned on the corresponding grouped counts. -/
theorem depletingCountsContinuation_aggregation (m n groups : Nat) (stocks labels counts : List Nat)
    (available : m + n ≤ stocks.sum) (dimension : labels.length = stocks.length)
    (within : ∀ label ∈ labels, label < groups) (supported : depletingCountsSupported m stocks counts) :
    ((depletingCountsContinuation m n stocks counts available supported).map
      (List.map (fun colour => labels.getD colour 0))).SameLaw
      (depletingCountsContinuation m n (aggregateCounts groups labels stocks) (aggregateCounts groups labels counts)
        (by rw [aggregateCounts_sum groups labels stocks dimension within]; exact available)
        (depletingCountsSupported_aggregation m groups stocks labels counts dimension within supported)) := by
  have fine := (depletingCountsContinuation_updated m n stocks counts available supported).map
    (List.map (fun colour => labels.getD colour 0))
  have future := multicolourDepleting_aggregation n groups (depletingState stocks counts) labels
    (depletingCounts_remaining m n stocks counts available supported)
    (by rw [depletingState_length]; exact dimension) within
  have merged := fine.trans future
  have coarse := depletingCountsContinuation_updated m n
    (aggregateCounts groups labels stocks) (aggregateCounts groups labels counts)
    (by rw [aggregateCounts_sum groups labels stocks dimension within]; exact available)
    (depletingCountsSupported_aggregation m groups stocks labels counts dimension within supported)
  have state := aggregateCounts_depletingState_supported m groups stocks labels counts dimension supported
  apply merged.trans
  simpa only [← state] using coarse.symm

end Thesis.Probability.Distros
