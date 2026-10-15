import Thesis.Probability.FourLabelTransportationReservation

namespace Thesis
namespace Probability
namespace FourLabelTransportation

/-!
# Multi-unit constructive transportation

The original `transport` remains a small reference constructor.  This module
uses its finite eligible-edge search but reserves the *entire* available
capacity, not one unit.  Each batch either exhausts a selected margin or
exhausts an untouched capacity slack.  Large natural denominators therefore
do not by themselves force one recursive call per unit of mass.

The recursion measure below is the remaining natural total.  The positive
batch lemma proves strict decrease; the reservation foundation proves all
remaining margins feasible and restores the original exact table afterward.
This is not a bounded-denominator search, and it changes neither feasibility
nor the possible extremal values.  No equality with the reference table is
claimed: several valid tables may have the same margins.

The zero branch calls only `transport 0`; the unit-recursive positive branch
is never invoked.  Extremal clients import this module and use this batched
constructor when completing their remaining reservations.
-/

/-- Eligibility gives one unit in *every* minimum constraint, including
the untouched-label cuts.  Thus a maximal reservation is genuinely positive;
positivity of just the selected row and column would not suffice. -/
theorem edgeCapacity_positive_of_eligible (total : Nat) (rows columns : Masses)
    (positive : 0 < total) (edge : Fin 4 × Fin 4)
    (eligible : Eligible total rows columns edge) :
    0 < edgeCapacity total rows columns edge := by
  have cutPositive : forall label, 1 ≤ cutCapacity total rows columns edge label := by
    intro label
    by_cases endpoint : label = edge.1 ∨ label = edge.2
    · simp only [cutCapacity, if_pos endpoint]
      exact positive
    · have awayRow : label ≠ edge.1 := fun same => endpoint (Or.inl same)
      have awayColumn : label ≠ edge.2 := fun same => endpoint (Or.inr same)
      have slack := eligible.2.2.2 label awayRow awayColumn
      simp only [cutCapacity, if_neg endpoint]
      omega
  exact Nat.le_min.mpr ⟨eligible.2.1,
    Nat.le_min.mpr ⟨eligible.2.2.1, le_minimum4 1 _ cutPositive⟩⟩

/-- A positive maximal batch strictly reduces the supplied total.  The
selected row bounds the batch by that total, so natural subtraction does
not silently discard any reserved mass. -/
theorem batch_remaining_total_lt (total : Nat) (rows columns : Masses)
    (margins : Margins total rows columns) (positive : 0 < total)
    (edge : Fin 4 × Fin 4) (eligible : Eligible total rows columns edge) :
    total - edgeCapacity total rows columns edge < total := by
  have batchPositive := edgeCapacity_positive_of_eligible total rows columns positive edge eligible
  have batchBound := Nat.le_trans (edgeCapacity_le_row total rows columns edge)
    (margins.rows_total ▸ le_sum4 rows edge.1)
  omega

private theorem minimum4_attained (masses : Masses) :
    ∃ label, minimum4 masses = masses label := by
  unfold minimum4
  by_cases first : masses 0 ≤ Nat.min (masses 1) (Nat.min (masses 2) (masses 3))
  · exact ⟨0, Nat.min_eq_left first⟩
  · rw [Nat.min_eq_right (by omega : Nat.min (masses 1) (Nat.min (masses 2) (masses 3)) ≤ masses 0)]
    by_cases second : masses 1 ≤ Nat.min (masses 2) (masses 3)
    · exact ⟨1, Nat.min_eq_left second⟩
    · rw [Nat.min_eq_right (by omega : Nat.min (masses 2) (masses 3) ≤ masses 1)]
      by_cases third : masses 2 ≤ masses 3
      · exact ⟨2, Nat.min_eq_left third⟩
      · exact ⟨3, Nat.min_eq_right (by omega)⟩

/-- Each maximal batch reaches a real boundary: a selected margin is
exhausted, or an untouched capacity becomes tight in the residual problem.
This is the reason batching is different from arbitrary positive stepping.
The witness is obtained by finite comparisons of supplied natural masses. -/
theorem edgeCapacity_saturates (total : Nat) (rows columns : Masses)
    (margins : Margins total rows columns) (edge : Fin 4 × Fin 4) :
    edgeCapacity total rows columns edge = rows edge.1 ∨
      edgeCapacity total rows columns edge = columns edge.2 ∨
      ∃ label, label ≠ edge.1 ∧ label ≠ edge.2 ∧
        edgeCapacity total rows columns edge + rows label + columns label = total := by
  by_cases rowMinimum : rows edge.1 ≤
      Nat.min (columns edge.2) (minimum4 (cutCapacity total rows columns edge))
  · exact Or.inl (Nat.min_eq_left rowMinimum)
  · have removeRow : edgeCapacity total rows columns edge =
        Nat.min (columns edge.2) (minimum4 (cutCapacity total rows columns edge)) :=
      Nat.min_eq_right (by omega)
    by_cases columnMinimum : columns edge.2 ≤ minimum4 (cutCapacity total rows columns edge)
    · exact Or.inr (Or.inl (removeRow.trans (Nat.min_eq_left columnMinimum)))
    · have removeColumn : edgeCapacity total rows columns edge = minimum4 (cutCapacity total rows columns edge) :=
        removeRow.trans (Nat.min_eq_right (by omega))
      obtain ⟨label, attained⟩ := minimum4_attained (cutCapacity total rows columns edge)
      have batchCut := removeColumn.trans attained
      by_cases endpoint : label = edge.1 ∨ label = edge.2
      · have rowBound := margins.rows_total ▸ le_sum4 rows edge.1
        have batchBound := edgeCapacity_le_row total rows columns edge
        simp only [cutCapacity, if_pos endpoint] at batchCut
        exact Or.inl (by omega)
      · have awayRow : label ≠ edge.1 := fun same => endpoint (Or.inl same)
        have awayColumn : label ≠ edge.2 := fun same => endpoint (Or.inr same)
        have capacity := margins.capacity label
        simp only [cutCapacity, if_neg endpoint] at batchCut
        exact Or.inr (Or.inr ⟨label, awayRow, awayColumn, by omega⟩)

/-- Construct the exact same *class* of diagonal-free tables as `transport`,
but fill an eligible cell by its full feasible capacity at each recursive
step.  The return type retains every row, column, and diagonal guarantee. -/
def transportBatched (total : Nat) (rows columns : Masses)
    (margins : Margins total rows columns) : Transportation rows columns :=
  if zero : total = 0 then
    transport 0 rows columns (zero ▸ margins)
  else
    let positive := Nat.pos_of_ne_zero zero
    let selected := nextStep total rows columns margins positive
    let amount := edgeCapacity total rows columns selected.val
    let reserved := edgeCapacity_reservation total rows columns margins selected.val selected.property.1
    let residual := transportBatched (total - amount)
      (reserveMasses rows selected.val.1 amount) (reserveMasses columns selected.val.2 amount)
      (reservation_margins total rows columns margins selected.val amount reserved)
    restoreReservation total rows columns selected.val amount reserved residual
termination_by total
decreasing_by
  exact batch_remaining_total_lt total rows columns margins positive selected.val selected.property

end FourLabelTransportation
end Probability
end Thesis
