import Thesis.Probability.FourLabelTransportation

namespace Thesis
namespace Probability
namespace FourLabelTransportation

/-!
# Capacity bounds and reusable multi-unit reservations

An off-diagonal cell is bounded by its whole row, its whole column, and
the spare capacity of each untouched label.  The minimum of those bounds
is exact: reserve that many units in the cell, construct a feasible table
for the remaining margins, then restore the reserved mass.  The universal
bound ensures that the completed table cannot add extra mass to that cell.

All operations act on supplied natural masses.  Zero maxima and zero
remaining totals are allowed; no positive-cell division or search over
bounded rational denominators is involved.  A reservation is checked
against the true remaining capacities, not just row and column availability.

Restoring a reservation returns an actual table with the original margins.
This foundation does not choose a residual-table algorithm: both the batched
constructor and the extremal constructors reuse these same guarantees.
Single-cell and simultaneous maxima are assembled in the importing modules.
-/

def minimum4 (masses : Masses) : Nat :=
  Nat.min (masses 0) (Nat.min (masses 1) (Nat.min (masses 2) (masses 3)))

theorem minimum4_le (masses : Masses) (label : Fin 4) : minimum4 masses ≤ masses label := by
  rcases label_cases label with same | same | same | same <;> subst label
  · exact Nat.min_le_left _ _
  · exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
  · exact Nat.le_trans (Nat.min_le_right _ _) (Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _))
  · exact Nat.le_trans (Nat.min_le_right _ _) (Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _))

theorem le_minimum4 (bound : Nat) (masses : Masses) (bounded : forall label, bound ≤ masses label) :
    bound ≤ minimum4 masses :=
  Nat.le_min.mpr ⟨bounded 0, Nat.le_min.mpr ⟨bounded 1, Nat.le_min.mpr ⟨bounded 2, bounded 3⟩⟩⟩

/-- Endpoint labels impose no extra cut: their own row or column loses
the reserved amount.  Every other label must have that amount of spare mass. -/
def cutCapacity (total : Nat) (rows columns : Masses) (edge : Fin 4 × Fin 4) : Masses :=
  fun label => if label = edge.1 ∨ label = edge.2 then total else total - (rows label + columns label)

def edgeCapacity (total : Nat) (rows columns : Masses) (edge : Fin 4 × Fin 4) : Nat :=
  Nat.min (rows edge.1) (Nat.min (columns edge.2) (minimum4 (cutCapacity total rows columns edge)))

theorem edgeCapacity_le_row (total : Nat) (rows columns : Masses) (edge : Fin 4 × Fin 4) :
    edgeCapacity total rows columns edge ≤ rows edge.1 := Nat.min_le_left _ _

theorem edgeCapacity_le_column (total : Nat) (rows columns : Masses) (edge : Fin 4 × Fin 4) :
    edgeCapacity total rows columns edge ≤ columns edge.2 :=
  Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)

theorem edgeCapacity_le_cut (total : Nat) (rows columns : Masses) (edge : Fin 4 × Fin 4) (label : Fin 4) :
    edgeCapacity total rows columns edge ≤ cutCapacity total rows columns edge label :=
  Nat.le_trans (Nat.min_le_right _ _)
    (Nat.le_trans (Nat.min_le_right _ _) (minimum4_le _ label))

theorem cell_le_row (rows columns : Masses) (table : Transportation rows columns) (row column : Fin 4) :
    table.cells row column ≤ rows row := by
  have bounded := le_sum4 (table.cells row) column
  rw [table.row_sum] at bounded
  exact bounded

theorem cell_le_column (rows columns : Masses) (table : Transportation rows columns) (row column : Fin 4) :
    table.cells row column ≤ columns column := by
  have bounded := le_sum4 (fun index => table.cells index column) row
  rw [table.column_sum] at bounded
  exact bounded

/-- The untouched row, untouched column, and selected cell are disjoint.
Explicit finite cases expose only their natural mass sums; the proof never
enumerates a table's potentially large denominator or positive atoms. -/
theorem cell_cut_bound (total : Nat) (rows columns : Masses)
    (rowsTotal : sum4 rows = total) (table : Transportation rows columns)
    (row column label : Fin 4) (different : row ≠ column)
    (awayRow : label ≠ row) (awayColumn : label ≠ column) :
    rows label + columns label + table.cells row column ≤ total := by
  have row0 := table.row_sum 0
  have row1 := table.row_sum 1
  have row2 := table.row_sum 2
  have row3 := table.row_sum 3
  have column0 := table.column_sum 0
  have column1 := table.column_sum 1
  have column2 := table.column_sum 2
  have column3 := table.column_sum 3
  have diagonal0 := table.diagonal_zero 0
  have diagonal1 := table.diagonal_zero 1
  have diagonal2 := table.diagonal_zero 2
  have diagonal3 := table.diagonal_zero 3
  simp only [sum4] at rowsTotal row0 row1 row2 row3 column0 column1 column2 column3
  rcases label_cases row with same | same | same | same <;> subst row <;>
    rcases label_cases column with same | same | same | same <;> subst column <;>
    rcases label_cases label with same | same | same | same <;> subst label
  all_goals first
    | exact False.elim (different rfl)
    | exact False.elim (awayRow rfl)
    | exact False.elim (awayColumn rfl)
    | omega

/-- Every table, not just the table later constructed for sharpness, obeys
the full minimum bound including both untouched-label cuts. -/
theorem cell_le_edgeCapacity (total : Nat) (rows columns : Masses)
    (margins : Margins total rows columns) (table : Transportation rows columns)
    (edge : Fin 4 × Fin 4) (different : edge.1 ≠ edge.2) :
    table.cells edge.1 edge.2 ≤ edgeCapacity total rows columns edge := by
  apply Nat.le_min.mpr
  refine ⟨cell_le_row rows columns table _ _, Nat.le_min.mpr ⟨cell_le_column rows columns table _ _, ?_⟩⟩
  apply le_minimum4
  intro label
  by_cases endpoint : label = edge.1 ∨ label = edge.2
  · simp only [cutCapacity, if_pos endpoint]
    exact Nat.le_trans (cell_le_row rows columns table _ _)
      (margins.rows_total ▸ le_sum4 rows edge.1)
  · have awayRow : label ≠ edge.1 := fun same => endpoint (Or.inl same)
    have awayColumn : label ≠ edge.2 := fun same => endpoint (Or.inr same)
    have cut := cell_cut_bound total rows columns margins.rows_total table _ _ label different awayRow awayColumn
    simp only [cutCapacity, if_neg endpoint]
    omega

/-- A reservation carries every load-bearing remaining-capacity condition.
In particular, available row and column mass alone would be insufficient. -/
structure Reservation (total : Nat) (rows columns : Masses) (edge : Fin 4 × Fin 4) (amount : Nat) : Prop where
  different : edge.1 ≠ edge.2
  row_mass : amount ≤ rows edge.1
  column_mass : amount ≤ columns edge.2
  untouched : forall label, label ≠ edge.1 → label ≠ edge.2 → amount + rows label + columns label ≤ total

theorem edgeCapacity_reservation (total : Nat) (rows columns : Masses)
    (margins : Margins total rows columns) (edge : Fin 4 × Fin 4) (different : edge.1 ≠ edge.2) :
    Reservation total rows columns edge (edgeCapacity total rows columns edge) := by
  refine ⟨different, edgeCapacity_le_row total rows columns edge,
    edgeCapacity_le_column total rows columns edge, ?_⟩
  intro label awayRow awayColumn
  have endpoint : ¬ (label = edge.1 ∨ label = edge.2) := fun same => same.elim awayRow awayColumn
  have cut := edgeCapacity_le_cut total rows columns edge label
  have capacity := margins.capacity label
  simp only [cutCapacity, if_neg endpoint] at cut
  omega

def reserveMasses (masses : Masses) (selected : Fin 4) (amount : Nat) : Masses :=
  fun label => if label = selected then masses label - amount else masses label

theorem reserveMasses_recover (masses : Masses) (selected : Fin 4) (amount : Nat)
    (bounded : amount ≤ masses selected) (label : Fin 4) :
    reserveMasses masses selected amount label + (if label = selected then amount else 0) = masses label := by
  by_cases same : label = selected
  · subst label
    simp only [reserveMasses]
    exact Nat.sub_add_cancel bounded
  · simp only [reserveMasses, if_neg same, Nat.add_zero]

private theorem sum4_massAt (selected : Fin 4) (amount : Nat) :
    sum4 (fun label => if label = selected then amount else 0) = amount := by
  rcases label_cases selected with same | same | same | same <;> subst selected <;> simp [sum4]

theorem sum4_addMassAt (masses : Masses) (selected : Fin 4) (amount : Nat) :
    sum4 (fun label => masses label + (if label = selected then amount else 0)) = sum4 masses + amount := by
  rw [sum4_add, sum4_massAt]

theorem sum4_reserveMasses (masses : Masses) (selected : Fin 4) (amount : Nat)
    (bounded : amount ≤ masses selected) :
    sum4 (reserveMasses masses selected amount) + amount = sum4 masses := by
  rw [← sum4_addMassAt]
  exact sum4_congr _ _ (reserveMasses_recover masses selected amount bounded)

/-- Reserving the complete capacity leaves normalized feasible margins,
including when the reserved amount or the remaining total is zero. -/
theorem reservation_margins (total : Nat) (rows columns : Masses)
    (margins : Margins total rows columns) (edge : Fin 4 × Fin 4) (amount : Nat)
    (reserved : Reservation total rows columns edge amount) :
    Margins (total - amount) (reserveMasses rows edge.1 amount) (reserveMasses columns edge.2 amount) := by
  refine ⟨?_, ?_, ?_⟩
  · have recovered := sum4_reserveMasses rows edge.1 amount reserved.row_mass
    rw [margins.rows_total] at recovered
    omega
  · have recovered := sum4_reserveMasses columns edge.2 amount reserved.column_mass
    rw [margins.columns_total] at recovered
    omega
  · intro label
    have capacity := margins.capacity label
    by_cases atRow : label = edge.1
    · have awayColumn : label ≠ edge.2 := fun same => reserved.different (atRow.symm.trans same)
      have rowBound : amount ≤ rows label := atRow.symm ▸ reserved.row_mass
      simp only [reserveMasses, if_pos atRow, if_neg awayColumn]
      omega
    · by_cases atColumn : label = edge.2
      · have columnBound : amount ≤ columns label := atColumn.symm ▸ reserved.column_mass
        simp only [reserveMasses, if_neg atRow, if_pos atColumn]
        omega
      · have cut := reserved.untouched label atRow atColumn
        simp only [reserveMasses, if_neg atRow, if_neg atColumn]
        omega

def addMassEdge (cells : Cells) (edge : Fin 4 × Fin 4) (amount : Nat) : Cells :=
  fun row column => cells row column + (if row = edge.1 then (if column = edge.2 then amount else 0) else 0)

theorem addMassEdge_row_sum (cells : Cells) (edge : Fin 4 × Fin 4) (amount : Nat) (row : Fin 4) :
    sum4 (addMassEdge cells edge amount row) = sum4 (cells row) + (if row = edge.1 then amount else 0) := by
  change sum4 (fun column => cells row column +
    (if row = edge.1 then (if column = edge.2 then amount else 0) else 0)) = _
  by_cases same : row = edge.1
  · simp only [if_pos same]
    exact sum4_addMassAt (cells row) edge.2 amount
  · simp only [if_neg same, Nat.add_zero]

theorem addMassEdge_column_sum (cells : Cells) (edge : Fin 4 × Fin 4) (amount : Nat) (column : Fin 4) :
    sum4 (fun row => addMassEdge cells edge amount row column) =
      sum4 (fun row => cells row column) + (if column = edge.2 then amount else 0) := by
  by_cases same : column = edge.2
  · simp only [addMassEdge, if_pos same]
    exact sum4_addMassAt (fun row => cells row column) edge.1 amount
  · have unchanged : forall row, addMassEdge cells edge amount row column = cells row column := by
      intro row
      simp only [addMassEdge, if_neg same, ite_self, Nat.add_zero]
    simp only [if_neg same, Nat.add_zero]
    exact sum4_congr _ _ unchanged

/-- Restore reserved mass to any supplied remaining table.  Keeping this
operation separate from `transport` lets later joint optimizers constrain
the remaining table before restoring the original margins. -/
def restoreReservation (total : Nat) (rows columns : Masses) (edge : Fin 4 × Fin 4) (amount : Nat)
    (reserved : Reservation total rows columns edge amount)
    (residual : Transportation (reserveMasses rows edge.1 amount) (reserveMasses columns edge.2 amount)) :
    Transportation rows columns :=
  { cells := addMassEdge residual.cells edge amount
    row_sum := by
      intro row
      rw [addMassEdge_row_sum, residual.row_sum]
      exact reserveMasses_recover rows edge.1 amount reserved.row_mass row
    column_sum := by
      intro column
      rw [addMassEdge_column_sum, residual.column_sum]
      exact reserveMasses_recover columns edge.2 amount reserved.column_mass column
    diagonal_zero := by
      intro label
      by_cases atRow : label = edge.1
      · have awayColumn : label ≠ edge.2 := fun same => reserved.different (atRow.symm.trans same)
        simp only [addMassEdge, residual.diagonal_zero, if_pos atRow, if_neg awayColumn, Nat.add_zero]
      · simp only [addMassEdge, residual.diagonal_zero, if_neg atRow, Nat.add_zero] }

theorem restoreReservation_selected_ge (total : Nat) (rows columns : Masses)
    (edge : Fin 4 × Fin 4) (amount : Nat) (reserved : Reservation total rows columns edge amount)
    (residual : Transportation (reserveMasses rows edge.1 amount) (reserveMasses columns edge.2 amount)) :
    amount ≤ (restoreReservation total rows columns edge amount reserved residual).cells edge.1 edge.2 := by
  change amount ≤ residual.cells edge.1 edge.2 +
    (if edge.1 = edge.1 then (if edge.2 = edge.2 then amount else 0) else 0)
  simp only
  exact Nat.le_add_left _ _

theorem restoreReservation_unchanged_row (total : Nat) (rows columns : Masses)
    (edge : Fin 4 × Fin 4) (amount : Nat) (reserved : Reservation total rows columns edge amount)
    (residual : Transportation (reserveMasses rows edge.1 amount) (reserveMasses columns edge.2 amount))
    (row column : Fin 4) (away : row ≠ edge.1) :
    (restoreReservation total rows columns edge amount reserved residual).cells row column = residual.cells row column := by
  simp only [restoreReservation, addMassEdge, if_neg away, Nat.add_zero]

end FourLabelTransportation
end Probability
end Thesis
