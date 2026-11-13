import Thesis.Probability.FourLabelTransportationExtrema

namespace Thesis
namespace Probability
namespace FourLabelTransportation

/-!
# Simultaneous sharp maxima at complementary off-diagonal cells

Independently sharp cell bounds need not be jointly attainable in an arbitrary
transportation problem.  Here the two selected edges have distinct rows,
distinct columns, and together cover the four labels.  This is the precise
finite compatibility needed for the opposing treatment-risk endpoints in
the binary-IV problem after its forbidden cells are relabelled to a diagonal.

Reserve the first edge's complete sharp capacity.  The second reservation
survives unchanged: its row and column are untouched, and each capacity
outside its endpoints belongs to a first-edge endpoint.  The first reserved
mass is subtracted from both that capacity's sum and the total.  An actual
remaining table can therefore be completed and both reservations restored.

The two universal single-cell bounds then show equality at both maxima in
that *same* completed table.  No second independent optimizer output, real
polytope theorem, selected model-class assumption, or choice principle is
used.  Zero capacities and a zero remaining total are retained throughout.
-/

/-- Explicit finite compatibility of the two selected edges.  The IV
applications use `(0,1),(3,2)` and `(1,0),(2,3)` and check this data directly. -/
structure ComplementaryEdges (first second : Fin 4 × Fin 4) : Prop where
  rows_different : first.1 ≠ second.1
  columns_different : first.2 ≠ second.2
  cover : forall label, label = first.1 ∨ label = first.2 ∨ label = second.1 ∨ label = second.2

/-- Reserving the first edge does not reduce the allowable second amount.
The cover condition is load-bearing: otherwise a capacity outside *both*
edges would lose total mass without losing either of its margins. -/
theorem reservation_after_complementary (total : Nat) (rows columns : Masses)
    (first second : Fin 4 × Fin 4) (firstAmount secondAmount : Nat)
    (complementary : ComplementaryEdges first second)
    (firstReserved : Reservation total rows columns first firstAmount)
    (secondReserved : Reservation total rows columns second secondAmount) :
    Reservation (total - firstAmount)
      (reserveMasses rows first.1 firstAmount) (reserveMasses columns first.2 firstAmount)
      second secondAmount := by
  refine ⟨secondReserved.different, ?_, ?_, ?_⟩
  · have away : second.1 ≠ first.1 := fun same => complementary.rows_different same.symm
    simp only [reserveMasses, if_neg away]
    exact secondReserved.row_mass
  · have away : second.2 ≠ first.2 := fun same => complementary.columns_different same.symm
    simp only [reserveMasses, if_neg away]
    exact secondReserved.column_mass
  · intro label awayRow awayColumn
    have bounded := secondReserved.untouched label awayRow awayColumn
    rcases complementary.cover label with atFirstRow | atFirstColumn | atSecondRow | atSecondColumn
    · have awayFirstColumn : label ≠ first.2 := fun same => firstReserved.different (atFirstRow.symm.trans same)
      have available : firstAmount ≤ rows label := atFirstRow.symm ▸ firstReserved.row_mass
      simp only [reserveMasses, if_pos atFirstRow, if_neg awayFirstColumn]
      omega
    · have awayFirstRow : label ≠ first.1 := fun same => firstReserved.different (same.symm.trans atFirstColumn)
      have available : firstAmount ≤ columns label := atFirstColumn.symm ▸ firstReserved.column_mass
      simp only [reserveMasses, if_neg awayFirstRow, if_pos atFirstColumn]
      omega
    · exact False.elim (awayRow atSecondRow)
    · exact False.elim (awayColumn atSecondColumn)

/-- One explicit table maximizing both complementary cells.  Only the
remaining unconstrained mass is filled by the base transport constructor. -/
def maximizeComplementary (total : Nat) (rows columns : Masses) (margins : Margins total rows columns)
    (first second : Fin 4 × Fin 4) (firstDifferent : first.1 ≠ first.2) (secondDifferent : second.1 ≠ second.2)
    (complementary : ComplementaryEdges first second) : Transportation rows columns :=
  let firstAmount := edgeCapacity total rows columns first
  let secondAmount := edgeCapacity total rows columns second
  let firstReserved := edgeCapacity_reservation total rows columns margins first firstDifferent
  let secondReserved := edgeCapacity_reservation total rows columns margins second secondDifferent
  let remaining := reservation_margins total rows columns margins first firstAmount firstReserved
  let secondAfter := reservation_after_complementary total rows columns first second firstAmount secondAmount
    complementary firstReserved secondReserved
  let restoredSecond := completeReservation (total - firstAmount)
    (reserveMasses rows first.1 firstAmount) (reserveMasses columns first.2 firstAmount)
    remaining second secondAmount secondAfter
  restoreReservation total rows columns first firstAmount firstReserved restoredSecond

/-- The *same* table attains both universal maxima.  This statement is
stronger than two separate existential sharpness witnesses and is what
permits sharp opposing-risk differences for the average treatment effect. -/
theorem maximizeComplementary_attains (total : Nat) (rows columns : Masses) (margins : Margins total rows columns)
    (first second : Fin 4 × Fin 4) (firstDifferent : first.1 ≠ first.2) (secondDifferent : second.1 ≠ second.2)
    (complementary : ComplementaryEdges first second) :
    (maximizeComplementary total rows columns margins first second firstDifferent secondDifferent complementary).cells first.1 first.2 =
        edgeCapacity total rows columns first ∧
      (maximizeComplementary total rows columns margins first second firstDifferent secondDifferent complementary).cells second.1 second.2 =
        edgeCapacity total rows columns second := by
  let table := maximizeComplementary total rows columns margins first second firstDifferent secondDifferent complementary
  let firstAmount := edgeCapacity total rows columns first
  let secondAmount := edgeCapacity total rows columns second
  let firstReserved := edgeCapacity_reservation total rows columns margins first firstDifferent
  let secondReserved := edgeCapacity_reservation total rows columns margins second secondDifferent
  let remaining := reservation_margins total rows columns margins first firstAmount firstReserved
  let secondAfter := reservation_after_complementary total rows columns first second firstAmount secondAmount
    complementary firstReserved secondReserved
  let restoredSecond := completeReservation (total - firstAmount)
    (reserveMasses rows first.1 firstAmount) (reserveMasses columns first.2 firstAmount)
    remaining second secondAmount secondAfter
  have firstLower : edgeCapacity total rows columns first ≤ table.cells first.1 first.2 :=
    restoreReservation_selected_ge total rows columns first firstAmount firstReserved restoredSecond
  have secondLower : edgeCapacity total rows columns second ≤ table.cells second.1 second.2 := by
    have away : second.1 ≠ first.1 := fun same => complementary.rows_different same.symm
    change secondAmount ≤
      (restoreReservation total rows columns first firstAmount firstReserved restoredSecond).cells second.1 second.2
    rw [restoreReservation_unchanged_row total rows columns first firstAmount firstReserved restoredSecond second.1 second.2 away]
    exact completeReservation_selected_ge (total - firstAmount)
      (reserveMasses rows first.1 firstAmount) (reserveMasses columns first.2 firstAmount)
      remaining second secondAmount secondAfter
  exact ⟨Nat.le_antisymm (cell_le_edgeCapacity total rows columns margins table first firstDifferent) firstLower,
    Nat.le_antisymm (cell_le_edgeCapacity total rows columns margins table second secondDifferent) secondLower⟩

/-- Consequently the same explicit table maximizes their sum throughout
the whole transportation class.  This is the linear objective used by the
opposing signed-effect endpoints, not a bound obtained from unrelated models. -/
theorem maximizeComplementary_sum (total : Nat) (rows columns : Masses) (margins : Margins total rows columns)
    (first second : Fin 4 × Fin 4) (firstDifferent : first.1 ≠ first.2) (secondDifferent : second.1 ≠ second.2)
    (complementary : ComplementaryEdges first second) (other : Transportation rows columns) :
    other.cells first.1 first.2 + other.cells second.1 second.2 ≤
      (maximizeComplementary total rows columns margins first second firstDifferent secondDifferent complementary).cells first.1 first.2 +
        (maximizeComplementary total rows columns margins first second firstDifferent secondDifferent complementary).cells second.1 second.2 := by
  have attained := maximizeComplementary_attains total rows columns margins first second firstDifferent secondDifferent complementary
  rw [attained.1, attained.2]
  exact Nat.add_le_add (cell_le_edgeCapacity total rows columns margins other first firstDifferent)
    (cell_le_edgeCapacity total rows columns margins other second secondDifferent)

end FourLabelTransportation
end Probability
end Thesis
