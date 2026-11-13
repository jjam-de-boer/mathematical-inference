import Thesis.Probability.FourLabelTransportationJointExtrema
import Thesis.Probability.FiniteRecord

namespace Thesis
namespace Probability
namespace FourLabelTransportation

/-!
# Actual finite rational records from transportation tables

Each of the sixteen labelled cells is retained as an atom, including the
four zero-weight forbidden diagonal cells.  The original positive margin
total is the record's denominator.  Normalization comes from the table's
proved row sums, not from a new assumed probability-law field.

The row, column and cell formulas are exact common-denominator probabilities.
The off-diagonal event has probability one, so a later bijective relabelling
can turn this record into an actual IV coupling with a proved consistency
support condition.  Zero rows and columns are allowed; only the complete
record's total must be positive.  No conditional or singleton mass is divided
out, and no replacement of a null cell by an arbitrary conditional occurs.

All finite identities below expand the fixed sixteen-cell data layout.
They are symbolic in the supplied weights and therefore never enumerate a
possibly large common denominator or unit-cell expansion.
-/

def tableAtoms (cells : Cells) : List ((Fin 4 × Fin 4) × Nat) :=
  candidateEdges.map (fun edge => (edge, cells edge.1 edge.2))

theorem tableAtoms_total (cells : Cells) :
    FiniteProbRecord.totalMass (tableAtoms cells) = sum4 (fun row => sum4 (cells row)) := by
  simp [tableAtoms, candidateEdges, FiniteProbRecord.totalMass, sum4, Nat.add_assoc]

theorem tableAtoms_row (cells : Cells) (row : Fin 4) :
    FiniteProbRecord.eventMass (tableAtoms cells) (fun pair => decide (pair.1 = row)) = sum4 (cells row) := by
  rcases label_cases row with same | same | same | same <;> subst row <;>
    simp [tableAtoms, candidateEdges, FiniteProbRecord.eventMass, sum4, Nat.add_assoc]

theorem tableAtoms_column (cells : Cells) (column : Fin 4) :
    FiniteProbRecord.eventMass (tableAtoms cells) (fun pair => decide (pair.2 = column)) =
      sum4 (fun row => cells row column) := by
  rcases label_cases column with same | same | same | same <;> subst column <;>
    simp [tableAtoms, candidateEdges, FiniteProbRecord.eventMass, sum4, Nat.add_assoc]

theorem tableAtoms_cell (cells : Cells) (row column : Fin 4) :
    FiniteProbRecord.eventMass (tableAtoms cells) (FiniteProbRecord.singletonEvent (row, column)) = cells row column := by
  rcases label_cases row with same | same | same | same <;> subst row <;>
    rcases label_cases column with same | same | same | same <;> subst column <;>
    simp [tableAtoms, candidateEdges, FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent]

def offDiagonal : Event (Fin 4 × Fin 4) := fun pair => decide (pair.1 ≠ pair.2)

theorem tableAtoms_offDiagonal (cells : Cells) (excluded : forall label, cells label label = 0) :
    FiniteProbRecord.eventMass (tableAtoms cells) offDiagonal = FiniteProbRecord.totalMass (tableAtoms cells) := by
  simp [tableAtoms, candidateEdges, FiniteProbRecord.eventMass, FiniteProbRecord.totalMass,
    offDiagonal, excluded]

/-- A normalized probability record, with the original sixteen natural
weights and the supplied positive total.  There is no assumed semantic law
or positivity requirement for an individual atom. -/
def record (total : Nat) (positive : 0 < total) (rows columns : Masses)
    (margins : Margins total rows columns) (table : Transportation rows columns) :
    FiniteProbRecord (Fin 4 × Fin 4) where
  atoms := tableAtoms table.cells
  den := total
  den_pos := positive
  total_mass := (tableAtoms_total table.cells).trans
    ((sum4_congr _ _ table.row_sum).trans margins.rows_total)

theorem record_row (total : Nat) (positive : 0 < total) (rows columns : Masses)
    (margins : Margins total rows columns) (table : Transportation rows columns) (row : Fin 4) :
    QProb.Equiv ((record total positive rows columns margins table).probVal (fun pair => decide (pair.1 = row)))
      ⟨rows row, total, positive⟩ := by
  have mass := (tableAtoms_row table.cells row).trans (table.row_sum row)
  change FiniteProbRecord.eventMass (tableAtoms table.cells) (fun pair => decide (pair.1 = row)) * total = rows row * total
  rw [mass]

theorem record_column (total : Nat) (positive : 0 < total) (rows columns : Masses)
    (margins : Margins total rows columns) (table : Transportation rows columns) (column : Fin 4) :
    QProb.Equiv ((record total positive rows columns margins table).probVal (fun pair => decide (pair.2 = column)))
      ⟨columns column, total, positive⟩ := by
  have mass := (tableAtoms_column table.cells column).trans (table.column_sum column)
  change FiniteProbRecord.eventMass (tableAtoms table.cells) (fun pair => decide (pair.2 = column)) * total = columns column * total
  rw [mass]

theorem record_cell (total : Nat) (positive : 0 < total) (rows columns : Masses)
    (margins : Margins total rows columns) (table : Transportation rows columns) (row column : Fin 4) :
    QProb.Equiv ((record total positive rows columns margins table).probVal (FiniteProbRecord.singletonEvent (row, column)))
      ⟨table.cells row column, total, positive⟩ := by
  change FiniteProbRecord.eventMass (tableAtoms table.cells) _ * total = table.cells row column * total
  rw [tableAtoms_cell]

/-- Forbidden diagonal cells have exactly zero weight, so the record's
complete mass is concentrated on permitted off-diagonal pairs. -/
theorem record_offDiagonal (total : Nat) (positive : 0 < total) (rows columns : Masses)
    (margins : Margins total rows columns) (table : Transportation rows columns) :
    QProb.Equiv ((record total positive rows columns margins table).probVal offDiagonal) QProb.one := by
  have mass := (tableAtoms_offDiagonal table.cells table.diagonal_zero).trans
    (record total positive rows columns margins table).total_mass
  change FiniteProbRecord.eventMass (tableAtoms table.cells) offDiagonal * 1 = 1 * total
  simpa only [Nat.mul_one, Nat.one_mul] using mass

end FourLabelTransportation
end Probability
end Thesis
