import Thesis.Probability.FourLabelTransportationConstruction

namespace Thesis
namespace Probability
namespace FourLabelTransportation

/-!
# Diagonal-free transportation: necessity and exact feasibility

The construction and all its supporting lemmas are re-exported from
`FourLabelTransportationConstruction`. Existing clients may keep importing
this module: public declaration names and types are unchanged.

Separating construction from this final theorem boundary lets Lean reuse its
checked artifact instead of retaining the entire construction elaboration
while checking the capacity argument. This is a compilation boundary only:
all original proof bodies are retained, including the zero-total case and
the unbounded natural-weight constructor. The faster batched constructor
remains a separate downstream module, with its existing guarantees.
-/

/-- Diagonal exclusion also forces the four capacity inequalities.  This
checks necessity separately from the recursive constructor: a whole row and
the same-labelled whole column do not share any positive cell. -/
theorem transportation_capacity (total : Nat) (rows columns : Masses)
    (rowsTotal : sum4 rows = total) (table : Transportation rows columns) :
    forall label, rows label + columns label ≤ total := by
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
  intro label
  rcases label_cases label with same | same | same | same <;> subst label <;>
    simp only [sum4] at * <;> omega

/-- Exact finite feasibility, including the zero-total boundary.  The
constructor's denominator is whatever common scaling a caller supplies;
there is no bounded search over rational probability parameters. -/
theorem transportation_exists_iff (total : Nat) (rows columns : Masses)
    (rowsTotal : sum4 rows = total) (columnsTotal : sum4 columns = total) :
    Nonempty (Transportation rows columns) ↔ forall label, rows label + columns label ≤ total := by
  constructor
  · rintro ⟨table⟩
    exact transportation_capacity total rows columns rowsTotal table
  · intro capacity
    exact ⟨transport total rows columns ⟨rowsTotal, columnsTotal, capacity⟩⟩

end FourLabelTransportation
end Probability
end Thesis
