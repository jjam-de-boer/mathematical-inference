import Thesis.Probability.FourLabelTransportation

namespace Thesis
namespace Probability
namespace Examples
namespace FourLabelTransportation

open Thesis.Probability.FourLabelTransportation

/-!
# Small transportation regressions with zero and concentrated margins

These tests exercise the explicit table constructor, not only an existential
feasibility assertion.  Zero total returns the zero table.  A two-unit row
concentrated at label zero and a column concentrated at label one must place
both units in the off-diagonal cell `(0,1)`.  Equal four-label margins give
one unit to every row and column while leaving every diagonal cell zero.

Only the two-unit computation is reduced by the kernel.  The universal
row/column/diagonal assertions use the constructor's proved fields; no large
rational denominator or optimization instance is enumerated in these tests.
-/

def zeros : Masses := fun _ => 0
def units : Masses := fun _ => 1
def concentrated (label : Fin 4) : Masses := fun index => if index = label then 2 else 0

theorem zero_margins : Margins 0 zeros zeros := by
  refine ⟨rfl, rfl, ?_⟩
  intro _
  exact Nat.le_refl 0

theorem concentrated_margins : Margins 2 (concentrated 0) (concentrated 1) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  decide +kernel

theorem unit_margins : Margins 4 units units := by
  refine ⟨rfl, rfl, ?_⟩
  intro _
  change 1 + 1 ≤ 4
  decide +kernel

def zeroTable : Transportation zeros zeros := transport 0 zeros zeros zero_margins
def concentratedTable : Transportation (concentrated 0) (concentrated 1) :=
  transport 2 (concentrated 0) (concentrated 1) concentrated_margins
def unitTable : Transportation units units := transport 4 units units unit_margins

theorem zero_table : forall row column, zeroTable.cells row column = 0 := fun _ _ => rfl
theorem concentrated_cell : concentratedTable.cells 0 1 = 2 := by decide +kernel

theorem unit_rows : forall row, sum4 (unitTable.cells row) = 1 := unitTable.row_sum
theorem unit_columns : forall column, sum4 (fun row => unitTable.cells row column) = 1 := unitTable.column_sum
theorem unit_diagonal : forall label, unitTable.cells label label = 0 := unitTable.diagonal_zero

end FourLabelTransportation
end Examples
end Probability
end Thesis
