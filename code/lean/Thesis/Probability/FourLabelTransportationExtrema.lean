import Thesis.Probability.FourLabelTransportationBatched

namespace Thesis
namespace Probability
namespace FourLabelTransportation

/-!
# Sharp cell maxima in diagonal-free four-label transportation

An off-diagonal cell is bounded by its whole row, its whole column, and
the spare capacity of each untouched label.  The minimum of those bounds
is exact: reserve that many units in the cell, construct a feasible table
for the remaining margins, then restore the reserved mass.  The universal
bound ensures that the completed table cannot add extra mass to that cell.

All operations act on supplied natural masses.  Zero maxima and zero
remaining totals are allowed; no positive-cell division or search over
bounded rational denominators is involved.  A reservation is checked
against the true remaining capacities, not just row and column availability.

The constructor returns an actual table with the original margins.  This
module proves a *single* cell maximum.  Simultaneous maxima required for
sharp treatment-effect endpoints are a separate compatibility obligation.
-/

/-- Finish the remaining transport, then restore the actual reserved mass.
No optimizer correctness assertion is supplied as a constructor field. -/
def completeReservation (total : Nat) (rows columns : Masses)
    (margins : Margins total rows columns) (edge : Fin 4 × Fin 4) (amount : Nat)
    (reserved : Reservation total rows columns edge amount) : Transportation rows columns :=
  restoreReservation total rows columns edge amount reserved
    (transportBatched (total - amount) (reserveMasses rows edge.1 amount) (reserveMasses columns edge.2 amount)
      (reservation_margins total rows columns margins edge amount reserved))

theorem completeReservation_selected_ge (total : Nat) (rows columns : Masses)
    (margins : Margins total rows columns) (edge : Fin 4 × Fin 4) (amount : Nat)
    (reserved : Reservation total rows columns edge amount) :
    amount ≤ (completeReservation total rows columns margins edge amount reserved).cells edge.1 edge.2 :=
  restoreReservation_selected_ge total rows columns edge amount reserved _

/-- An actual table maximizing the requested cell throughout the complete
transportation class with the supplied original margins. -/
def maximizeCell (total : Nat) (rows columns : Masses) (margins : Margins total rows columns)
    (edge : Fin 4 × Fin 4) (different : edge.1 ≠ edge.2) : Transportation rows columns :=
  completeReservation total rows columns margins edge (edgeCapacity total rows columns edge)
    (edgeCapacity_reservation total rows columns margins edge different)

theorem maximizeCell_attains (total : Nat) (rows columns : Masses) (margins : Margins total rows columns)
    (edge : Fin 4 × Fin 4) (different : edge.1 ≠ edge.2) :
    (maximizeCell total rows columns margins edge different).cells edge.1 edge.2 = edgeCapacity total rows columns edge := by
  have upper := cell_le_edgeCapacity total rows columns margins (maximizeCell total rows columns margins edge different) edge different
  have lower := completeReservation_selected_ge total rows columns margins edge
    (edgeCapacity total rows columns edge) (edgeCapacity_reservation total rows columns margins edge different)
  exact Nat.le_antisymm upper lower

end FourLabelTransportation
end Probability
end Thesis
