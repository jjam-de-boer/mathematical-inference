import Thesis.Probability.FourLabelTransportationExtrema

namespace Thesis
namespace Probability
namespace Examples
namespace FourLabelTransportationExtrema

open Thesis.Probability.FourLabelTransportation

/-!
# Exact cell maxima and the load-bearing untouched-label cut

Uniform one-unit margins have maximum one in every permitted cell.  A
second fixture gives the requested row and column two units each, but
another label has row-plus-column mass equal to the total.  Its cut forces
the requested cell to zero.  Merely taking the minimum of the selected row
and column would therefore produce a false sharpness claim.

The maximizing tables are actual outputs of the reserve-and-complete
constructor.  Their attained values and the universal exclusion use the
symbolic theorem.  Kernel numerical decisions inspect only the displayed
four margins and minimum expressions, not an unbounded optimization search.
-/

def units : Masses := fun _ => 1

theorem unit_margins : Margins 4 units units := by
  refine ⟨rfl, rfl, ?_⟩
  intro _
  change 1 + 1 ≤ 4
  decide +kernel

def selected : Fin 4 × Fin 4 := (0, 1)
theorem selected_different : selected.1 ≠ selected.2 := by decide +kernel

theorem unit_capacity : edgeCapacity 4 units units selected = 1 := by decide +kernel

def unitMaximum : Transportation units units := maximizeCell 4 units units unit_margins selected selected_different

theorem unit_maximum_attained : unitMaximum.cells 0 1 = 1 :=
  (maximizeCell_attains 4 units units unit_margins selected selected_different).trans unit_capacity

def cutRows : Masses := fun label => if label = 0 ∨ label = 2 then 2 else 0
def cutColumns : Masses := fun label => if label = 1 ∨ label = 2 then 2 else 0

theorem cut_margins : Margins 4 cutRows cutColumns := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  decide +kernel

theorem cut_capacity : edgeCapacity 4 cutRows cutColumns selected = 0 := by decide +kernel

def cutMaximum : Transportation cutRows cutColumns := maximizeCell 4 cutRows cutColumns cut_margins selected selected_different

theorem cut_maximum_attained : cutMaximum.cells 0 1 = 0 :=
  (maximizeCell_attains 4 cutRows cutColumns cut_margins selected selected_different).trans cut_capacity

/-- The cut excludes positive mass in every table with these margins,
despite both selected margins being nonzero. -/
theorem cut_excludes (table : Transportation cutRows cutColumns) : table.cells 0 1 = 0 := by
  have bounded := cell_le_edgeCapacity 4 cutRows cutColumns cut_margins table selected selected_different
  rw [cut_capacity] at bounded
  exact Nat.eq_zero_of_le_zero bounded

end FourLabelTransportationExtrema
end Examples
end Probability
end Thesis
