import Thesis.Probability.FourLabelTransportationJointExtrema
import Thesis.Probability.FourLabelTransportationScaling

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

/-! ## A single asymmetric table attaining two complementary maxima -/

def asymmetricRows : Masses := fun label => if label = 0 then 2 else 1
def asymmetricColumns : Masses := fun label => if label = 1 then 2 else 1

theorem asymmetric_margins : Margins 5 asymmetricRows asymmetricColumns := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  decide +kernel

def opposite : Fin 4 × Fin 4 := (3, 2)
theorem opposite_different : opposite.1 ≠ opposite.2 := by decide +kernel

theorem complementary_edges : ComplementaryEdges selected opposite := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  decide +kernel

theorem asymmetric_first_capacity : edgeCapacity 5 asymmetricRows asymmetricColumns selected = 2 := by decide +kernel
theorem asymmetric_second_capacity : edgeCapacity 5 asymmetricRows asymmetricColumns opposite = 1 := by decide +kernel

def asymmetricJoint : Transportation asymmetricRows asymmetricColumns :=
  maximizeComplementary 5 asymmetricRows asymmetricColumns asymmetric_margins selected opposite
    selected_different opposite_different complementary_edges

/-- Both values belong to one table with the original margins.  Two
separate existence proofs would not establish this assertion. -/
theorem asymmetric_joint_attained : asymmetricJoint.cells 0 1 = 2 ∧ asymmetricJoint.cells 3 2 = 1 := by
  have attained := maximizeComplementary_attains 5 asymmetricRows asymmetricColumns asymmetric_margins
    selected opposite selected_different opposite_different complementary_edges
  simpa only [asymmetric_first_capacity, asymmetric_second_capacity] using attained

theorem asymmetric_sum_optimal (other : Transportation asymmetricRows asymmetricColumns) :
    other.cells 0 1 + other.cells 3 2 ≤ asymmetricJoint.cells 0 1 + asymmetricJoint.cells 3 2 :=
  maximizeComplementary_sum 5 asymmetricRows asymmetricColumns asymmetric_margins selected opposite
    selected_different opposite_different complementary_edges other

/-! ## Unknown rational weights need not lie on the observed denominator grid -/

/-- Eight unit cells yield row and column masses two.  Individual cells
have odd mass, so this table is not twice an integer table on total four. -/
def nongridTable : Transportation (fun label => units label * 2) (fun label => units label * 2) where
  cells := fun row column => if column.val = (row.val + 1) % 4 ∨ column.val = (row.val + 2) % 4 then 1 else 0
  row_sum := by decide +kernel
  column_sum := by decide +kernel
  diagonal_zero := by decide +kernel

theorem nongrid_cell : nongridTable.cells 0 1 = 1 := rfl

theorem nongrid_not_rescaled : ¬ ∃ original : Transportation units units,
    forall row column, nongridTable.cells row column = original.cells row column * 2 := by
  rintro ⟨original, same⟩
  have cell := same 0 1
  rw [nongrid_cell] at cell
  omega

/-- The universal bound still covers this compatible rational-grid
refinement; no assumption that the unknown table is an integral rescaling
has slipped into the optimization theorem. -/
theorem nongrid_bound : nongridTable.cells 0 1 ≤ 2 := by
  have bounded := scaled_cell_bound 4 units units unit_margins 2 selected selected_different nongridTable
  simpa only [unit_capacity] using bounded

end FourLabelTransportationExtrema
end Examples
end Probability
end Thesis
