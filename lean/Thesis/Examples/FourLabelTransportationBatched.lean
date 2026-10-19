import Thesis.Probability.FourLabelTransportationExtrema

namespace Thesis
namespace Probability
namespace Examples
namespace FourLabelTransportationBatched

open Thesis.Probability.FourLabelTransportation

/-!
# Batched transport at large natural mass and zero boundaries

The billion-unit example reduces the actual constructor in the kernel.  A
unit-recursive algorithm would need a billion positive calls; here the first
eligible cell absorbs the complete total.  The second fixture has uniform
large margins and exercises successive batches.  These are finite exact
regressions, not timing claims about arbitrary native causal-model expansion.

The extremal assertion also checks the existing maximizing interface after
its residual completion was switched to batching.  All old transportation
and IV endpoint theorems remain part of the complete build and axiom audit.
-/

def concentrated (selected : Fin 4) : Masses :=
  fun label => if label = selected then 1000000000 else 0

theorem concentrated_margins : Margins 1000000000 (concentrated 0) (concentrated 1) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  decide +kernel

def largeTable : Transportation (concentrated 0) (concentrated 1) :=
  transportBatched 1000000000 (concentrated 0) (concentrated 1) concentrated_margins

theorem large_cell : largeTable.cells 0 1 = 1000000000 := by decide +kernel

def uniform : Masses := fun _ => 1000000

/-- Establish the uniform capacities before specializing the mass. Keeping
this arithmetic proof symbolic avoids normalizing a large concrete margins
constructor in the kernel. The later regression still uses the same million
units per label and checks the actual batched table, not a smaller surrogate.
Only natural-number arithmetic is used; no computational trust axiom is added. -/
private theorem uniform_margins_general (mass : Nat) :
    Margins (mass + mass + mass + mass) (fun _ => mass) (fun _ => mass) := by
  refine ⟨rfl, rfl, ?_⟩
  intro _
  change mass + mass ≤ mass + mass + mass + mass
  omega

theorem uniform_margins : Margins 4000000 uniform uniform :=
  uniform_margins_general 1000000

def uniformTable : Transportation uniform uniform :=
  transportBatched 4000000 uniform uniform uniform_margins

theorem uniform_first_cell : uniformTable.cells 0 1 = 1000000 := by decide +kernel
theorem uniform_row_sums : forall row, sum4 (uniformTable.cells row) = uniform row := uniformTable.row_sum
theorem uniform_column_sums : forall column, sum4 (fun row => uniformTable.cells row column) = uniform column :=
  uniformTable.column_sum
theorem uniform_diagonal : forall label, uniformTable.cells label label = 0 := uniformTable.diagonal_zero

theorem extremal_capacity_preserved :
    (maximizeCell 4000000 uniform uniform uniform_margins (0, 1) (by decide +kernel)).cells 0 1 = 1000000 :=
  (maximizeCell_attains 4000000 uniform uniform uniform_margins (0, 1) (by decide +kernel)).trans (by decide +kernel)

def zeros : Masses := fun _ => 0
theorem zero_margins : Margins 0 zeros zeros := ⟨rfl, rfl, fun _ => Nat.le_refl 0⟩
theorem zero_cell : (transportBatched 0 zeros zeros zero_margins).cells 0 1 = 0 := by decide +kernel

end FourLabelTransportationBatched
end Examples
end Probability
end Thesis
