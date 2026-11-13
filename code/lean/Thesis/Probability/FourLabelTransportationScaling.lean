import Thesis.Probability.FourLabelTransportationExtrema

namespace Thesis
namespace Probability
namespace FourLabelTransportation

/-!
# Scale-independent sharp capacities for rational transportation

An observed rational margin presentation does not restrict the denominator
of an unknown compatible response law.  Multiplying both presentations to
a common natural denominator produces scaled margins, but the unknown table
need not be an integer rescaling of a table on the observed denominator.

The sharp capacity is homogeneous, and its scaled upper bound applies to
*every* table with the scaled margins, including cells not divisible by the
scaling factor.  This is the arithmetic step needed to carry the natural
construction to universal bounds over arbitrary rational response weights.
It is not a bounded-denominator feasibility search or an integrality
assumption on the original causal model's probabilities.

Scaling zero is permitted in these natural identities.  Probability-record
clients still retain their explicit positive total and denominator witnesses;
no zero denominator is introduced by this module.
-/

theorem sum4_scale (masses : Masses) (factor : Nat) :
    sum4 (fun label => masses label * factor) = sum4 masses * factor := by
  simp only [sum4, Nat.add_mul]

theorem minimum4_scale (masses : Masses) (factor : Nat) :
    minimum4 (fun label => masses label * factor) = minimum4 masses * factor := by
  simp only [minimum4, Nat.mul_min_mul_right]

theorem cutCapacity_scale (total : Nat) (rows columns : Masses) (edge : Fin 4 × Fin 4) (factor : Nat) :
    cutCapacity (total * factor) (fun label => rows label * factor) (fun label => columns label * factor) edge =
      (fun label => cutCapacity total rows columns edge label * factor) := by
  funext label
  by_cases endpoint : label = edge.1 ∨ label = edge.2
  · simp only [cutCapacity, if_pos endpoint]
  · simp only [cutCapacity, if_neg endpoint, Nat.sub_mul, Nat.add_mul]

/-- All four cell constraints scale exactly, not merely monotonically.
The original minimum therefore gives the same rational bound at any common
denominator used to compare an unknown compatible table. -/
theorem edgeCapacity_scale (total : Nat) (rows columns : Masses) (edge : Fin 4 × Fin 4) (factor : Nat) :
    edgeCapacity (total * factor) (fun label => rows label * factor) (fun label => columns label * factor) edge =
      edgeCapacity total rows columns edge * factor := by
  simp only [edgeCapacity, cutCapacity_scale, minimum4_scale, Nat.mul_min_mul_right]

def scaleMargins (total : Nat) (rows columns : Masses) (margins : Margins total rows columns) (factor : Nat) :
    Margins (total * factor) (fun label => rows label * factor) (fun label => columns label * factor) where
  rows_total := (sum4_scale rows factor).trans (congrArg (fun mass => mass * factor) margins.rows_total)
  columns_total := (sum4_scale columns factor).trans (congrArg (fun mass => mass * factor) margins.columns_total)
  capacity := fun label => by
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_right factor (margins.capacity label)

/-- This particular scaled table is a witness, not a restriction on all
tables to which the universal theorem below applies. -/
def scaleTable (rows columns : Masses) (table : Transportation rows columns) (factor : Nat) :
    Transportation (fun label => rows label * factor) (fun label => columns label * factor) where
  cells := fun row column => table.cells row column * factor
  row_sum := fun row => (sum4_scale (table.cells row) factor).trans (congrArg (fun mass => mass * factor) (table.row_sum row))
  column_sum := fun column => (sum4_scale (fun row => table.cells row column) factor).trans
    (congrArg (fun mass => mass * factor) (table.column_sum column))
  diagonal_zero := fun label => by rw [table.diagonal_zero, Nat.zero_mul]

/-- Every scaled-margin table is bounded, not only outputs of `scaleTable`.
In the rational application its cells contain the unknown response record's
actual weights multiplied by the observed common denominator. -/
theorem scaled_cell_bound (total : Nat) (rows columns : Masses) (margins : Margins total rows columns)
    (factor : Nat) (edge : Fin 4 × Fin 4) (different : edge.1 ≠ edge.2)
    (other : Transportation (fun label => rows label * factor) (fun label => columns label * factor)) :
    other.cells edge.1 edge.2 ≤ edgeCapacity total rows columns edge * factor := by
  have bounded := cell_le_edgeCapacity (total * factor) _ _ (scaleMargins total rows columns margins factor) other edge different
  rw [edgeCapacity_scale] at bounded
  exact bounded

end FourLabelTransportation
end Probability
end Thesis
