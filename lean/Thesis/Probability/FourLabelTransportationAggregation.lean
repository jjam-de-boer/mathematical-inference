import Thesis.Probability.FourLabelTransportationRecord
import Thesis.Probability.FiniteRecordSlicing
import Thesis.Probability.FiniteRecordAlmostSure

namespace Thesis
namespace Probability
namespace FourLabelTransportation

/-!
# Aggregate every arbitrary finite coupling into an exact transportation table

A supplied record can have arbitrary rational denominator, repeated pair
labels, and zero-weight forbidden cells.  Its sixteen singleton masses give
a natural table with its *own* original denominator.  Row and column sums
are proved by finite fibre additivity, not asserted as a model-class field.
Probability-one off-diagonal support forces each diagonal singleton mass
to zero without requiring every listed atom to satisfy the support predicate.

The dense sixteen-cell record of the resulting table preserves every event
of the input record.  Consequently optimization does not select a convenient
subfamily of couplings or impose the observed law's denominator on unknown
response weights.  This is the all-record direction needed before the
scale-independent cell bounds can be applied to every native IV model.
-/

def labels : List (Fin 4) := [0, 1, 2, 3]
theorem labels_nodup : labels.Nodup := by decide +kernel
theorem labels_complete : forall label : Fin 4, label ∈ labels := by decide +kernel

def rowEvent (row : Fin 4) : Event (Fin 4 × Fin 4) := fun pair => decide (pair.1 = row)
def columnEvent (column : Fin 4) : Event (Fin 4 × Fin 4) := fun pair => decide (pair.2 = column)

def aggregateRows (source : FiniteProbRecord (Fin 4 × Fin 4)) : Masses :=
  fun row => FiniteProbRecord.eventMass source.atoms (rowEvent row)
def aggregateColumns (source : FiniteProbRecord (Fin 4 × Fin 4)) : Masses :=
  fun column => FiniteProbRecord.eventMass source.atoms (columnEvent column)
def aggregateCells (source : FiniteProbRecord (Fin 4 × Fin 4)) : Cells :=
  fun row column => FiniteProbRecord.eventMass source.atoms (FiniteProbRecord.singletonEvent (row, column))

private theorem column_fibre (row column : Fin 4) :
    FiniteProbRecord.fibreEvent Prod.snd (rowEvent row) column = FiniteProbRecord.singletonEvent (row, column) := by
  funext pair
  apply Bool.eq_iff_iff.mpr
  simp only [FiniteProbRecord.fibreEvent, rowEvent, FiniteProbRecord.singletonEvent,
    Bool.and_eq_true_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨atColumn, atRow⟩
    exact Prod.ext atRow atColumn
  · intro same
    exact ⟨congrArg Prod.snd same, congrArg Prod.fst same⟩

private theorem row_fibre (row column : Fin 4) :
    FiniteProbRecord.fibreEvent Prod.fst (columnEvent column) row = FiniteProbRecord.singletonEvent (row, column) := by
  funext pair
  apply Bool.eq_iff_iff.mpr
  simp only [FiniteProbRecord.fibreEvent, columnEvent, FiniteProbRecord.singletonEvent,
    Bool.and_eq_true_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨atRow, atColumn⟩
    exact Prod.ext atRow atColumn
  · intro same
    exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩

theorem aggregate_row_sum (source : FiniteProbRecord (Fin 4 × Fin 4)) (row : Fin 4) :
    sum4 (aggregateCells source row) = aggregateRows source row := by
  have split := source.eventMass_eq_listSum_fibres Prod.snd (rowEvent row) labels labels_nodup labels_complete
  simp only [column_fibre] at split
  simpa only [aggregateCells, aggregateRows, sum4, labels, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc] using split.symm

theorem aggregate_column_sum (source : FiniteProbRecord (Fin 4 × Fin 4)) (column : Fin 4) :
    sum4 (fun row => aggregateCells source row column) = aggregateColumns source column := by
  have split := source.eventMass_eq_listSum_fibres Prod.fst (columnEvent column) labels labels_nodup labels_complete
  simp only [row_fibre] at split
  simpa only [aggregateCells, aggregateColumns, sum4, labels, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc] using split.symm

theorem aggregate_rows_total (source : FiniteProbRecord (Fin 4 × Fin 4)) : sum4 (aggregateRows source) = source.den := by
  have split := source.eventMass_eq_listSum_fibres Prod.fst topEvent labels labels_nodup labels_complete
  have fibre (row : Fin 4) : FiniteProbRecord.fibreEvent Prod.fst topEvent row = rowEvent row := by
    funext pair
    simp only [FiniteProbRecord.fibreEvent, topEvent, rowEvent, Bool.and_true]
  simp only [fibre, FiniteProbRecord.eventMass_top, source.total_mass] at split
  simpa only [aggregateRows, sum4, labels, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc] using split.symm

theorem aggregate_columns_total (source : FiniteProbRecord (Fin 4 × Fin 4)) : sum4 (aggregateColumns source) = source.den := by
  have split := source.eventMass_eq_listSum_fibres Prod.snd topEvent labels labels_nodup labels_complete
  have fibre (column : Fin 4) : FiniteProbRecord.fibreEvent Prod.snd topEvent column = columnEvent column := by
    funext pair
    simp only [FiniteProbRecord.fibreEvent, topEvent, columnEvent, Bool.and_true]
  simp only [fibre, FiniteProbRecord.eventMass_top, source.total_mass] at split
  simpa only [aggregateColumns, sum4, labels, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc] using split.symm

/-- Probability-one support removes only zero mass, not zero-weight labels
from the original data.  No arbitrary singleton is assumed positive. -/
theorem aggregate_diagonal_zero (source : FiniteProbRecord (Fin 4 × Fin 4))
    (permitted : QProb.Equiv (source.probVal offDiagonal) QProb.one) (label : Fin 4) :
    aggregateCells source label label = 0 := by
  have null : QProb.Equiv (source.probVal (FiniteProbRecord.singletonEvent (label, label))) QProb.zero :=
    QProb.equiv_trans
      (source.probVal_congr_on_probability_one offDiagonal (FiniteProbRecord.singletonEvent (label, label))
        (fun _ => false) permitted (fun pair allowed => by
          cases selected : FiniteProbRecord.singletonEvent (label, label) pair with
          | false => rfl
          | true =>
              have same : pair = (label, label) := of_decide_eq_true selected
              subst pair
              have different : label ≠ label := of_decide_eq_true allowed
              exact False.elim (different rfl)))
      (source.probVal_false)
  exact (QProb.equiv_num_zero_iff null).mpr rfl

/-- The literal table extracted from any supplied off-diagonal coupling.
Its denominator and weights come from that record, not from observed margins. -/
def aggregateTable (source : FiniteProbRecord (Fin 4 × Fin 4))
    (permitted : QProb.Equiv (source.probVal offDiagonal) QProb.one) :
    Transportation (aggregateRows source) (aggregateColumns source) where
  cells := aggregateCells source
  row_sum := aggregate_row_sum source
  column_sum := aggregate_column_sum source
  diagonal_zero := aggregate_diagonal_zero source permitted

def aggregateMargins (source : FiniteProbRecord (Fin 4 × Fin 4))
    (permitted : QProb.Equiv (source.probVal offDiagonal) QProb.one) :
    Margins source.den (aggregateRows source) (aggregateColumns source) where
  rows_total := aggregate_rows_total source
  columns_total := aggregate_columns_total source
  capacity := transportation_capacity source.den _ _ (aggregate_rows_total source) (aggregateTable source permitted)

/-- The original sparse or repeated-label coupling agrees on *every*
event with the dense table record.  This is the exact all-record direction,
not merely conservation of its row and column totals. -/
theorem aggregated_record_preserves (source : FiniteProbRecord (Fin 4 × Fin 4))
    (permitted : QProb.Equiv (source.probVal offDiagonal) QProb.one) (event : Event (Fin 4 × Fin 4)) :
    QProb.Equiv
      ((record source.den source.den_pos (aggregateRows source) (aggregateColumns source)
        (aggregateMargins source permitted) (aggregateTable source permitted)).probVal event)
      (source.probVal event) := by
  apply FiniteProbRecord.probVal_extensional_of_singletons _ _ candidateEdges candidateEdges_nodup candidateEdges_complete
    (fun reference => ?_) event
  exact record_cell source.den source.den_pos (aggregateRows source) (aggregateColumns source)
    (aggregateMargins source permitted) (aggregateTable source permitted) reference.1 reference.2

end FourLabelTransportation
end Probability
end Thesis
