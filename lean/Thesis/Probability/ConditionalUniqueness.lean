import Thesis.Probability.FiniteRecord

namespace Thesis
namespace Probability

/-!
# Two-way conditional comparison without matched denominators

Equal conditioning marginals are sufficient to transfer joint separation
to conditional separation, but they are not necessary.  For example, a
common positive observation channel applied to two different outcome laws
changes the conditioning marginal while retaining different posteriors.

This module proves the finite normalization argument needed for that case.
Only one explicitly supplied conditioning column must have positive cells.
Equality of the outcome conditional in that column and equality of the
reverse conditionals everywhere force the full joint laws to agree.
Different atom lists, repeated labels, natural weights, and rational
denominators are retained.  No likelihood is assumed independent of the
outcome, and no conditioning marginal is assumed equal.

The proof first cancels the positive reference cells to obtain a common
scale for all outcome rows.  Summing those rows determines the scale from
the two genuine prior normalizations.  Reverse conditional comparison then
recovers every joint cell.  All choices are explicit finite data; arbitrary
propositional excluded middle and choice are not used.

At this layer the laws are actual finite records, not SCMs.  Applying the
result to a causal terminal additionally requires connecting its kernel
evaluation to these records and proving the common reverse conditional.
-/

namespace ConditionalUniqueness

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

/-- A whole outcome row of a joint record. -/
def rowEvent (row : α) : Event (α × β) := fun pair => decide (pair.1 = row)

/-- A whole conditioning column of a joint record. -/
def columnEvent (column : β) : Event (α × β) := fun pair => decide (pair.2 = column)

/-- One full-value joint cell; both coordinate equalities are retained. -/
def cellEvent (row : α) (column : β) : Event (α × β) :=
  fun pair => rowEvent row pair && columnEvent column pair

private theorem cell_singleton (row : α) (column : β) :
    cellEvent row column = FiniteProbRecord.singletonEvent (row, column) := by
  funext pair
  apply Bool.eq_iff_iff.mpr
  simp only [cellEvent, rowEvent, columnEvent, Bool.and_eq_true_iff,
    decide_eq_true_eq, FiniteProbRecord.singletonEvent]
  exact ⟨fun parts => Prod.ext parts.1 parts.2,
    fun same => ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩⟩

/-- Finite normalization at raw natural-mass level.  This is obtained
from the existing singleton-sum law on the record's actual denominator;
the denominator is cancelled only using its stored positivity proof. -/
private theorem sum_singletonMass_eq_den (record : FiniteProbRecord α)
    (values : List α) (nodup : values.Nodup) (complete : forall value, value ∈ values) :
    (values.map (fun value => FiniteProbRecord.eventMass record.atoms
      (FiniteProbRecord.singletonEvent value))).sum = record.den := by
  have membership : FiniteProbRecord.membershipEvent values = topEvent := by
    funext value
    exact decide_eq_true (complete value)
  have sum := record.probVal_membership_equiv_listSum values nodup
  rw [membership] at sum
  have presentation := QProb.listSum_mk_same_den record.den record.den_pos
    (values.map (fun value => FiniteProbRecord.eventMass record.atoms (FiniteProbRecord.singletonEvent value)))
  have combined : QProb.Equiv (record.probVal topEvent)
      ⟨(values.map (fun value => FiniteProbRecord.eventMass record.atoms
        (FiniteProbRecord.singletonEvent value))).sum, record.den, record.den_pos⟩ :=
    QProb.equiv_trans sum (by simpa only [List.map_map, Function.comp_def, FiniteProbRecord.probVal] using presentation)
  change FiniteProbRecord.eventMass record.atoms topEvent * record.den =
    (values.map (fun value => FiniteProbRecord.eventMass record.atoms (FiniteProbRecord.singletonEvent value))).sum * record.den at combined
  exact (Nat.eq_of_mul_eq_mul_right record.den_pos combined).symm.trans
    ((FiniteProbRecord.eventMass_top record.atoms).trans record.total_mass)

private def rowMass (record : FiniteProbRecord (α × β)) (row : α) : Nat :=
  FiniteProbRecord.eventMass record.atoms (rowEvent row)

private def columnMass (record : FiniteProbRecord (α × β)) (column : β) : Nat :=
  FiniteProbRecord.eventMass record.atoms (columnEvent column)

private def cellMass (record : FiniteProbRecord (α × β)) (row : α) (column : β) : Nat :=
  FiniteProbRecord.eventMass record.atoms (cellEvent row column)

omit [DecidableEq β] in
private theorem sum_rowMass_eq_den (record : FiniteProbRecord (α × β))
    (values : List α) (nodup : values.Nodup) (complete : forall value, value ∈ values) :
    (values.map (rowMass record)).sum = record.den := by
  simpa only [rowMass, rowEvent, FiniteProbRecord.map, FiniteProbRecord.eventMass_map_labels,
    FiniteProbRecord.singletonEvent] using sum_singletonMass_eq_den (record.map Prod.fst) values nodup complete

/-- The decisive cross-multiplication step.  The reference column need
not have equal mass in the two records.  A positive *right cell* is the
only quantity cancelled to compare its entire outcome row. -/
private theorem row_scale_of_twoWay
    (left right : FiniteProbRecord (α × β)) (reference : β) (row : α)
    (positive : 0 < cellMass right row reference)
    (forward : cellMass left row reference * columnMass right reference =
      cellMass right row reference * columnMass left reference)
    (reverse : cellMass left row reference * rowMass right row =
      cellMass right row reference * rowMass left row) :
    rowMass left row * columnMass right reference = rowMass right row * columnMass left reference := by
  apply Nat.eq_of_mul_eq_mul_left positive
  calc
    _ = (cellMass right row reference * rowMass left row) * columnMass right reference := by ac_rfl
    _ = (cellMass left row reference * rowMass right row) * columnMass right reference := by rw [← reverse]
    _ = (cellMass left row reference * columnMass right reference) * rowMass right row := by ac_rfl
    _ = (cellMass right row reference * columnMass left reference) * rowMass right row := by rw [forward]
    _ = _ := by ac_rfl

omit [DecidableEq α] in
private theorem sum_scaled (values : List α) (left right : α -> Nat) (first second : Nat)
    (scaled : forall row, left row * first = right row * second) :
    (values.map left).sum * first = (values.map right).sum * second := by
  induction values with
  | nil => simp only [List.map_nil, List.sum_nil, Nat.zero_mul]
  | cons row rest ih =>
      simp only [List.map_cons, List.sum_cons, Nat.add_mul]
      rw [scaled row, ih]

end ConditionalUniqueness

namespace FiniteProbRecord

open ConditionalUniqueness

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

/-- Raw conditional cross-products determine every normalized joint cell.
Only the right reference-column cells and its total column mass must be
positive.  Left row/column positivity is unnecessary at this algebraic
level, where no undefined conditional is represented as a zero value.

`forward` is comparison of outcome-given-reference-column; `reverse` is
comparison of conditioning-given-outcome.  Normalization is read from the
actual two records, rather than supplied as an equality of denominators. -/
theorem cell_probVal_equiv_of_twoWayConditionalMasses
    (left right : FiniteProbRecord (α × β))
    (rows : List α) (nodup : rows.Nodup) (complete : forall row, row ∈ rows)
    (reference : β) (columnPositive : right.EventPositive (columnEvent reference))
    (cellsPositive : forall row, right.EventPositive (cellEvent row reference))
    (forward : forall row,
      eventMass left.atoms (cellEvent row reference) * eventMass right.atoms (columnEvent reference) =
        eventMass right.atoms (cellEvent row reference) * eventMass left.atoms (columnEvent reference))
    (reverse : forall row column,
      eventMass left.atoms (cellEvent row column) * eventMass right.atoms (rowEvent row) =
        eventMass right.atoms (cellEvent row column) * eventMass left.atoms (rowEvent row))
    (row : α) (column : β) :
    QProb.Equiv (left.probVal (cellEvent row column)) (right.probVal (cellEvent row column)) := by
  have scaled (value : α) := ConditionalUniqueness.row_scale_of_twoWay left right reference value
    (cellsPositive value) (forward value) (reverse value reference)
  have total := ConditionalUniqueness.sum_scaled rows (ConditionalUniqueness.rowMass left)
    (ConditionalUniqueness.rowMass right) (ConditionalUniqueness.columnMass right reference)
    (ConditionalUniqueness.columnMass left reference) scaled
  rw [ConditionalUniqueness.sum_rowMass_eq_den left rows nodup complete,
    ConditionalUniqueness.sum_rowMass_eq_den right rows nodup complete] at total
  have rowEqual (value : α) : ConditionalUniqueness.rowMass left value * right.den =
      ConditionalUniqueness.rowMass right value * left.den := by
    apply Nat.eq_of_mul_eq_mul_right columnPositive
    calc
      _ = (ConditionalUniqueness.rowMass left value * ConditionalUniqueness.columnMass right reference) * right.den := by ac_rfl
      _ = (ConditionalUniqueness.rowMass right value * ConditionalUniqueness.columnMass left reference) * right.den := by rw [scaled value]
      _ = ConditionalUniqueness.rowMass right value * (right.den * ConditionalUniqueness.columnMass left reference) := by ac_rfl
      _ = ConditionalUniqueness.rowMass right value * (left.den * ConditionalUniqueness.columnMass right reference) := by rw [← total]
      _ = _ := by ac_rfl
  have rowPositive : 0 < ConditionalUniqueness.rowMass right row :=
    Nat.lt_of_lt_of_le (cellsPositive row)
      (eventMass_mono right.atoms (cellEvent row reference) (rowEvent row)
        (fun _ selected => (Bool.and_eq_true_iff.mp selected).1))
  change ConditionalUniqueness.cellMass left row column * right.den =
    ConditionalUniqueness.cellMass right row column * left.den
  have cellScaled : ConditionalUniqueness.cellMass left row column * ConditionalUniqueness.rowMass right row =
      ConditionalUniqueness.cellMass right row column * ConditionalUniqueness.rowMass left row := reverse row column
  apply Nat.eq_of_mul_eq_mul_right rowPositive
  calc
    _ = (ConditionalUniqueness.cellMass left row column * ConditionalUniqueness.rowMass right row) * right.den := by ac_rfl
    _ = (ConditionalUniqueness.cellMass right row column * ConditionalUniqueness.rowMass left row) * right.den := by rw [cellScaled]
    _ = ConditionalUniqueness.cellMass right row column * (ConditionalUniqueness.rowMass left row * right.den) := by ac_rfl
    _ = ConditionalUniqueness.cellMass right row column * (ConditionalUniqueness.rowMass right row * left.den) := by rw [rowEqual row]
    _ = _ := by ac_rfl

/-- Equality of both conditional directions determines every joint event.
The first direction is needed only at the explicit reference conditioner;
reverse comparison may inspect every full-value conditioner.  Positive
support is carried explicitly wherever `conditionOn` is used. -/
theorem probVal_equiv_of_twoWayConditionals
    (left right : FiniteProbRecord (α × β))
    (rows : List α) (rowNodup : rows.Nodup) (rowsComplete : forall row, row ∈ rows)
    (values : List (α × β)) (nodup : values.Nodup) (complete : forall value, value ∈ values)
    (reference : β)
    (leftColumn : left.EventPositive (columnEvent reference)) (rightColumn : right.EventPositive (columnEvent reference))
    (leftRows : forall row, left.EventPositive (rowEvent row)) (rightRows : forall row, right.EventPositive (rowEvent row))
    (rightCells : forall row, right.EventPositive (cellEvent row reference))
    (forward : forall row, QProb.Equiv
      ((left.conditionOn (columnEvent reference) leftColumn).probVal (rowEvent row))
      ((right.conditionOn (columnEvent reference) rightColumn).probVal (rowEvent row)))
    (reverse : forall row column, QProb.Equiv
      ((left.conditionOn (rowEvent row) (leftRows row)).probVal (columnEvent column))
      ((right.conditionOn (rowEvent row) (rightRows row)).probVal (columnEvent column)))
    (event : Event (α × β)) : QProb.Equiv (left.probVal event) (right.probVal event) := by
  apply probVal_extensional_of_singletons left right values nodup complete
  intro value
  rw [← ConditionalUniqueness.cell_singleton]
  apply cell_probVal_equiv_of_twoWayConditionalMasses left right rows rowNodup rowsComplete reference rightColumn rightCells
  · intro row
    have compared := forward row
    simp only [QProb.Equiv, conditionOn, probVal, eventMass_filter_event] at compared
    change eventMass left.atoms (fun pair => columnEvent reference pair && rowEvent row pair) *
        eventMass right.atoms (columnEvent reference) =
      eventMass right.atoms (fun pair => columnEvent reference pair && rowEvent row pair) *
        eventMass left.atoms (columnEvent reference) at compared
    have commute : (fun pair => columnEvent reference pair && rowEvent row pair) = cellEvent row reference := by
      funext pair
      exact Bool.and_comm _ _
    rw [commute] at compared
    exact compared
  · intro row column
    simpa only [QProb.Equiv, conditionOn, probVal, eventMass_filter_event, cellEvent] using reverse row column

end FiniteProbRecord

end Probability
end Thesis
