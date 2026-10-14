import Thesis.Probability.Core

namespace Thesis
namespace Probability
namespace FourLabelTransportation

/-!
# Constructive transportation on four labels without diagonal cells

Rows and columns are natural masses with the same total.  A diagonal-free
table exists precisely when each row mass plus the corresponding column
mass is at most that total.  For binary instrumental variables a relabelling
of the column outcome bit turns the four forbidden cells into this diagonal.

The construction removes one actual unit at a time.  An eligible off-diagonal
cell has positive row and column masses and covers every currently tight
capacity constraint.  Decrementing its row and column preserves all capacities,
so recursion on the supplied total ends in an exact natural-weight table.
The cell is found in a fixed finite list; no witness is chosen from an
arbitrary existential proposition.  Only natural and finite-label decisions
are used, and the construction introduces neither real parameters nor signed
probability weights.

The recursion is a proof of existence with an explicit, terminating algorithm,
not a claim of efficient large-denominator execution.  Later probability
clients can scale rational margins to a common natural denominator without
restricting their original denominators.  Optimization and extremal cell
capacities are separate obligations from this feasibility construction.
-/

abbrev Masses := Fin 4 → Nat
abbrev Cells := Fin 4 → Fin 4 → Nat

def sum4 (masses : Masses) : Nat := masses 0 + masses 1 + masses 2 + masses 3

/-- The four explicit labels, used to check finite table identities without
classical quantifier transformations or unbounded enumeration. -/
theorem label_cases : forall label : Fin 4,
    label = 0 ∨ label = 1 ∨ label = 2 ∨ label = 3 := by decide +kernel

private theorem forall_four (predicate : Fin 4 → Prop) :
    (forall label, predicate label) ↔ predicate 0 ∧ predicate 1 ∧ predicate 2 ∧ predicate 3 := by
  constructor
  · intro all
    exact ⟨all 0, all 1, all 2, all 3⟩
  · rintro ⟨zero, one, two, three⟩ label
    rcases label_cases label with same | same | same | same <;> subst label
    · exact zero
    · exact one
    · exact two
    · exact three

theorem sum4_congr (left right : Masses) (same : forall label, left label = right label) :
    sum4 left = sum4 right := by simp only [sum4, same]

theorem sum4_add (left right : Masses) :
    sum4 (fun label => left label + right label) = sum4 left + sum4 right := by
  simp only [sum4]
  ac_rfl

theorem le_sum4 (masses : Masses) (label : Fin 4) : masses label ≤ sum4 masses := by
  rcases label_cases label with same | same | same | same <;> subst label <;>
    simp only [sum4] <;> omega

/-- Normalized margins and the four singleton capacity inequalities.
They allow zero rows, zero columns, and a total of zero. -/
structure Margins (total : Nat) (rows columns : Masses) : Prop where
  rows_total : sum4 rows = total
  columns_total : sum4 columns = total
  capacity : forall label, rows label + columns label ≤ total

/-- An exact table is data, not only a proof of numerical feasibility. -/
structure Transportation (rows columns : Masses) where
  cells : Cells
  row_sum : forall row, sum4 (cells row) = rows row
  column_sum : forall column, sum4 (fun row => cells row column) = columns column
  diagonal_zero : forall label, cells label label = 0

/-- Every untouched capacity must have a unit of slack before the total
is reduced.  The selected row and column lose that unit themselves. -/
def Eligible (total : Nat) (rows columns : Masses) (edge : Fin 4 × Fin 4) : Prop :=
  edge.1 ≠ edge.2 ∧ 0 < rows edge.1 ∧ 0 < columns edge.2 ∧
    forall label, label ≠ edge.1 → label ≠ edge.2 → rows label + columns label < total

instance eligibleDecidable (total : Nat) (rows columns : Masses) (edge : Fin 4 × Fin 4) :
    Decidable (Eligible total rows columns edge) := by
  unfold Eligible
  infer_instance

def candidateEdges : List (Fin 4 × Fin 4) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3),
    (2, 0), (2, 1), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3)]

private theorem candidateEdges_complete (edge : Fin 4 × Fin 4) : edge ∈ candidateEdges := by
  rcases edge with ⟨row, column⟩
  rcases label_cases row with same | same | same | same <;> subst row <;>
    rcases label_cases column with same | same | same | same <;> subst column <;>
    decide +kernel

/-- With the first row positive, at most one of the other three labels can
be tight.  Such a tight label has a positive column, giving an eligible edge.
If none is tight, blocking all three edges forces every other column to zero,
contradicting the first-row capacity.  Each arithmetic subproof excludes the
edge implications from its context, so it checks only a small linear fact. -/
private theorem positive_row_contradiction (total r0 r1 r2 r3 c0 c1 c2 c3 : Nat)
    (rowsTotal : r0 + r1 + r2 + r3 = total)
    (columnsTotal : c0 + c1 + c2 + c3 = total)
    (capacity0 : r0 + c0 ≤ total) (capacity1 : r1 + c1 ≤ total)
    (capacity2 : r2 + c2 ≤ total) (capacity3 : r3 + c3 ≤ total)
    (rowPositive : 0 < r0)
    (blocked01 : 0 < r0 → 0 < c1 → r2 + c2 < total → total ≤ r3 + c3)
    (blocked02 : 0 < r0 → 0 < c2 → r1 + c1 < total → total ≤ r3 + c3)
    (blocked03 : 0 < r0 → 0 < c3 → r1 + c1 < total → total ≤ r2 + c2) : False := by
  by_cases tight1 : r1 + c1 = total
  · have columnPositive : 0 < c1 := by
      clear blocked01 blocked02 blocked03
      omega
    have slack2 : r2 + c2 < total := by
      clear blocked01 blocked02 blocked03
      omega
    have slack3 : r3 + c3 < total := by
      clear blocked01 blocked02 blocked03
      omega
    exact Nat.not_le_of_gt slack3 (blocked01 rowPositive columnPositive slack2)
  · have slack1 : r1 + c1 < total := by
      clear blocked01 blocked02 blocked03
      omega
    by_cases tight2 : r2 + c2 = total
    · have columnPositive : 0 < c2 := by
        clear blocked01 blocked02 blocked03
        omega
      have slack3 : r3 + c3 < total := by
        clear blocked01 blocked02 blocked03
        omega
      exact Nat.not_le_of_gt slack3 (blocked02 rowPositive columnPositive slack1)
    · have slack2 : r2 + c2 < total := by
        clear blocked01 blocked02 blocked03
        omega
      by_cases tight3 : r3 + c3 = total
      · have columnPositive : 0 < c3 := by
          clear blocked01 blocked02 blocked03
          omega
        exact Nat.not_le_of_gt slack2 (blocked03 rowPositive columnPositive slack1)
      · have slack3 : r3 + c3 < total := by
          clear blocked01 blocked02 blocked03
          omega
        have noColumn1 : ¬ 0 < c1 := fun positive =>
          Nat.not_le_of_gt slack3 (blocked01 rowPositive positive slack2)
        have noColumn2 : ¬ 0 < c2 := fun positive =>
          Nat.not_le_of_gt slack3 (blocked02 rowPositive positive slack1)
        have noColumn3 : ¬ 0 < c3 := fun positive =>
          Nat.not_le_of_gt slack2 (blocked03 rowPositive positive slack1)
        clear blocked01 blocked02 blocked03
        omega

/-- Normalize the twelve blocked edges, find a positive row constructively,
then apply the same bounded argument with that row relabelled first.  The
permutations change only the order of natural sums, never the model class. -/
private theorem no_step_impossible (total : Nat) (rows columns : Masses)
    (margins : Margins total rows columns) (positive : 0 < total)
    (blocked : forall edge, ¬ Eligible total rows columns edge) : False := by
  have rowsTotal := margins.rows_total
  have columnsTotal := margins.columns_total
  have capacity0 := margins.capacity 0
  have capacity1 := margins.capacity 1
  have capacity2 := margins.capacity 2
  have capacity3 := margins.capacity 3
  have blocked01 := blocked (0, 1)
  have blocked02 := blocked (0, 2)
  have blocked03 := blocked (0, 3)
  have blocked10 := blocked (1, 0)
  have blocked12 := blocked (1, 2)
  have blocked13 := blocked (1, 3)
  have blocked20 := blocked (2, 0)
  have blocked21 := blocked (2, 1)
  have blocked23 := blocked (2, 3)
  have blocked30 := blocked (3, 0)
  have blocked31 := blocked (3, 1)
  have blocked32 := blocked (3, 2)
  simp only [sum4] at rowsTotal columnsTotal
  simp [Eligible, forall_four] at blocked01 blocked02 blocked03 blocked10 blocked12 blocked13 blocked20 blocked21 blocked23 blocked30 blocked31 blocked32
  have positiveRow : 0 < rows 0 ∨ 0 < rows 1 ∨ 0 < rows 2 ∨ 0 < rows 3 := by
    clear blocked blocked01 blocked02 blocked03 blocked10 blocked12 blocked13 blocked20 blocked21 blocked23 blocked30 blocked31 blocked32
    omega
  rcases positiveRow with rowPositive | rowPositive | rowPositive | rowPositive
  · exact positive_row_contradiction total (rows 0) (rows 1) (rows 2) (rows 3)
      (columns 0) (columns 1) (columns 2) (columns 3) rowsTotal columnsTotal
      capacity0 capacity1 capacity2 capacity3 rowPositive blocked01 blocked02 blocked03
  · apply positive_row_contradiction total (rows 1) (rows 0) (rows 2) (rows 3)
      (columns 1) (columns 0) (columns 2) (columns 3) ?_ ?_
      capacity1 capacity0 capacity2 capacity3 rowPositive blocked10 blocked12 blocked13
    · calc
        _ = rows 0 + rows 1 + rows 2 + rows 3 := by ac_rfl
        _ = total := rowsTotal
    · calc
        _ = columns 0 + columns 1 + columns 2 + columns 3 := by ac_rfl
        _ = total := columnsTotal
  · apply positive_row_contradiction total (rows 2) (rows 0) (rows 1) (rows 3)
      (columns 2) (columns 0) (columns 1) (columns 3) ?_ ?_
      capacity2 capacity0 capacity1 capacity3 rowPositive blocked20 blocked21 blocked23
    · calc
        _ = rows 0 + rows 1 + rows 2 + rows 3 := by ac_rfl
        _ = total := rowsTotal
    · calc
        _ = columns 0 + columns 1 + columns 2 + columns 3 := by ac_rfl
        _ = total := columnsTotal
  · apply positive_row_contradiction total (rows 3) (rows 0) (rows 1) (rows 2)
      (columns 3) (columns 0) (columns 1) (columns 2) ?_ ?_
      capacity3 capacity0 capacity1 capacity2 rowPositive blocked30 blocked31 blocked32
    · calc
        _ = rows 0 + rows 1 + rows 2 + rows 3 := by ac_rfl
        _ = total := rowsTotal
    · calc
        _ = columns 0 + columns 1 + columns 2 + columns 3 := by ac_rfl
        _ = total := columnsTotal

/-- The first eligible edge is explicit finite data.  Failure is ruled out
by the capacity lemma; it is not converted into a chosen existential witness. -/
def nextStep (total : Nat) (rows columns : Masses)
    (margins : Margins total rows columns) (positive : 0 < total) :
    {edge : Fin 4 × Fin 4 // Eligible total rows columns edge} :=
  match found : candidateEdges.find? (fun edge => decide (Eligible total rows columns edge)) with
  | some edge => ⟨edge, of_decide_eq_true
      (List.find?_some (p := fun candidate => decide (Eligible total rows columns candidate)) found)⟩
  | none => by
      have blocked : forall edge, ¬ Eligible total rows columns edge := by
        intro edge valid
        have absent := (List.find?_eq_none.mp found) edge (candidateEdges_complete edge)
        exact absent (decide_eq_true valid)
      exact False.elim (no_step_impossible total rows columns margins positive blocked)

def decrementAt (masses : Masses) (selected : Fin 4) : Masses :=
  fun label => if label = selected then masses label - 1 else masses label

theorem decrementAt_recover (masses : Masses) (selected : Fin 4) (positive : 0 < masses selected)
    (label : Fin 4) :
    decrementAt masses selected label + (if label = selected then 1 else 0) = masses label := by
  by_cases same : label = selected
  · subst label
    simp only [decrementAt]
    exact Nat.sub_add_cancel positive
  · simp only [decrementAt, if_neg same, Nat.add_zero]

private theorem sum4_singleton (selected : Fin 4) :
    sum4 (fun label => if label = selected then 1 else 0) = 1 := by
  rcases label_cases selected with same | same | same | same <;> subst selected <;> decide +kernel

theorem sum4_addAt (masses : Masses) (selected : Fin 4) :
    sum4 (fun label => masses label + (if label = selected then 1 else 0)) = sum4 masses + 1 := by
  rw [sum4_add, sum4_singleton]

theorem sum4_decrementAt (masses : Masses) (selected : Fin 4) (positive : 0 < masses selected) :
    sum4 (decrementAt masses selected) + 1 = sum4 masses := by
  rw [← sum4_addAt]
  exact sum4_congr _ _ (decrementAt_recover masses selected positive)

/-- One eligible unit leaves another normalized feasible margin problem.
Each strict untouched inequality supplies exactly the lost total unit. -/
theorem remainingMargins (total : Nat) (rows columns : Masses)
    (margins : Margins (total + 1) rows columns)
    (edge : Fin 4 × Fin 4) (eligible : Eligible (total + 1) rows columns edge) :
    Margins total (decrementAt rows edge.1) (decrementAt columns edge.2) := by
  refine ⟨?_, ?_, ?_⟩
  · have recovered := sum4_decrementAt rows edge.1 eligible.2.1
    rw [margins.rows_total] at recovered
    omega
  · have recovered := sum4_decrementAt columns edge.2 eligible.2.2.1
    rw [margins.columns_total] at recovered
    omega
  · intro label
    have bounded := margins.capacity label
    by_cases atRow : label = edge.1
    · have awayColumn : label ≠ edge.2 := fun same => eligible.1 (atRow.symm.trans same)
      have positive : 0 < rows label := atRow.symm ▸ eligible.2.1
      simp only [decrementAt, if_pos atRow, if_neg awayColumn]
      omega
    · by_cases atColumn : label = edge.2
      · have positive : 0 < columns label := atColumn.symm ▸ eligible.2.2.1
        simp only [decrementAt, if_neg atRow, if_pos atColumn]
        omega
      · have slack := eligible.2.2.2 label atRow atColumn
        simp only [decrementAt, if_neg atRow, if_neg atColumn]
        omega

def addEdge (cells : Cells) (edge : Fin 4 × Fin 4) : Cells :=
  fun row column => cells row column + (if row = edge.1 then (if column = edge.2 then 1 else 0) else 0)

private theorem addEdge_row_sum (cells : Cells) (edge : Fin 4 × Fin 4) (row : Fin 4) :
    sum4 (addEdge cells edge row) = sum4 (cells row) + (if row = edge.1 then 1 else 0) := by
  change sum4 (fun column => cells row column +
    (if row = edge.1 then (if column = edge.2 then 1 else 0) else 0)) = _
  by_cases same : row = edge.1
  · simp only [if_pos same]
    exact sum4_addAt (cells row) edge.2
  · simp only [if_neg same, Nat.add_zero]

private theorem addEdge_column_sum (cells : Cells) (edge : Fin 4 × Fin 4) (column : Fin 4) :
    sum4 (fun row => addEdge cells edge row column) =
      sum4 (fun row => cells row column) + (if column = edge.2 then 1 else 0) := by
  by_cases same : column = edge.2
  · simp only [addEdge, if_pos same]
    exact sum4_addAt (fun row => cells row column) edge.1
  · have unchanged : forall row, addEdge cells edge row column = cells row column := by
      intro row
      simp only [addEdge, if_neg same, ite_self, Nat.add_zero]
    simp only [if_neg same, Nat.add_zero]
    exact sum4_congr _ _ unchanged

/-- Construct the exact table for *every* supplied natural margin instance
satisfying the four capacity inequalities.  The total is the recursion measure,
not a searched denominator cutoff or a hidden-variable cardinality bound. -/
def transport : (total : Nat) → (rows columns : Masses) →
    Margins total rows columns → Transportation rows columns
  | 0, rows, columns, margins =>
      { cells := fun _ _ => 0
        row_sum := by
          intro row
          have bounded := le_sum4 rows row
          rw [margins.rows_total] at bounded
          have zero := Nat.eq_zero_of_le_zero bounded
          exact zero.symm
        column_sum := by
          intro column
          have bounded := le_sum4 columns column
          rw [margins.columns_total] at bounded
          have zero := Nat.eq_zero_of_le_zero bounded
          exact zero.symm
        diagonal_zero := fun _ => rfl }
  | total + 1, rows, columns, margins =>
      let selected := nextStep (total + 1) rows columns margins (Nat.succ_pos total)
      let residual := transport total (decrementAt rows selected.val.1) (decrementAt columns selected.val.2)
        (remainingMargins total rows columns margins selected.val selected.property)
      { cells := addEdge residual.cells selected.val
        row_sum := by
          intro row
          rw [addEdge_row_sum, residual.row_sum]
          exact decrementAt_recover rows selected.val.1 selected.property.2.1 row
        column_sum := by
          intro column
          rw [addEdge_column_sum, residual.column_sum]
          exact decrementAt_recover columns selected.val.2 selected.property.2.2.1 column
        diagonal_zero := by
          intro label
          have excluded : ¬ (label = selected.val.1 ∧ label = selected.val.2) := by
            rintro ⟨atRow, atColumn⟩
            exact selected.property.1 (atRow.symm.trans atColumn)
          by_cases atRow : label = selected.val.1
          · have awayColumn : label ≠ selected.val.2 := fun same => excluded ⟨atRow, same⟩
            simp only [addEdge, residual.diagonal_zero, if_pos atRow, if_neg awayColumn, Nat.add_zero]
          · simp only [addEdge, residual.diagonal_zero, if_neg atRow, Nat.add_zero] }

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
