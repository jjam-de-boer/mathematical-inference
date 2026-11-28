import Thesis.Causality.IntegerEquations
import Thesis.Probability.Construction

namespace Thesis.Causality.IntegerEquations

open Probability IntegerLinearAlgebra

/-!
# Compiling equations with named natural unknowns

A row lists signed terms, allowing repeated names. The compiler assigns
one column to each name that occurs and omits rows whose two sides are
identically zero by inspection. A constant contradiction remains a row.
Names used only with coefficient zero still have columns, so a caller can
ask about an unknown even when the equations leave it unconstrained.

Both translations of assignments are explicit. The correctness theorem
preserves row satisfaction in each direction and justifies using the
integer solver on the compact system.
-/

structure NamedRow (α : Type) where
  terms : List (α × Int)
  rhs : Int

/-- On the literal finite index list, selecting one index takes its value
exactly once, including for signed values. -/
theorem sum_fin_single {n : Nat} (column : Fin n) (term : Fin n → Int) :
    sum ((List.finRange n).map (fun other => if other = column then term other else 0)) =
      term column := by
  induction n with
  | zero => exact Fin.elim0 column
  | succ n ih =>
      refine Fin.cases ?_ (fun column => ?_) column
      · simp only [List.finRange_succ, List.map_cons, List.map_map]
        change term 0 + sum ((List.finRange n).map (fun _ => (0 : Int))) = _
        rw [sum_map_zero, Int.add_zero]
      · have off : (0 : Fin (n + 1)) ≠ column.succ := Ne.symm (Fin.succ_ne_zero column)
        simp only [List.finRange_succ, List.map_cons, List.map_map, Function.comp_def,
          if_neg off, Fin.succ_inj]
        change 0 + sum ((List.finRange n).map
          (fun other => if other = column then term other.succ else 0)) = _
        rw [Int.zero_add, ih]

namespace NamedRow

variable {α : Type}

def value (row : NamedRow α) (assignment : α → Nat) : Int :=
  sum (row.terms.map (fun (name, weight) => weight * (assignment name : Int)))

def Satisfies (rows : List (NamedRow α)) (assignment : α → Nat) : Prop :=
  ∀ row ∈ rows, row.value assignment = row.rhs

private def redundant (row : NamedRow α) : Bool :=
  decide (row.rhs = 0) && row.terms.all (fun term => decide (term.2 = 0))

private theorem redundant_exact {row : NamedRow α} (trivialRow : row.redundant = true)
    (assignment : α → Nat) : row.value assignment = row.rhs := by
  have facts := Bool.and_eq_true_iff.mp trivialRow
  have right := of_decide_eq_true facts.1
  have zero : row.terms.map (fun (name, weight) => weight * (assignment name : Int)) =
      row.terms.map (fun _ => (0 : Int)) := by
    apply List.map_congr_left
    intro term member
    have weight := of_decide_eq_true ((List.all_eq_true.mp facts.2) term member)
    change term.2 * (assignment term.1 : Int) = 0
    rw [weight, Int.zero_mul]
  unfold value
  rw [zero, sum_map_zero, right]

private def kept (rows : List (NamedRow α)) : List (NamedRow α) :=
  rows.filter (fun row => !row.redundant)

variable [DecidableEq α]

def columns (rows : List (NamedRow α)) : List α :=
  deduplicate (rows.flatMap (fun row => row.terms.map Prod.fst))

theorem mem_columns {rows : List (NamedRow α)} {row : NamedRow α} {term : α × Int}
    (rowIn : row ∈ rows) (termIn : term ∈ row.terms) : term.1 ∈ columns rows :=
  (mem_deduplicate _ _).mpr (List.mem_flatMap.mpr ⟨row, rowIn, List.mem_map_of_mem termIn⟩)

/-- Look up a column using only literal equality of the supplied names. -/
def columnIndex (rows : List (NamedRow α)) (name : α) : Option (Fin (columns rows).length) :=
  let index := (columns rows).findIdx (fun key => decide (key = name))
  if inRange : index < (columns rows).length then some ⟨index, inRange⟩ else none

theorem columnIndex_of_mem (rows : List (NamedRow α)) {name : α} (member : name ∈ columns rows) :
    ∃ index, columnIndex rows name = some index ∧ (columns rows).get index = name := by
  have bound := List.findIdx_lt_length_of_exists
    (p := fun key : α => decide (key = name)) ⟨name, member, decide_eq_true rfl⟩
  refine ⟨⟨_, bound⟩, by simp only [columnIndex, dif_pos bound], ?_⟩
  exact of_decide_eq_true (List.findIdx_getElem (w := bound))

theorem columnIndex_get {rows : List (NamedRow α)} {name : α} {index : Fin (columns rows).length}
    (located : columnIndex rows name = some index) : (columns rows).get index = name := by
  simp only [columnIndex] at located
  split at located
  · rename_i bound
    have same := Option.some.inj located
    subst index
    exact of_decide_eq_true (List.findIdx_getElem (w := bound))
  · cases located

def encode (rows : List (NamedRow α)) (assignment : α → Nat) :
    Fin (columns rows).length → Nat :=
  fun index => assignment ((columns rows).get index)

def decode (rows : List (NamedRow α)) (values : Fin (columns rows).length → Nat) :
    α → Nat :=
  fun name => ((columnIndex rows name).map values).getD 0

theorem decode_encode (rows : List (NamedRow α)) (assignment : α → Nat)
    {name : α} (member : name ∈ columns rows) :
    decode rows (encode rows assignment) name = assignment name := by
  obtain ⟨index, located, actual⟩ := columnIndex_of_mem rows member
  simp only [decode, located, Option.map_some, Option.getD_some, encode, actual]

private def termColumn (rows : List (NamedRow α)) (term : α × Int)
    (column : Fin (columns rows).length) : Int :=
  if columnIndex rows term.1 = some column then term.2 else 0

private def coefficients (rows : List (NamedRow α)) (terms : List (α × Int))
    (column : Fin (columns rows).length) : Int :=
  sum (terms.map (fun term => termColumn rows term column))

private theorem rowValue_add_coefficients {n : Nat} (left right : Fin n → Int)
    (values : Fin n → Nat) :
    rowValue (fun index => left index + right index) values =
      rowValue left values + rowValue right values := by
  simp only [rowValue, Int.add_mul]
  exact sum_map_add _ _ _

private theorem rowValue_oneColumn {n : Nat} (column : Fin n) (weight : Int)
    (values : Fin n → Nat) :
    rowValue (fun other => if other = column then weight else 0) values =
      weight * (values column : Int) := by
  unfold rowValue
  rw [← sum_fin_single column (fun other => weight * (values other : Int))]
  congr 1
  apply List.map_congr_left
  intro index _
  by_cases same : index = column
  · simp only [if_pos same]
  · simp only [if_neg same, Int.zero_mul]

private theorem rowValue_terms (rows : List (NamedRow α)) (terms : List (α × Int))
    (values : Fin (columns rows).length → Nat)
    (included : ∀ term ∈ terms, term.1 ∈ columns rows) :
    rowValue (coefficients rows terms) values =
      sum (terms.map (fun (name, weight) => weight * (decode rows values name : Int))) := by
  induction terms with
  | nil =>
      change rowValue (fun _ => 0) values = 0
      simp only [rowValue, Int.zero_mul, sum_map_zero]
  | cons head tail ih =>
      obtain ⟨column, located, _⟩ := columnIndex_of_mem rows (included head (List.Mem.head _))
      change rowValue (fun index => termColumn rows head index + coefficients rows tail index) values =
        head.2 * (decode rows values head.1 : Int) +
          sum (tail.map (fun (name, weight) => weight * (decode rows values name : Int)))
      rw [rowValue_add_coefficients, ih (fun term inside => included term (List.Mem.tail _ inside))]
      simp only [decode, located, Option.map_some, Option.getD_some]
      have columnCoefficients : termColumn rows head =
          (fun index => if index = column then head.2 else 0) := by
        funext index
        simp only [termColumn, located, Option.some.injEq]
        by_cases same : column = index
        · subst index
          rfl
        · simp only [if_neg same, if_neg (Ne.symm same)]
      rw [columnCoefficients, rowValue_oneColumn]

def system (rows : List (NamedRow α)) : System (kept rows).length (columns rows).length where
  coefficients := fun index => coefficients rows ((kept rows).get index).terms
  rhs := fun index => ((kept rows).get index).rhs

/-- The dense solver and the named constraints agree for decoded values.
An omitted row is certified for every assignment by its zero coefficients. -/
theorem system_exact (rows : List (NamedRow α)) (values : Fin (columns rows).length → Nat) :
    (system rows).Satisfies values ↔ Satisfies rows (decode rows values) := by
  constructor
  · intro valid row member
    cases redundantRow : row.redundant
    · have keptMember : row ∈ kept rows :=
        List.mem_filter.mpr ⟨member, by simp only [redundantRow, Bool.not_false]⟩
      obtain ⟨index, actual⟩ := List.mem_iff_get.mp keptMember
      have equation := valid index
      change rowValue (coefficients rows ((kept rows).get index).terms) values = _ at equation
      have right : (system rows).rhs index = row.rhs := congrArg NamedRow.rhs actual
      rw [actual, right, rowValue_terms rows row.terms values (fun _ => mem_columns member)] at equation
      exact equation
    · exact redundant_exact redundantRow _
  · intro valid index
    let row := (kept rows).get index
    have member : row ∈ rows := (List.mem_filter.mp (List.get_mem (kept rows) index)).1
    change rowValue (coefficients rows row.terms) values = row.rhs
    rw [rowValue_terms rows row.terms values (fun _ => mem_columns member)]
    exact valid row member

theorem encode_satisfies {rows : List (NamedRow α)} {assignment : α → Nat}
    (valid : Satisfies rows assignment) : (system rows).Satisfies (encode rows assignment) := by
  apply (system_exact rows _).mpr
  intro row member
  unfold value
  have same : row.terms.map (fun (name, weight) => weight * (decode rows (encode rows assignment) name : Int)) =
      row.terms.map (fun (name, weight) => weight * (assignment name : Int)) := by
    apply List.map_congr_left
    intro term inside
    change term.2 * (decode rows (encode rows assignment) term.1 : Int) = _
    rw [decode_encode rows assignment (mem_columns member inside)]
  rw [same]
  exact valid row member

end NamedRow
end Thesis.Causality.IntegerEquations
