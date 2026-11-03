import Thesis.Probability.IntegerNullspace

namespace Thesis.Causality.IntegerEquations

open Probability
open IntegerLinearAlgebra

/-!
# Signed linear equations with natural-number unknowns

The coefficients and right-hand sides are arbitrary integers. Unknowns are
natural numbers, with no supplied upper bound. These are exact integer
constraints, not a rational relaxation or a Petri firing-order criterion.
The finite sum and binary decomposition lemmas below support the later
carry automaton; they assume neither solvability nor a search oracle.

The coefficient budget is computed from all rows and their right-hand
sides. It bounds every digit contribution and the initial carry. Empty
row and variable families retain their usual vacuous equations and sums.
-/

structure System (rows variables : Nat) where
  coefficients : Fin rows → Fin variables → Int
  rhs : Fin rows → Int

variable {rows variables : Nat}

def rowValue (coefficients : Fin variables → Int) (values : Fin variables → Nat) : Int :=
  sum ((List.finRange variables).map (fun index => coefficients index * (values index : Int)))

def System.Satisfies (system : System rows variables) (values : Fin variables → Nat) : Prop :=
  ∀ row, rowValue (system.coefficients row) values = system.rhs row

theorem rowValue_zero (coefficients : Fin variables → Int) : rowValue coefficients (fun _ => 0) = 0 := by
  simpa only [rowValue, Int.natCast_zero, Int.mul_zero] using sum_map_zero (List.finRange variables)

theorem rowValue_add (coefficients : Fin variables → Int) (left right : Fin variables → Nat) :
    rowValue coefficients (fun index => left index + right index) =
      rowValue coefficients left + rowValue coefficients right := by
  simp only [rowValue, Int.natCast_add, Int.mul_add]
  exact sum_map_add _ _ _

theorem rowValue_scale (coefficients : Fin variables → Int) (factor : Nat) (values : Fin variables → Nat) :
    rowValue coefficients (fun index => factor * values index) = (factor : Int) * rowValue coefficients values := by
  simp only [rowValue, Int.natCast_mul]
  have commute : (fun index => coefficients index * ((factor : Int) * (values index : Int))) =
      (fun index => (factor : Int) * (coefficients index * (values index : Int))) := by
    funext index
    exact Int.mul_left_comm _ _ _
  rw [commute]
  exact sum_map_mul_left _ _ _

/-- One binary digit and the remaining higher digits reconstruct a whole
row, including negative coefficients. -/
theorem rowValue_binary (coefficients : Fin variables → Int) (values : Fin variables → Nat) :
    rowValue coefficients values = rowValue coefficients (fun index => values index % 2) +
      2 * rowValue coefficients (fun index => values index / 2) := by
  have splitValues : values = (fun index => values index % 2 + 2 * (values index / 2)) := by
    funext index
    omega
  calc
    rowValue coefficients values = rowValue coefficients
        (fun index => values index % 2 + 2 * (values index / 2)) := congrArg (rowValue coefficients) splitValues
    _ = _ := by rw [rowValue_add, rowValue_scale]; rfl

private theorem member_le_sum (values : List Nat) (value : Nat) (listed : value ∈ values) : value ≤ values.sum := by
  induction values with
  | nil => cases listed
  | cons head tail ih =>
      rcases List.mem_cons.mp listed with same | later
      · subst value
        simp only [List.sum_cons]
        omega
      · have earlier := ih later
        simp only [List.sum_cons]
        omega

def rowWeight (coefficients : Fin variables → Int) : Nat :=
  ((List.finRange variables).map (fun index => (coefficients index).natAbs)).sum

def System.budget (system : System rows variables) : Nat :=
  ((List.finRange rows).map (fun row => rowWeight (system.coefficients row) + (system.rhs row).natAbs)).sum

theorem System.rowWeight_le_budget (system : System rows variables) (row : Fin rows) :
    rowWeight (system.coefficients row) ≤ system.budget := by
  have bound := member_le_sum _ _ (List.mem_map_of_mem (f := fun row =>
    rowWeight (system.coefficients row) + (system.rhs row).natAbs) (List.mem_finRange row))
  exact Nat.le_trans (Nat.le_add_right _ _) bound

theorem System.rhs_abs_le_budget (system : System rows variables) (row : Fin rows) :
    (system.rhs row).natAbs ≤ system.budget := by
  have bound := member_le_sum _ _ (List.mem_map_of_mem (f := fun row =>
    rowWeight (system.coefficients row) + (system.rhs row).natAbs) (List.mem_finRange row))
  change rowWeight (system.coefficients row) + (system.rhs row).natAbs ≤ system.budget at bound
  omega

/-- A signed coefficient lies between its two natural absolute bounds. -/
theorem coefficient_bounds (value : Int) : -(value.natAbs : Int) ≤ value ∧ value ≤ (value.natAbs : Int) := by
  have upper := Int.le_natAbs (a := value)
  have lower := Int.le_natAbs (a := -value)
  rw [Int.natAbs_neg] at lower
  -- Construct the conjunction directly; arithmetic reflection receives
  -- only decidable integer comparisons, without propositional EM.
  constructor <;> omega

private theorem sum_digit_bounds (indices : List α) (coefficients : α → Int) (digits : α → Fin 2) :
    -(((indices.map (fun index => (coefficients index).natAbs)).sum : Nat) : Int) ≤
      sum (indices.map (fun index => coefficients index * (digits index).val)) ∧
    sum (indices.map (fun index => coefficients index * (digits index).val)) ≤
      (((indices.map (fun index => (coefficients index).natAbs)).sum : Nat) : Int) := by
  induction indices with
  | nil => exact ⟨Int.le_refl _, Int.le_refl _⟩
  | cons head tail ih =>
      have bound := coefficient_bounds (coefficients head)
      have bit := (digits head).isLt
      simp only [List.map_cons, List.sum_cons, Int.natCast_add]
      change -((coefficients head).natAbs +
          (((tail.map (fun index => (coefficients index).natAbs)).sum : Nat) : Int)) ≤
          coefficients head * ((digits head).val : Int) +
            sum (tail.map (fun index => coefficients index * (digits index).val)) ∧
        coefficients head * ((digits head).val : Int) +
            sum (tail.map (fun index => coefficients index * (digits index).val)) ≤
          (coefficients head).natAbs +
            (((tail.map (fun index => (coefficients index).natAbs)).sum : Nat) : Int)
      by_cases zero : (digits head).val = 0
      · simp only [zero, Int.natCast_zero, Int.mul_zero]
        constructor <;> omega
      · have one : (digits head).val = 1 := by omega
        simp only [one, Int.natCast_one, Int.mul_one]
        constructor <;> omega

theorem digit_row_bounds (coefficients : Fin variables → Int) (digits : Fin variables → Fin 2) :
    -(rowWeight coefficients : Int) ≤ rowValue coefficients (fun index => (digits index).val) ∧
      rowValue coefficients (fun index => (digits index).val) ≤ (rowWeight coefficients : Int) :=
  sum_digit_bounds (List.finRange variables) coefficients digits

/-- This fuel is used only to encode an already supplied solution in the
completeness proof. The solver itself searches the bounded carry graph. -/
def encodingFuel (values : Fin variables → Nat) : Nat := ((List.finRange variables).map values).sum

theorem le_encodingFuel (values : Fin variables → Nat) (index : Fin variables) : values index ≤ encodingFuel values :=
  member_le_sum _ _ (List.mem_map_of_mem (f := values) (List.mem_finRange index))

end Thesis.Causality.IntegerEquations
