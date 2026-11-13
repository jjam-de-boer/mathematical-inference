import Thesis.Causality.IntegerFeasibility

namespace Thesis.Causality.Examples.IntegerFeasibility

open Causality.IntegerEquations

/-!
# Exact integer-feasibility regressions

The small one-row examples normalize the actual solver in the kernel,
including its returned natural witness. They distinguish integral from
rational feasibility, signed data from nonnegative unknowns, and empty
dimensions from a nonzero constant equation. No native execution axiom or
assumed candidate bound is used.

The coupled two-row example separately exercises the general exactness
theorem without normalizing a larger carry-state table during compilation.
That separation keeps a mathematical regression from becoming a large
runtime benchmark disguised as a proof.
-/

def singleEquation (coefficient rhs : Int) : System 1 1 where
  coefficients := fun _ _ => coefficient
  rhs := fun _ => rhs

def firstSolution (system : System 1 1) : Option Nat :=
  match system.solve with
  | .feasible values _ => some (values 0)
  | .infeasible _ => none

theorem integral_witness_computed : firstSolution (singleEquation 2 2) = some 1 := by decide +kernel

/-- The rational solution 1/2 must not count as a natural solution. -/
theorem rational_relaxation_rejected : (singleEquation 2 1).isFeasible = false := by decide +kernel

theorem signed_witness_computed : firstSolution (singleEquation (-2) (-4)) = some 2 := by decide +kernel

/-- Signed input data do not allow a negative value for an unknown. -/
theorem negative_unknown_rejected : (singleEquation 1 (-1)).isFeasible = false := by decide +kernel

def emptyEquations : System 0 0 where
  coefficients := fun row => Fin.elim0 row
  rhs := Fin.elim0

theorem empty_system_accepted : emptyEquations.isFeasible = true := by decide +kernel

def noVariables (rhs : Int) : System 1 0 where
  coefficients := fun _ => Fin.elim0
  rhs := fun _ => rhs

theorem zero_constant_accepted : (noVariables 0).isFeasible = true := by decide +kernel
theorem nonzero_constant_rejected : (noVariables 1).isFeasible = false := by decide +kernel

def noRows : System 0 1 where
  coefficients := fun row => Fin.elim0 row
  rhs := Fin.elim0

theorem unconstrained_variable_accepted : noRows.isFeasible = true := by decide +kernel

/-- x-y = 1 and x+y = 5 have the natural solution (3,2).
Both rows constrain the same vector; solving each row independently would
not establish this simultaneous-system claim. -/
def coupled : System 2 2 where
  coefficients := fun row column => if row = 0 ∧ column = 1 then -1 else 1
  rhs := fun row => if row = 0 then 1 else 5

theorem simultaneous_rows_accepted : coupled.isFeasible = true := by
  apply coupled.isFeasible_exact.mpr
  refine ⟨fun index => if index = 0 then 3 else 2, ?_⟩
  unfold System.Satisfies
  decide +kernel

/-- This consequence quantifies over every natural candidate, not over a
finite list used only for the small normalization regression above. -/
theorem no_integral_half : ¬ ∃ values, (singleEquation 2 1).Satisfies values :=
  (singleEquation 2 1).isFeasible_false_exact.mp rational_relaxation_rejected

end Thesis.Causality.Examples.IntegerFeasibility
