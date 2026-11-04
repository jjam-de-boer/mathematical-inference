import Thesis.Causality.IntegerCoordinateClassification

namespace Thesis.Causality.Examples.IntegerCoordinateClassification

open Causality.IntegerEquations

/-!
# Exact coordinate-classification regressions

The small examples run the actual classifier in the kernel, retaining its
computed solution and direction data. They check all three result kinds,
an empty row family, and two different coordinate kinds in the same system.

The inconsistent constant equation has positive homogeneous directions:
it must nevertheless be reported as infeasible. The signed equation
x - 2*y = 1 has a positive direction whose first coordinate cannot be one.
It checks the shift u + e_j, rather than the incorrect restriction h_j = 1.
The universal consequences below use the returned certificates and apply
above arbitrarily large thresholds, without normalizing large test inputs.
No runtime pilot, Petri test, or native execution axiom is introduced.
-/

def noBase : System 1 1 where
  coefficients := fun _ _ => 0
  rhs := fun _ => 1

theorem positive_direction_without_base : (noBase.positiveDirectionSystem 0).isFeasible = true := by
  decide +kernel

theorem infeasibility_reported_first : (noBase.classifyCoordinate 0).kind = .infeasible := by
  decide +kernel

theorem infeasible_for_every_candidate : ¬ ∃ values, noBase.Satisfies values :=
  (noBase.classifyCoordinate 0).infeasible_iff.mp infeasibility_reported_first

def fixed : System 1 1 where
  coefficients := fun _ _ => 1
  rhs := fun _ => 2

def fixedReport := fixed.classifyCoordinate 0

theorem fixed_coordinate_bounded : fixedReport.kind = .bounded := by decide +kernel

theorem bounded_witness_computed :
    (match fixedReport with
      | .bounded base _ _ => some (base 0, fixed.coordinateBound)
      | _ => none) = some (2, 128) := by decide +kernel

theorem fixed_has_solution_and_bound :
    (∃ values, fixed.Satisfies values) ∧ fixed.CoordinateBounded 0 :=
  fixedReport.bounded_iff.mp fixed_coordinate_bounded

def mixed : System 1 2 where
  coefficients := fun _ index => if index = 0 then 1 else 0
  rhs := fun _ => 0

theorem first_coordinate_bounded : (mixed.classifyCoordinate 0).kind = .bounded := by decide +kernel
theorem second_coordinate_unbounded : (mixed.classifyCoordinate 1).kind = .unbounded := by decide +kernel

def signed : System 1 2 where
  coefficients := fun _ index => if index = 0 then 1 else -2
  rhs := fun _ => 1

def signedReport := signed.classifyCoordinate 0

theorem signed_coordinate_unbounded : signedReport.kind = .unbounded := by decide +kernel

theorem base_and_direction_computed :
    (match signedReport with
      | .unbounded base _ direction =>
          some (decide (base 0 = 1 + 2 * base 1), decide (direction.val 0 = 2 * direction.val 1),
            decide (2 ≤ direction.val 0))
      | _ => none) = some (true, true, true) := by decide +kernel

/-- This equation has no positive homogeneous direction with h_0 = 1.
The classifier still succeeds, since it searches all positive natural h_0. -/
theorem unit_growth_would_miss_this_case (direction : signed.PositiveDirection 0) :
    2 ≤ direction.val 0 := by
  have equation := direction.property.1 (0 : Fin 1)
  have positive := direction.property.2
  change 1 * (direction.val 0 : Int) + (-2 * (direction.val 1 : Int) + 0) = 0 at equation
  simp only [Int.one_mul, Int.add_zero] at equation
  omega

theorem every_threshold_has_a_solution : signed.CoordinateUnbounded 0 :=
  signedReport.unbounded_iff.mp signed_coordinate_unbounded

def free : System 0 1 where
  coefficients := fun row => Fin.elim0 row
  rhs := Fin.elim0

theorem empty_row_family_unbounded : (free.classifyCoordinate 0).kind = .unbounded := by decide +kernel

end Thesis.Causality.Examples.IntegerCoordinateClassification
