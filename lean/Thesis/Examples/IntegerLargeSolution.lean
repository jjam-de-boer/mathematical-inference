import Thesis.Causality.IntegerLargeSolution

namespace Thesis.Causality.Examples.IntegerLargeSolution

open Causality.IntegerEquations

/-!
# Large-coordinate direction regressions

Small kernel computations exercise the actual returned direction at the
threshold 2^N, including an empty row family. The constrained example fixes
the first coordinate at zero and grows the second, so the selected index
and the nonnegative homogeneous equation both matter.

The signed, nonzero-right-hand-side example uses the general certificate
without normalizing its longer padded word. These are distinct checks:
the small examples execute the witness construction in the kernel, while
the signed example checks the general theorem's stated interface.
No large execution benchmark or coordinate-classification claim is made.
-/

theorem zero_fuel_roundtrip :
    decodeWord (binaryWord 0 (fun _ : Fin 1 => 0)) = (fun _ => 0) :=
  decodeWord_binaryWord 0 _ (fun _ => Nat.le_refl 0)

theorem padding_roundtrip : decodeWord (binaryWord 7 (fun _ : Fin 1 => 5)) 0 = 5 :=
  congrFun (decodeWord_binaryWord 7 _ (fun _ => by decide +kernel)) 0

def free : System 0 1 where
  coefficients := fun row => Fin.elim0 row
  rhs := Fin.elim0

def freeValues : Fin 1 → Nat := fun _ => 2

def freeDirection : {direction : Fin 1 → Nat // free.homogeneous.Satisfies direction ∧ 0 < direction 0} :=
  free.directionOfLargeSolution freeValues (fun row => Fin.elim0 row) 0 (by decide +kernel)

theorem threshold_is_inclusive : 2 ^ free.carryWitness.enumeration.length = freeValues 0 := by decide +kernel
theorem free_direction_computed : freeDirection.val 0 = 1 := by decide +kernel

def fixedFirst : System 1 2 where
  coefficients := fun _ index => if index = 0 then 1 else 0
  rhs := fun _ => 0

def selectedValues : Fin 2 → Nat := fun index => if index = 0 then 0 else 8

theorem selected_values_satisfy : fixedFirst.Satisfies selectedValues := by
  unfold System.Satisfies
  decide +kernel

def selectedDirection :
    {direction : Fin 2 → Nat // fixedFirst.homogeneous.Satisfies direction ∧ 0 < direction 1} :=
  fixedFirst.directionOfLargeSolution selectedValues selected_values_satisfy 1 (by decide +kernel)

theorem selected_direction_computed : selectedDirection.val 0 = 0 ∧ selectedDirection.val 1 = 4 := by decide +kernel
theorem selected_direction_satisfies : fixedFirst.homogeneous.Satisfies selectedDirection.val := selectedDirection.property.1
theorem selected_direction_positive : 0 < selectedDirection.val 1 := selectedDirection.property.2

def difference : System 1 2 where
  coefficients := fun _ index => if index = 0 then 1 else -1
  rhs := fun _ => 1

def differenceValues : Fin 2 → Nat := fun index => if index = 0 then 129 else 128

theorem signed_rhs_direction : ∃ direction : Fin 2 → Nat,
    difference.homogeneous.Satisfies direction ∧ 0 < direction 1 := by
  have valid : difference.Satisfies differenceValues := by
    unfold System.Satisfies
    decide +kernel
  have large : 2 ^ difference.carryWitness.enumeration.length ≤ differenceValues 1 := by decide +kernel
  let witness := difference.directionOfLargeSolution differenceValues valid 1 large
  exact ⟨witness.val, witness.property⟩

end Thesis.Causality.Examples.IntegerLargeSolution
