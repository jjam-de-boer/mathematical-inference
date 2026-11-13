import Thesis.Causality.IntegerCarryLoops

namespace Thesis.Causality.Examples.IntegerCarryLoops

open Causality.IntegerEquations
open Probability

/-!
# Carry-loop direction regressions

For x-y = 1, the nonzero carry 1 returns to itself on digit (0,1),
then reaches zero on digit (1,0). Their order is least significant first:
the concatenated word represents (2,1), and the direction theorem computes
h = (1,1). Adding any natural multiple of h preserves the equation.

The final examples check the two essential positivity boundaries. An empty
loop contributes no direction even with a positive suffix; a nonempty
zero-only loop with an empty suffix contributes none either. In particular,
the zero carry's padding loop does not prove that x = 1 is unbounded.

Only supplied, tiny words are normalized in the kernel. This module does
not run a loop search, a coordinate classifier, or a Petri solver.
-/

def difference : System 1 2 where
  coefficients := fun _ index => if index = 0 then 1 else -1
  rhs := fun _ => 1

def cycleDigit : Digit 2 := vectorOfFn (fun index => if index = 0 then 0 else 1)
def suffixDigit : Digit 2 := vectorOfFn (fun index => if index = 0 then 1 else 0)

theorem nonzero_carry_loop :
    FiniteLabelledReachability.run difference.advance difference.initialCarry [cycleDigit] =
      some difference.initialCarry := by decide +kernel

theorem suffix_accepted :
    FiniteLabelledReachability.run difference.advance difference.initialCarry [suffixDigit] =
      some difference.zeroCarry := by decide +kernel

theorem concatenated_word_accepted :
    FiniteLabelledReachability.run difference.advance difference.initialCarry ([cycleDigit] ++ [suffixDigit]) =
      some difference.zeroCarry := by
  rw [FiniteLabelledReachability.run_append, nonzero_carry_loop, Option.bind_some]
  exact suffix_accepted

theorem concatenated_values :
    decodeWord ([cycleDigit] ++ [suffixDigit]) 0 = 2 ∧
      decodeWord ([cycleDigit] ++ [suffixDigit]) 1 = 1 := by decide +kernel

def direction : Fin 2 → Nat := loopDirection [cycleDigit] [suffixDigit]

theorem direction_values : direction 0 = 1 ∧ direction 1 = 1 := by decide +kernel

theorem direction_satisfies : difference.homogeneous.Satisfies direction :=
  difference.loopDirection_satisfies nonzero_carry_loop suffix_accepted

theorem direction_positive : 0 < direction 0 :=
  loopDirection_pos (by intro impossible; cases impossible) 0 (by decide +kernel)

/-- Every multiple is admitted by the general equation-preservation
theorem; no finite regression list is substituted for this quantifier. -/
theorem shifted_solutions (multiple : Nat) :
    difference.Satisfies (fun index => decodeWord [suffixDigit] index + multiple * direction index) :=
  difference.satisfies_add_homogeneous (difference.run_satisfies suffix_accepted) direction_satisfies multiple

theorem empty_loop_zero : loopDirection [] [suffixDigit] = (fun _ => 0) :=
  loopDirection_nil [suffixDigit]

def fixed : System 1 1 where
  coefficients := fun _ _ => 1
  rhs := fun _ => 1

def zeroDigit : Digit 1 := vectorOfFn (fun _ => 0)

theorem zero_padding_loop :
    FiniteLabelledReachability.run fixed.advance fixed.zeroCarry [zeroDigit] =
      some fixed.zeroCarry := by decide +kernel

theorem padding_direction_satisfies : fixed.homogeneous.Satisfies (loopDirection [zeroDigit] []) :=
  fixed.loopDirection_satisfies zero_padding_loop rfl

theorem padding_direction_not_positive : ¬ 0 < loopDirection [zeroDigit] [] 0 := by decide +kernel

end Thesis.Causality.Examples.IntegerCarryLoops
