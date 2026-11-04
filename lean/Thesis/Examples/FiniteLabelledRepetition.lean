import Thesis.Causality.FiniteLabelledRepetition

namespace Thesis.Causality.Examples.FiniteLabelledRepetition

open Probability
open Causality.FiniteLabelledReachability

/-!
# Literal finite-word repetition regressions

A two-state latch first leaves its starting state and only then repeats.
Its computed factorization must retain that initial transition, the actual
one-label loop, and the remaining suffix. A word with exactly N transitions
also suffices: the argument counts N+1 visited states, not N+1 transitions.

A one-state example uses natural-number labels. Its factors retain those
literal labels even though the label type is infinite and the transition
function ignores their values. Repetition uses only finite state equality.

These small examples normalize the actual witness-producing construction
in the kernel. They do not exercise a coordinate classifier or Petri search.
-/

def latch (state : Fin 2) (label : Bool) : Option (Fin 2) :=
  some (if label then 1 else state)

def delayed : WordRepetition latch 0 1 [true, false, true] (FiniteWitness.fin 2).enumeration.length :=
  factorRepetition (FiniteWitness.fin 2) latch 0 1 [true, false, true]
    (by decide +kernel) (by decide +kernel)

theorem delayed_factors :
    delayed.initial = [true] ∧ delayed.cycle = [false] ∧ delayed.suffix = [true] := by decide +kernel

theorem delayed_middle : delayed.middle = 1 := by decide +kernel

theorem literal_word_retained :
    [true, false, true] = delayed.initial ++ (delayed.cycle ++ delayed.suffix) := delayed.word_eq

theorem checked_loop : run latch delayed.middle delayed.cycle = some delayed.middle := delayed.cycle_run

theorem loop_ends_by_carrier_bound : delayed.initial.length + delayed.cycle.length ≤ 2 := delayed.within

def exactLength : WordRepetition latch 0 1 [true, false] (FiniteWitness.fin 2).enumeration.length :=
  factorRepetition (FiniteWitness.fin 2) latch 0 1 [true, false]
    (by decide +kernel) (by decide +kernel)

theorem exactly_n_transitions_suffice :
    exactLength.initial = [true] ∧ exactLength.cycle = [false] ∧ exactLength.suffix = [] := by decide +kernel

def hold (state : Fin 1) (_label : Nat) : Option (Fin 1) := some state

def payload : WordRepetition hold 0 0 [10, 20, 30] (FiniteWitness.fin 1).enumeration.length :=
  factorRepetition (FiniteWitness.fin 1) hold 0 0 [10, 20, 30]
    (by decide +kernel) (by decide +kernel)

theorem natural_labels_retained :
    payload.initial = [] ∧ payload.cycle = [10] ∧ payload.suffix = [20, 30] := by decide +kernel

theorem payload_cycle_nonempty : payload.cycle ≠ [] := payload.nonempty

end Thesis.Causality.Examples.FiniteLabelledRepetition
