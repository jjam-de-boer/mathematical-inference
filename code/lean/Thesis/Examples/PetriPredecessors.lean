import Thesis.Causality.PetriPredecessors
import Thesis.Causality.IntegerFeasibility

namespace Thesis.Causality.Examples.PetriPredecessors

open Thesis.Causality.PetriNet
open Thesis.Causality.IntegerEquations

/-!
# Predecessor, execution-lifting and balance-equation regressions

The two-place fixture needs tokens in both coordinates. Its least one-step
predecessor reaches the requested first coordinate exactly and overshoots
the second. The tests therefore retain coverability's pointwise meaning,
without confusing it with exact arrival. A smaller source is excluded by
the general necessity theorem, and a two-step word lifts to a larger source
with an explicitly computed endpoint. Empty words and empty place families
are checked separately.

The last fixture consumes one token and produces two. From zero tokens,
the signed balance equation for reaching one token has the natural firing
count one, accepted by the actual integer solver. No nonempty execution
can start, however, so one token is not even coverable. This rules out
using equation feasibility as an execution oracle; it does not refute
Petri reachability decidability. The negative proof covers every finite
word, rather than only an unsuccessful bounded search.
-/

def pair (first second : Nat) : Marking 2 :=
  fun place => if place = 0 then first else second

def transfer : Thesis.Causality.PetriNet 2 1 where
  consume := fun _ => pair 2 1
  produce := fun _ => pair 1 3

def target : Marking 2 := pair 4 2

theorem predecessor_computed :
    (transfer.predecessor 0 target 0, transfer.predecessor 0 target 1) = (5, 1) := by
  decide +kernel

def successor := transfer.fireFromPredecessor 0 target (transfer.predecessor 0 target) (Below.refl _)

theorem successor_computed : (successor.val 0, successor.val 1) = (4, 3) := by decide +kernel

theorem predecessor_firing_checked :
    transfer.check (transfer.predecessor 0 target) [0] successor.val = true :=
  (check_exact transfer _ _ _).mpr (.cons successor.property.1 (.nil _))

theorem successor_covers_target : Below target successor.val := successor.property.2

/-- The first coordinate falls short of the least predecessor. This
excludes every possible successor, not only the displayed candidate. -/
theorem below_minimum_impossible :
    ¬ ∃ after, transfer.Fires (pair 4 1) 0 after ∧ Below target after := by
  intro witness
  have bound := ((predecessor_exact transfer 0 target (pair 4 1)).mpr witness) 0
  change 5 ≤ 4 at bound
  omega

theorem supplied_two_step_execution : transfer.Execution (pair 5 1) [0, 0] (pair 3 5) :=
  (check_exact transfer _ _ _).mp (by decide +kernel)

def lifted := supplied_two_step_execution.lift (pair 8 4) (by
  unfold Below
  decide +kernel)

theorem lifted_endpoint_computed : (lifted.val 0, lifted.val 1) = (6, 8) := by decide +kernel

theorem lifted_execution : transfer.Execution (pair 8 4) [0, 0] lifted.val := lifted.property.1

theorem larger_source_still_covers : transfer.Coverable (pair 8 4) (pair 3 5) :=
  (show transfer.Coverable (pair 5 1) (pair 3 5) from
    ⟨pair 3 5, ⟨[0, 0], supplied_two_step_execution⟩, Below.refl _⟩).mono (by
      unfold Below
      decide +kernel)

def emptyLift := (show transfer.Execution (pair 2 7) [] (pair 2 7) from .nil _).lift
  (pair 6 9) (by unfold Below; decide +kernel)

theorem empty_word_endpoint_computed : (emptyLift.val 0, emptyLift.val 1) = (6, 9) := by decide +kernel

def emptyPlaces : Thesis.Causality.PetriNet 0 1 where
  consume := fun _ => Fin.elim0
  produce := fun _ => Fin.elim0

theorem empty_place_predecessor_fires :
    emptyPlaces.check (emptyPlaces.predecessor 0 Fin.elim0) [0] Fin.elim0 = true := by
  decide +kernel

def needsSeed : Thesis.Causality.PetriNet 1 1 where
  consume := fun _ _ => 1
  produce := fun _ _ => 2

def tokens (count : Nat) : Marking 1 := fun _ => count

/-- This matrix and right-hand side use the actual fixture's consumption,
production and endpoints. They are not an unrelated satisfiable equation. -/
def balanceSystem : System 1 1 where
  coefficients := fun place transition =>
    (needsSeed.produce transition place : Int) - (needsSeed.consume transition place : Int)
  rhs := fun place => (tokens 1 place : Int) - (tokens 0 place : Int)

theorem balance_witness : balanceSystem.Satisfies (fun _ => 1) := by
  unfold System.Satisfies
  decide +kernel

theorem balance_solver_accepts : balanceSystem.isFeasible = true := by decide +kernel

theorem zero_target_still_requires_consumption : needsSeed.predecessor 0 (tokens 0) 0 = 1 := by
  decide +kernel

/-- Every nonempty word fails at its first enabling condition. The only
possible execution is empty and leaves the starting marking unchanged. -/
theorem blocked_execution_ends_at_zero {word : List (Fin 1)} {after : Marking 1}
    (execution : needsSeed.Execution (tokens 0) word after) : after = tokens 0 := by
  cases execution with
  | nil => rfl
  | cons fired remaining =>
      have impossible := fired.1 (0 : Fin 1)
      change 1 ≤ 0 at impossible
      -- Close the impossible firing before eliminating into function
      -- equality; deciding that arbitrary proposition is unnecessary.
      exact False.elim (by omega)

theorem target_not_coverable : ¬ needsSeed.Coverable (tokens 0) (tokens 1) := by
  rintro ⟨after, ⟨word, execution⟩, covers⟩
  have impossible := covers (0 : Fin 1)
  rw [blocked_execution_ends_at_zero execution] at impossible
  change 1 ≤ 0 at impossible
  omega

theorem target_not_reachable : ¬ needsSeed.Reachable (tokens 0) (tokens 1) :=
  fun reachable => target_not_coverable reachable.coverable

theorem balance_feasibility_does_not_supply_execution :
    balanceSystem.isFeasible = true ∧ ¬ needsSeed.Coverable (tokens 0) (tokens 1) :=
  ⟨balance_solver_accepts, target_not_coverable⟩

end Thesis.Causality.Examples.PetriPredecessors
