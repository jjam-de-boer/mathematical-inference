import Thesis.Causality.PetriControlWordCompletion
import Thesis.Examples.PetriControl
import Thesis.Examples.PetriWordCompletion

namespace Thesis.Causality.Examples.PetriControlWordCompletion

open Thesis.Causality.PetriNet
open Thesis.Causality.ControlledPetriNet
open Thesis.Causality.Examples.PetriControl (tokens move wrongState controlOnly)
open Thesis.Causality.Examples.PetriWordCompletion (free fixed draining transfer lateSource lateTarget)

/-!
# Controlled partial endpoints retain states, guards and the actual word

The increment fixture completes unknown initial counters at a different
final state. Wrong initial, intermediate and final control states remain
impossible even when the ordinary counter word can be completed. An empty
word cannot change either the state or a fixed counter value. With no
counter places the control path still has to be checked.

Valid control does not repair a counter guard or inconsistent endpoint
surpluses. The transfer fixture exercises rejection in a later coordinate
after the first coordinate has passed. Separately, actual ordinary witness
data are converted without changing their endpoints, then checked through
the existing compiled execution theorem. All fixtures use supplied words;
there is no complete-search normalization, native decision axiom or pilot.
-/

variable {places states transitions : Nat}

/-- Inspect actual returned data, rather than only a positive Boolean. -/
private def resultAt {system : ControlledPetriNet places states transitions}
    {state next : Fin states} {word : List (Fin transitions)} {source target : PartialMarking places}
    (result : ControlledPetriNet.WordCompletionResult system state word next source target)
    (place : Fin places) : Option (Nat × Nat) :=
  match result with
  | .positive witness => some (witness.before place, witness.after place)
  | .negative _ => none

/-- The requested final state differs from the initial one. No returning
pump premise is imposed on this ordinary execution. -/
theorem state_changing_completion :
    resultAt (move.classifyWordCompletion 0 [0] 1 free (fixed 5)) 0 = some (4, 5) := rfl

theorem wrong_initial_state_refuted : ¬ wrongState.WordCompletable 0 [0] 1 free free :=
  (ControlledPetriNet.classifyWordCompletion_negative_iff wrongState 0 [0] 1 free free).mp rfl

theorem wrong_final_state_refuted : ¬ move.WordCompletable 0 [0] 0 free free :=
  (ControlledPetriNet.classifyWordCompletion_negative_iff move 0 [0] 0 free free).mp rfl

def brokenMiddle : ControlledPetriNet 0 2 2 where
  net := { consume := fun _ => Fin.elim0, produce := fun _ => Fin.elim0 }
  source := fun _ => 0
  target := fun edge => if edge = 0 then 1 else 0

/-- The first source and last target both match the query. After the
first edge reaches state one, however, the second edge requires state zero.
The zero-counter word itself is executable, so control alone rejects it. -/
theorem intermediate_state_refuted :
    (brokenMiddle.net.classifyWordCompletion [0, 1] free free).isPositive = true ∧
      ¬ brokenMiddle.WordCompletable 0 [0, 1] 0 free free :=
  ⟨rfl, (ControlledPetriNet.classifyWordCompletion_negative_iff brokenMiddle 0 [0, 1] 0 free free).mp rfl⟩

def guarded : ControlledPetriNet 1 2 1 where
  net := draining
  source := fun _ => 0
  target := fun _ => 0

/-- The self-loop path is valid, but two draining firings still require
five initial tokens. Completing the unknown target cannot supply a fifth. -/
theorem valid_path_insufficient_counters : ¬ guarded.WordCompletable 0 [0, 0] 0 (fixed 4) free :=
  (ControlledPetriNet.classifyWordCompletion_negative_iff guarded 0 [0, 0] 0 (fixed 4) free).mp rfl

theorem valid_path_sufficient_counters :
    resultAt (guarded.classifyWordCompletion 0 [0, 0] 0 (fixed 5) (fixed 1)) 0 = some (5, 1) := rfl

theorem empty_word_completes_same_state :
    resultAt (move.classifyWordCompletion 0 [] 0 free (fixed 7)) 0 = some (7, 7) := rfl

theorem empty_word_cannot_change_state : ¬ move.WordCompletable 0 [] 1 free free :=
  (ControlledPetriNet.classifyWordCompletion_negative_iff move 0 [] 1 free free).mp rfl

theorem empty_word_cannot_change_fixed_counter : ¬ move.WordCompletable 0 [] 0 (fixed 7) (fixed 8) :=
  (ControlledPetriNet.classifyWordCompletion_negative_iff move 0 [] 0 (fixed 7) (fixed 8)).mp rfl

theorem zero_counters_valid_control : controlOnly.WordCompletable 0 [0] 1 Fin.elim0 Fin.elim0 :=
  (ControlledPetriNet.classifyWordCompletion_exact controlOnly 0 [0] 1 Fin.elim0 Fin.elim0).mp rfl

theorem zero_counters_wrong_final_state : ¬ controlOnly.WordCompletable 0 [0] 0 Fin.elim0 Fin.elim0 :=
  (ControlledPetriNet.classifyWordCompletion_negative_iff controlOnly 0 [0] 0 Fin.elim0 Fin.elim0).mp rfl

def transferLoop : ControlledPetriNet 2 1 1 where
  net := transfer
  source := fun _ => 0
  target := fun _ => 0

/-- Control and the first coordinate pass; the second counter's unequal
surpluses refute every completed pair. The wrapper retains that rejection. -/
theorem later_counter_rejection : ¬ transferLoop.WordCompletable 0 [0, 0] 0 lateSource lateTarget :=
  (ControlledPetriNet.classifyWordCompletion_negative_iff transferLoop 0 [0, 0] 0 lateSource lateTarget).mp rfl

def counterMove : PetriNet.WordCompletionWitness move.net [0] free (fixed 5) where
  before := tokens 4
  after := tokens 5
  source_matches := fun _ => trivial
  target_matches := fun _ => rfl
  execution := (PetriNet.run_eq_some_iff move.net _ _ _).mp rfl

def controlledMove : ControlledPetriNet.WordCompletionWitness move 0 [0] 1 free (fixed 5) :=
  ControlledPetriNet.WordCompletionWitness.ofCounter counterMove rfl

theorem converted_endpoints_unchanged :
    controlledMove.before = counterMove.before ∧ controlledMove.after = counterMove.after := ⟨rfl, rfl⟩

theorem converted_data_execute :
    move.controlRun 0 [0] = some 1 ∧ move.net.run controlledMove.before [0] = some controlledMove.after :=
  controlledMove.run_exact

theorem converted_data_compile :
    move.compiled.run (encode (0 : Fin 2) controlledMove.before) [0] =
      some (encode (1 : Fin 2) controlledMove.after) :=
  controlledMove.compiled_run_exact

end Thesis.Causality.Examples.PetriControlWordCompletion
