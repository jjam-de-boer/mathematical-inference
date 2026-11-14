import Thesis.Causality.PetriControl
import Thesis.Causality.PetriPumping

namespace Thesis.Causality.Examples.PetriControl

open Thesis.Causality.PetriNet
open Thesis.Causality.ControlledPetriNet

/-!
# Control-sensitive compilation regressions

The same counter increment is allowed in one state and forbidden in
another. A self-loop keeps exactly one control token, and a nonreturning
edge can cover its destination without supplying a pump at its source.
These distinctions would disappear if compilation retained only counter
effects or forgot the original control token during a growth test.

An endpoint presented as a raw marking is decoded into its computed state
and counter execution. Separate fixtures retain a returning two-edge word,
parallel edge indices, zero counter places, no edges and both empty-word
endpoint checks. Supplied words are kernel checked; the complete pumping
classifier is used through its theorem, without a new runtime pilot or a
controlled classifier adapter.
-/

def tokens (count : Nat) : Marking 1 := fun _ => count

def increment : Thesis.Causality.PetriNet 1 1 where
  consume := fun _ _ => 0
  produce := fun _ _ => 1

def wrongState : ControlledPetriNet 1 2 1 where
  net := increment
  source := fun _ => 1
  target := fun _ => 1

theorem forgetting_control_admits_edge : increment.check (tokens 0) [0] (tokens 1) = true := by
  decide +kernel

theorem wrong_state_edge_rejected :
    wrongState.compiled.check (encode (0 : Fin 2) (tokens 0)) [0] (encode (1 : Fin 2) (tokens 1)) = false := by
  decide +kernel

/-- This exclusion concerns all words, rather than only the rejected
single-edge example. No edge can start in state zero. -/
theorem wrong_state_not_coverable : ¬ wrongState.Coverable 0 (tokens 0) 1 (tokens 1) := by
  rintro ⟨word, after, execution, _⟩
  cases word with
  | nil =>
      have same := Option.some.inj execution.1
      exact (by decide +kernel : (0 : Fin 2) ≠ 1) same
  | cons edge rest =>
      have first := (controlRun_cons_iff wrongState _ _ _ _).mp execution.1
      exact (by decide +kernel : (0 : Fin 2) ≠ 1) first.1

theorem compiled_wrong_state_not_coverable :
    ¬ wrongState.compiled.Coverable (encode (0 : Fin 2) (tokens 0)) (encode (1 : Fin 2) (tokens 1)) :=
  fun coverable => wrong_state_not_coverable ((coverable_compiled_iff wrongState _ _ _ _).mp coverable)

theorem self_loop_execution : wrongState.Execution 1 (tokens 0) [0] 1 (tokens 1) :=
  ⟨rfl, (check_exact increment _ _ _).mp forgetting_control_admits_edge⟩

theorem self_loop_exact_endpoint :
    wrongState.compiled.run (encode (1 : Fin 2) (tokens 0)) [0] = some (encode (1 : Fin 2) (tokens 1)) :=
  (run_eq_some_iff wrongState.compiled _ _ _).mpr self_loop_execution.compile

def move : ControlledPetriNet 1 2 1 where
  net := increment
  source := fun _ => 0
  target := fun _ => 1

/-- Deliberately not written with `encode`: all compiled endpoints, not
only syntactically encoded ones, must have the promised interpretation. -/
def rawMoveEndpoint : Marking 3 := fun place => if place = 1 then 0 else 1

theorem move_raw_execution :
    move.compiled.Execution (encode (0 : Fin 2) (tokens 0)) [0] rawMoveEndpoint :=
  (check_exact move.compiled _ _ _).mp (by decide +kernel)

def decodedMove := decodeExecution move_raw_execution

theorem decoded_move_state : decodedMove.finalState = 1 := rfl

theorem decoded_move_shape : rawMoveEndpoint = encode (1 : Fin 2) (project (places := 1) (states := 2) rawMoveEndpoint) :=
  decodedMove.endpoint

theorem decoded_move_counter : move.net.Execution (tokens 0) [0] (project (states := 2) rawMoveEndpoint) :=
  decodedMove.execution.2

theorem move_covers_destination : move.Coverable 0 (tokens 0) 1 (tokens 1) :=
  ⟨[0], tokens 1, ⟨rfl, (check_exact increment _ _ _).mp forgetting_control_admits_edge⟩,
    fun _ => Nat.le_refl _⟩

theorem compiled_move_covers_destination :
    move.compiled.Coverable (encode (0 : Fin 2) (tokens 0)) (encode (1 : Fin 2) (tokens 1)) :=
  (coverable_compiled_iff move _ _ _ _).mpr move_covers_destination

private theorem move_return_word_empty {word : List (Fin 1)}
    (returns : move.controlRun 0 word = some 0) : word = [] := by
  cases word with
  | nil => rfl
  | cons edge rest =>
      have suffix := ((controlRun_cons_iff move _ _ _ _).mp returns).2
      cases rest with
      | nil =>
          have same := Option.some.inj suffix
          exact False.elim ((by decide +kernel : (1 : Fin 2) ≠ 0) same)
      | cons next tail =>
          have first := ((controlRun_cons_iff move _ _ _ _).mp suffix).1
          exact False.elim ((by decide +kernel : (1 : Fin 2) ≠ 0) first)

def counterOnly : Fin 3 → Bool := fun place => decide (place = 0)

/-- The control places are unselected, but preservation still applies to
them. Thus leaving state zero cannot masquerade as a returning pump. -/
theorem nonreturning_growth_not_pumpable :
    ¬ move.compiled.Pumpable (encode (0 : Fin 2) (tokens 0)) counterOnly := by
  rintro ⟨word, after, execution, grows⟩
  let decoded := decodeExecution execution
  have preserved : Below (encode (0 : Fin 2) (tokens 0))
      (encode decoded.finalState (project after)) := by
    rw [← decoded.endpoint]
    exact grows.1
  have state := ((encode_below_iff _ _ _ _).mp preserved).1
  have control := decoded.execution.1
  rw [← state] at control
  have empty := move_return_word_empty control
  have computed := (run_eq_some_iff move.compiled _ _ _).mpr execution
  rw [empty] at computed
  change some (encode (0 : Fin 2) (tokens 0)) = some after at computed
  have same := Option.some.inj computed
  have strict := grows.2 (0 : Fin 3) rfl
  rw [← same] at strict
  exact Nat.lt_irrefl 0 strict

theorem compiled_nonreturning_growth_rejected :
    (move.compiled.classifyPump (encode (0 : Fin 2) (tokens 0)) counterOnly).isPositive = false :=
  (classifyPump_negative_iff _ _ _).mpr nonreturning_growth_not_pumpable

def roundTrip : ControlledPetriNet 1 2 2 where
  net := {
    consume := fun _ _ => 0
    produce := fun edge _ => if edge = 0 then 1 else 0 }
  source := fun edge => if edge = 0 then 0 else 1
  target := fun edge => if edge = 0 then 1 else 0

theorem returning_word : roundTrip.Execution 0 (tokens 0) [0, 1] 0 (tokens 1) :=
  ⟨rfl, (check_exact roundTrip.net _ _ _).mp (by decide +kernel)⟩

theorem compiled_returning_word :
    roundTrip.compiled.Execution (encode (0 : Fin 2) (tokens 0)) [0, 1] (encode (0 : Fin 2) (tokens 1)) :=
  returning_word.compile

def parallelEdges : ControlledPetriNet 1 1 2 where
  net := {
    consume := fun _ _ => 0
    produce := fun edge _ => if edge = 0 then 1 else 2 }
  source := fun _ => 0
  target := fun _ => 0

theorem parallel_second_edge_retained :
    parallelEdges.compiled.Execution (encode (0 : Fin 1) (tokens 0)) [1] (encode (0 : Fin 1) (tokens 2)) :=
  (check_exact parallelEdges.compiled _ _ _).mp (by decide +kernel)

theorem parallel_counter_word_retained : parallelEdges.Execution 0 (tokens 0) [1] 0 (tokens 2) :=
  (execution_compiled_iff parallelEdges _ _ _ _ _).mp parallel_second_edge_retained

def controlOnly : ControlledPetriNet 0 2 1 where
  net := { consume := fun _ => Fin.elim0, produce := fun _ => Fin.elim0 }
  source := fun _ => 0
  target := fun _ => 1

theorem zero_counter_places :
    controlOnly.compiled.Execution (encode (0 : Fin 2) Fin.elim0) [0] (encode (1 : Fin 2) Fin.elim0) :=
  (check_exact controlOnly.compiled _ _ _).mp (by decide +kernel)

def noEdges : ControlledPetriNet 1 2 0 where
  net := { consume := Fin.elim0, produce := Fin.elim0 }
  source := Fin.elim0
  target := Fin.elim0

theorem no_edges_same_state_coverable : noEdges.Coverable 0 (tokens 3) 0 (tokens 2) :=
  ⟨[], tokens 3, ⟨rfl, .nil _⟩, fun _ => (by decide +kernel : 2 ≤ 3)⟩

theorem no_edges_other_state_not_coverable : ¬ noEdges.Coverable 0 (tokens 3) 1 (tokens 2) := by
  rintro ⟨word, after, execution, _⟩
  cases word with
  | nil => exact (by decide +kernel : (0 : Fin 2) ≠ 1) (Option.some.inj execution.1)
  | cons edge rest => exact Fin.elim0 edge

theorem empty_word_keeps_state :
    noEdges.compiled.check (encode (0 : Fin 2) (tokens 3)) [] (encode (1 : Fin 2) (tokens 3)) = false := by
  decide +kernel

theorem empty_word_keeps_counters :
    noEdges.compiled.check (encode (0 : Fin 2) (tokens 3)) [] (encode (0 : Fin 2) (tokens 2)) = false := by
  decide +kernel

end Thesis.Causality.Examples.PetriControl
