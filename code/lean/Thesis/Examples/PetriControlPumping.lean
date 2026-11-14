import Thesis.Causality.PetriControlPumping
import Thesis.Examples.PetriControl

namespace Thesis.Causality.Examples.PetriControlPumping

open Thesis.Causality.PetriNet
open Thesis.Causality.ControlledPetriNet
open Thesis.Causality.Examples.PetriControl

/-!
# Returning growth, backward words and the control-state boundary

The two-edge fixture returns to its initial state and adds one counter token.
Its reversed system drains that token along the reversed literal edge order;
the unreversed order has the wrong control guard. A second check accepts the
control path but rejects an insufficient counter marking at its second edge.
The general repetition theorem retains control and the exact endpoint at
every natural count, rather than just checking a few repetitions.

Two negative cases separate pumping from ordinary growth. Spending an
unselected counter is not a pump. A one-time move to another state can enable
arbitrarily large counters without ever returning to the original state.
The latter exclusion concerns every finite word and is paired with actual
executions at every requested threshold; a negative pump does not bound it.

Supplied finite words are kernel checked. Classifier regressions use the
proved exactness theorems without normalizing the complete saturation search.
Empty selections, no edges and zero counters keep their stated semantics.
There is no runtime pilot or exact-reachability procedure in these examples.
-/

def returningGrowth : ControlledPetriNet 1 2 2 where
  net := {
    consume := fun edge _ => if edge = 0 then 1 else 2
    produce := fun edge _ => if edge = 0 then 3 else 1 }
  source := fun edge => if edge = 0 then 0 else 1
  target := fun edge => if edge = 0 then 1 else 0

def returningWitness : ControlledPetriNet.PumpWitness returningGrowth 0 (tokens 1) (fun _ => true) where
  word := [0, 1]
  endpoint := tokens 2
  execution := ⟨rfl, (PetriNet.check_exact returningGrowth.net _ _ _).mp (by decide +kernel)⟩
  grows := (pumpTarget_exact _ _ _).mp (by unfold Below; decide +kernel)

theorem returning_classifier_positive :
    (returningGrowth.classifyPump 0 (tokens 1) (fun _ => true)).isPositive = true :=
  (ControlledPetriNet.classifyPump_exact _ _ _ _).mpr returningWitness.pumpable

theorem returning_word_nonempty : returningWitness.word ≠ [] := returningWitness.word_ne_nil 0 rfl

theorem returning_repeated_endpoint (steps : Nat) : returningWitness.iteratedEndpoint steps = tokens (1 + steps) := by
  funext place
  change 1 + steps * 1 = 1 + steps
  rw [Nat.mul_one]

theorem returning_repeated_execution (steps : Nat) :
    returningGrowth.Execution 0 (tokens 1) (repeatWord [0, 1] steps) 0 (tokens (1 + steps)) := by
  have execution := returningWitness.repeat_execution steps
  rw [returning_repeated_endpoint] at execution
  exact execution

def draining := returningGrowth.reverse

/-- The same edge indices occur in reverse order. Both endpoints have the
original control state; the larger marking is the original execution source. -/
theorem draining_backward_word : draining.Execution 0 (tokens 2) [1, 0] 0 (tokens 1) :=
  ControlledPetriNet.PumpWitness.reverse_execution (system := draining) returningWitness

theorem draining_backward_positive :
    (draining.classifyBackwardPump 0 (tokens 1) (fun _ => true)).isPositive = true :=
  (ControlledPetriNet.classifyBackwardPump_exact _ _ _ _).mpr
    ⟨[1, 0], tokens 2, draining_backward_word, returningWitness.grows⟩

theorem draining_backward_repeated (steps : Nat) :
    draining.Execution 0 (tokens (1 + steps)) (repeatWord [0, 1] steps).reverse 0 (tokens 1) := by
  have execution := ControlledPetriNet.PumpWitness.repeat_reverse_execution
    (system := draining) returningWitness steps
  change draining.Execution 0 (returningWitness.iteratedEndpoint steps)
    (repeatWord [0, 1] steps).reverse 0 (tokens 1) at execution
  rw [returning_repeated_endpoint] at execution
  exact execution

theorem unreversed_order_rejected :
    draining.compiled.check (encode (0 : Fin 2) (tokens 2)) [0, 1] (encode (0 : Fin 2) (tokens 1)) = false := by
  decide +kernel

/-- Matching the complete control path alone is insufficient. The second
edge needs three tokens, but the first has produced only two. -/
theorem matching_path_insufficient_counters :
    draining.controlRun 0 [1, 0] = some 0 ∧
      draining.compiled.run (encode (0 : Fin 2) (tokens 1)) [1, 0] = none := by
  constructor
  · rfl
  · decide +kernel

theorem empty_selection_positive (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) :
    (system.classifyPump state before (fun _ => false)).isPositive = true ∧
      (system.classifyBackwardPump state before (fun _ => false)).isPositive = true := by
  constructor
  · apply (ControlledPetriNet.classifyPump_exact _ _ _ _).mpr
    exact ⟨[], before, ⟨rfl, .nil _⟩, Below.refl _, fun _ impossible => by cases impossible⟩
  · apply (ControlledPetriNet.classifyBackwardPump_exact _ _ _ _).mpr
    exact ⟨[], before, ⟨rfl, .nil _⟩, Below.refl _, fun _ impossible => by cases impossible⟩

theorem no_edges_selected_negative :
    (noEdges.classifyPump 0 (tokens 1) (fun _ => true)).isPositive = false := by
  apply (ControlledPetriNet.classifyPump_negative_iff _ _ _ _).mpr
  rintro ⟨word, after, ⟨_, execution⟩, grows⟩
  cases execution with
  | nil => exact Nat.lt_irrefl 1 (grows.2 0 rfl)
  | @cons _ _ _ edge _ _ _ => exact Fin.elim0 edge

theorem no_edges_backward_selected_negative :
    (noEdges.classifyBackwardPump 0 (tokens 1) (fun _ => true)).isPositive = false := by
  apply (ControlledPetriNet.classifyBackwardPump_negative_iff _ _ _ _).mpr
  rintro ⟨word, larger, ⟨_, execution⟩, grows⟩
  cases execution with
  | nil => exact Nat.lt_irrefl 1 (grows.2 0 rfl)
  | @cons _ _ _ edge _ _ _ => exact Fin.elim0 edge

theorem zero_counter_positive :
    (controlOnly.classifyPump 0 Fin.elim0 Fin.elim0).isPositive = true := by
  apply (ControlledPetriNet.classifyPump_exact _ _ _ _).mpr
  exact ⟨[], Fin.elim0, ⟨rfl, .nil _⟩, fun place => Fin.elim0 place, fun place => Fin.elim0 place⟩

def pair (first second : Nat) : Marking 2 := fun place => if place = 0 then first else second

def simultaneousGrowth : ControlledPetriNet 2 1 1 where
  net := { consume := fun _ => pair 1 1, produce := fun _ => pair 2 3 }
  source := fun _ => 0
  target := fun _ => 0

def simultaneousWitness : ControlledPetriNet.PumpWitness simultaneousGrowth 0 (pair 1 1) (fun _ => true) where
  word := [0]
  endpoint := pair 2 3
  execution := ⟨rfl, (PetriNet.check_exact simultaneousGrowth.net _ _ _).mp (by decide +kernel)⟩
  grows := (pumpTarget_exact _ _ _).mp (by unfold Below; decide +kernel)

theorem simultaneous_threshold (threshold : Nat) :
    1 + threshold ≤ simultaneousWitness.iteratedEndpoint threshold 0 ∧
      1 + threshold ≤ simultaneousWitness.iteratedEndpoint threshold 1 :=
  ⟨simultaneousWitness.repeat_above threshold 0 rfl, simultaneousWitness.repeat_above threshold 1 rfl⟩

def spendsOther : ControlledPetriNet 2 1 1 where
  net := { consume := fun _ => pair 0 1, produce := fun _ => pair 1 0 }
  source := fun _ => 0
  target := fun _ => 0

def firstOnly : Fin 2 → Bool := fun place => decide (place = 0)

theorem selected_growth_spends_unselected : spendsOther.Execution 0 (pair 0 1) [0] 0 (pair 1 0) :=
  ⟨rfl, (PetriNet.check_exact spendsOther.net _ _ _).mp (by decide +kernel)⟩

private theorem total_preserved (before : Marking 2) (edge : Fin 1) (after : Marking 2)
    (fired : spendsOther.net.Fires before edge after) (total : before 0 + before 1 = 1) :
    after 0 + after 1 = 1 := by
  have ready := fired.1 (1 : Fin 2)
  have first := congrFun fired.2 (0 : Fin 2)
  have second := congrFun fired.2 (1 : Fin 2)
  change 1 ≤ before 1 at ready
  change after 0 = before 0 - 0 + 1 at first
  change after 1 = before 1 - 1 + 0 at second
  omega

/-- The preserved total excludes every word, not just the displayed
one-step transfer. Growth of one coordinate cannot spend the other. -/
theorem unselected_loss_classifier_negative :
    (spendsOther.classifyPump 0 (pair 0 1) firstOnly).isPositive = false := by
  apply (ControlledPetriNet.classifyPump_negative_iff _ _ _ _).mpr
  rintro ⟨word, after, ⟨_, execution⟩, grows⟩
  have total := execution.preserves (fun marking => marking 0 + marking 1 = 1) total_preserved rfl
  have other := grows.1 (1 : Fin 2)
  have strict := grows.2 (0 : Fin 2) rfl
  change 1 ≤ after 1 at other
  change 0 < after 0 at strict
  omega

/-! Moving once to state one enables unlimited later growth. Returning to
state zero is impossible for every nonempty word, regardless of counters. -/

def switchedGrowth : ControlledPetriNet 1 2 2 where
  net := {
    consume := fun _ _ => 0
    produce := fun edge _ => if edge = 0 then 0 else 1 }
  source := fun edge => if edge = 0 then 0 else 1
  target := fun _ => 1

def activeWitness : ControlledPetriNet.PumpWitness switchedGrowth 1 (tokens 0) (fun _ => true) where
  word := [1]
  endpoint := tokens 1
  execution := ⟨rfl, (PetriNet.check_exact switchedGrowth.net _ _ _).mp (by decide +kernel)⟩
  grows := (pumpTarget_exact _ _ _).mp (by unfold Below; decide +kernel)

private theorem cannot_return_from_one (word : List (Fin 2)) : switchedGrowth.controlRun 1 word ≠ some 0 := by
  induction word with
  | nil => exact (by decide +kernel : (some (1 : Fin 2)) ≠ some 0)
  | cons edge rest ih =>
      intro accepted
      exact ih ((controlRun_cons_iff switchedGrowth _ _ _ _).mp accepted).2

private theorem returning_word_empty {word : List (Fin 2)}
    (returns : switchedGrowth.controlRun 0 word = some 0) : word = [] := by
  cases word with
  | nil => rfl
  | cons edge rest =>
      exact False.elim (cannot_return_from_one rest ((controlRun_cons_iff switchedGrowth _ _ _ _).mp returns).2)

theorem switched_source_not_pumpable : ¬ switchedGrowth.Pumpable 0 (tokens 0) (fun _ => true) := by
  rintro ⟨word, after, ⟨control, execution⟩, grows⟩
  have empty := returning_word_empty control
  rw [empty] at execution
  cases execution
  exact Nat.lt_irrefl 0 (grows.2 0 rfl)

theorem active_repeated_endpoint (steps : Nat) : activeWitness.iteratedEndpoint steps = tokens steps := by
  funext place
  change 0 + steps * 1 = steps
  rw [Nat.mul_one, Nat.zero_add]

theorem switched_execution (steps : Nat) :
    switchedGrowth.Execution 0 (tokens 0) ([0] ++ repeatWord [1] steps) 1 (tokens steps) := by
  have initial : switchedGrowth.Execution 0 (tokens 0) [0] 1 (tokens 0) :=
    ⟨rfl, (PetriNet.check_exact switchedGrowth.net _ _ _).mp (by decide +kernel)⟩
  have growing := activeWitness.repeat_execution steps
  rw [active_repeated_endpoint] at growing
  exact initial.append growing

/-- The negative decision and unbounded later values coexist. This rules
out deriving a counter bound from failure of a pump at the original state. -/
theorem failed_pump_does_not_bound_selected_coordinate :
    (switchedGrowth.classifyPump 0 (tokens 0) (fun _ => true)).isPositive = false ∧
      ∀ threshold, ∃ word after,
        switchedGrowth.Execution 0 (tokens 0) word 1 after ∧ threshold ≤ after 0 :=
  ⟨(ControlledPetriNet.classifyPump_negative_iff _ _ _ _).mpr switched_source_not_pumpable,
    fun threshold => ⟨[0] ++ repeatWord [1] threshold, tokens threshold, switched_execution threshold, Nat.le_refl _⟩⟩

end Thesis.Causality.Examples.PetriControlPumping
