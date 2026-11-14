import Thesis.Causality.PetriControlCoverability
import Thesis.Causality.PetriControlReversal
import Thesis.Causality.PetriPumping

namespace Thesis.Causality.ControlledPetriNet

open PetriNet

/-!
# Returning pumps with explicit finite control

A forward pump starts and ends at the supplied control state. Its selected
counter coordinates strictly increase; every other counter is preserved or
increased as well. Returning control is essential for repeating the word.
The existing controlled coverability classifier decides this question in
one call, with the same control state and the counter pump target.

Actual words and original counter endpoints remain in the result. Repetition
reuses the raw counter witness's exact affine endpoint and separately checks
the repeated control path. No word is selected from a propositional existence
claim. Empty selections permit the empty word, and a nonempty selection
forces every witness word to be nonempty.

Backward pumping runs this construction in the reversed controlled system
from the known finite marking. Reversing its stored word gives an original
execution from a larger marking at the same control state back to the input.
This keeps decoding on the known-source side of the compilation theorem.

The existing saturation procedure and termination proof are unchanged.
Neither a negative pumping answer nor control-state finiteness bounds the
reachable counters. Partially specified endpoints, general exact reachability
and causal formula-search stopping remain separate problems.
-/

variable {places states transitions : Nat}
variable {system : ControlledPetriNet places states transitions}

def Pumpable (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) (selected : Fin places → Bool) : Prop :=
  ∃ word after, system.Execution state before word state after ∧ GrowsOn before after selected

theorem pumpable_iff_coverable (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) (selected : Fin places → Bool) :
    system.Pumpable state before selected ↔ system.Coverable state before state (pumpTarget before selected) := by
  constructor
  · rintro ⟨word, after, execution, grows⟩
    exact ⟨word, after, execution, (pumpTarget_exact _ _ _).mpr grows⟩
  · rintro ⟨word, after, execution, covers⟩
    exact ⟨word, after, execution, (pumpTarget_exact _ _ _).mp covers⟩

structure PumpWitness (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) (selected : Fin places → Bool) where
  word : List (Fin transitions)
  endpoint : Marking places
  execution : system.Execution state before word state endpoint
  grows : GrowsOn before endpoint selected

namespace PumpWitness

variable {state : Fin states} {before : Marking places} {selected : Fin places → Bool}

theorem pumpable (witness : PumpWitness system state before selected) : system.Pumpable state before selected :=
  ⟨witness.word, witness.endpoint, witness.execution, witness.grows⟩

/-- Forget only the control proof, retaining the concrete word, endpoint
and all counter guards. Existing affine repetition lemmas apply directly. -/
def toCounterWitness (witness : PumpWitness system state before selected) :
    PetriNet.PumpWitness system.net before selected where
  word := witness.word
  endpoint := witness.endpoint
  execution := witness.execution.2
  grows := witness.grows

def gain (witness : PumpWitness system state before selected) : Marking places :=
  witness.toCounterWitness.gain

def iteratedEndpoint (witness : PumpWitness system state before selected) (steps : Nat) : Marking places :=
  witness.toCounterWitness.iteratedEndpoint steps

theorem endpoint_eq_add_gain (witness : PumpWitness system state before selected) :
    witness.endpoint = addMarking before witness.gain := witness.toCounterWitness.endpoint_eq_add_gain

theorem gain_positive (witness : PumpWitness system state before selected) (place : Fin places)
    (chosen : selected place = true) : 0 < witness.gain place :=
  witness.toCounterWitness.gain_positive place chosen

/-- Counter repetition supplies the entire affine endpoint. Control
concatenation independently proves that every copy returns to the same state. -/
theorem repeat_execution (witness : PumpWitness system state before selected) (steps : Nat) :
    system.Execution state before (repeatWord witness.word steps) state (witness.iteratedEndpoint steps) := by
  refine ⟨?_, witness.toCounterWitness.repeat_execution steps⟩
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [repeatWord, controlRun_append, ih, Option.bind_some]
      exact witness.execution.1

theorem repeat_above (witness : PumpWitness system state before selected) (threshold : Nat)
    (place : Fin places) (chosen : selected place = true) :
    before place + threshold ≤ witness.iteratedEndpoint threshold place :=
  witness.toCounterWitness.repeat_above threshold place chosen

theorem word_ne_nil (witness : PumpWitness system state before selected) (place : Fin places)
    (chosen : selected place = true) : witness.word ≠ [] :=
  witness.toCounterWitness.word_ne_nil place chosen

/-- This is the original-system word: reverse the actual reverse-system
word and exchange its exact counter endpoints, retaining the control state. -/
theorem reverse_execution (witness : PumpWitness system.reverse state before selected) :
    system.Execution state witness.endpoint witness.word.reverse state before := by
  simpa only [reverse_reverse] using witness.execution.reverse

theorem repeat_reverse_execution (witness : PumpWitness system.reverse state before selected) (steps : Nat) :
    system.Execution state (witness.iteratedEndpoint steps) (repeatWord witness.word steps).reverse state before := by
  simpa only [reverse_reverse] using (witness.repeat_execution steps).reverse

end PumpWitness

inductive PumpResult (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) (selected : Fin places → Bool) where
  | positive (witness : PumpWitness system state before selected)
  | negative (refuted : ¬ system.Pumpable state before selected)

def PumpResult.isPositive {state : Fin states} {before : Marking places} {selected : Fin places → Bool} :
    PumpResult system state before selected → Bool
  | .positive _ => true
  | .negative _ => false

theorem PumpResult.positive_exact {state : Fin states} {before : Marking places} {selected : Fin places → Bool}
    (result : PumpResult system state before selected) :
    result.isPositive = true ↔ system.Pumpable state before selected := by
  cases result with
  | positive witness => exact ⟨fun _ => witness.pumpable, fun _ => rfl⟩
  | negative refuted =>
      constructor
      · intro impossible; cases impossible
      · intro pumpable; exact False.elim (refuted pumpable)

theorem PumpResult.negative_exact {state : Fin states} {before : Marking places} {selected : Fin places → Bool}
    (result : PumpResult system state before selected) :
    result.isPositive = false ↔ ¬ system.Pumpable state before selected := by
  cases result with
  | positive witness =>
      constructor
      · intro impossible; cases impossible
      · intro refuted; exact False.elim (refuted witness.pumpable)
  | negative refuted => exact ⟨fun _ => refuted, fun _ => rfl⟩

/-- One existing coverability call at the same control state. All witness
data are already in the original counter space; the remaining conversion
only changes the target-coverage proof into the exact growth condition. -/
def classifyPump (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) (selected : Fin places → Bool) :
    PumpResult system state before selected :=
  match system.classifyCoverability state before state (pumpTarget before selected) with
  | .positive witness => .positive {
      word := witness.word
      endpoint := witness.endpoint
      execution := witness.execution
      grows := (pumpTarget_exact _ _ _).mp witness.covers }
  | .negative refuted =>
      .negative (fun pumpable => refuted ((pumpable_iff_coverable system _ _ _).mp pumpable))

theorem classifyPump_exact (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) (selected : Fin places → Bool) :
    (system.classifyPump state before selected).isPositive = true ↔ system.Pumpable state before selected :=
  (system.classifyPump state before selected).positive_exact

theorem classifyPump_negative_iff (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) (selected : Fin places → Bool) :
    (system.classifyPump state before selected).isPositive = false ↔ ¬ system.Pumpable state before selected :=
  (system.classifyPump state before selected).negative_exact

def BackwardPumpable (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) (selected : Fin places → Bool) : Prop :=
  ∃ word larger, system.Execution state larger word state before ∧ GrowsOn before larger selected

theorem backwardPumpable_iff_reverse (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) (selected : Fin places → Bool) :
    system.BackwardPumpable state before selected ↔ system.reverse.Pumpable state before selected := by
  constructor
  · rintro ⟨word, larger, execution, grows⟩
    exact ⟨word.reverse, larger, execution.reverse, grows⟩
  · rintro ⟨word, larger, execution, grows⟩
    exact ⟨word.reverse, larger, by simpa only [reverse_reverse] using execution.reverse, grows⟩

/-- As for raw nets, a positive result stores a reverse-system witness.
Its `word.reverse` is executable in the original system by
`PumpWitness.reverse_execution`, including at every affine repetition. -/
def classifyBackwardPump (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) (selected : Fin places → Bool) :
    PumpResult system.reverse state before selected :=
  system.reverse.classifyPump state before selected

theorem classifyBackwardPump_exact (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) (selected : Fin places → Bool) :
    (system.classifyBackwardPump state before selected).isPositive = true ↔
      system.BackwardPumpable state before selected :=
  (classifyPump_exact system.reverse _ _ _).trans (backwardPumpable_iff_reverse system _ _ _).symm

theorem classifyBackwardPump_negative_iff (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) (selected : Fin places → Bool) :
    (system.classifyBackwardPump state before selected).isPositive = false ↔
      ¬ system.BackwardPumpable state before selected := by
  rw [classifyBackwardPump, classifyPump_negative_iff, ← backwardPumpable_iff_reverse]

end Thesis.Causality.ControlledPetriNet
