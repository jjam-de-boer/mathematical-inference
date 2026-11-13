import Thesis.Causality.PetriCoverabilitySearch
import Thesis.Causality.PetriReversal

namespace Thesis.Causality.PetriNet

/-!
# Exact pumping tests at finite markings

A selected coordinate must strictly increase, and every coordinate must
retain at least its starting value. Thus a positive answer supplies a real
execution that can be repeated from its own endpoint. Merely reaching a
large selected coordinate after consuming another resource is insufficient.

The target is the starting marking plus one token in every selected place.
The existing complete coverability classifier therefore decides this precise
question in one call, retaining an actual word and endpoint or refuting all
such words. No finite word cutoff, token bound or equation-only relaxation
is introduced. An empty selection deliberately permits the empty execution;
if any place is selected, every positive word is nonempty.

Backward pumping uses the reversed net. Its stored reverse word yields an
original-net execution from the larger marking back to the supplied marking.
All sources here are actual finite markings. There is no finite-control
compilation, partially specified endpoint, boundedness inference from a
negative answer, or general exact-reachability procedure in this module.
-/

variable {places transitions : Nat}
variable {net : Thesis.Causality.PetriNet places transitions}

/-- Selection is finite Boolean data; the remaining places may grow too,
but none may lose tokens. This is a property of both complete endpoints. -/
def GrowsOn (before after : Marking places) (selected : Fin places → Bool) : Prop :=
  Below before after ∧ ∀ place, selected place = true → before place < after place

def pumpTarget (before : Marking places) (selected : Fin places → Bool) : Marking places :=
  fun place => before place + if selected place then 1 else 0

theorem pumpTarget_exact (before after : Marking places) (selected : Fin places → Bool) :
    Below (pumpTarget before selected) after ↔ GrowsOn before after selected := by
  constructor
  · intro enough
    constructor
    · intro place
      have bound := enough place
      change before place + (if selected place then 1 else 0) ≤ after place at bound
      split at bound <;> omega
    · intro place chosen
      have bound := enough place
      change before place + (if selected place then 1 else 0) ≤ after place at bound
      simp only [chosen, ite_true] at bound
      omega
  · rintro ⟨preserved, increased⟩ place
    change before place + (if selected place then 1 else 0) ≤ after place
    cases chosen : selected place with
    | false =>
        simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
        exact preserved place
    | true =>
        have strict := increased place chosen
        simp only [ite_true]
        omega

def Pumpable (net : Thesis.Causality.PetriNet places transitions)
    (before : Marking places) (selected : Fin places → Bool) : Prop :=
  ∃ word after, net.Execution before word after ∧ GrowsOn before after selected

theorem pumpable_iff_coverable (net : Thesis.Causality.PetriNet places transitions)
    (before : Marking places) (selected : Fin places → Bool) :
    net.Pumpable before selected ↔ net.Coverable before (pumpTarget before selected) := by
  constructor
  · rintro ⟨word, after, execution, grows⟩
    exact ⟨after, ⟨word, execution⟩, (pumpTarget_exact before after selected).mpr grows⟩
  · rintro ⟨after, ⟨word, execution⟩, covers⟩
    exact ⟨word, after, execution, (pumpTarget_exact before after selected).mp covers⟩

structure PumpWitness (net : Thesis.Causality.PetriNet places transitions)
    (before : Marking places) (selected : Fin places → Bool) where
  word : List (Fin transitions)
  endpoint : Marking places
  execution : net.Execution before word endpoint
  grows : GrowsOn before endpoint selected

/-- Repetition retains the literal word order, rather than only a firing
count. Appending a copy at the end matches execution composition. -/
def repeatWord {α : Type u} (word : List α) : Nat → List α
  | 0 => []
  | steps + 1 => repeatWord word steps ++ word

namespace PumpWitness

variable {before : Marking places} {selected : Fin places → Bool}

theorem pumpable (witness : PumpWitness net before selected) : net.Pumpable before selected :=
  ⟨witness.word, witness.endpoint, witness.execution, witness.grows⟩

/-- Natural subtraction is exact because the witness preserves every
coordinate. No signed direction with a hidden negative entry is accepted. -/
def gain (witness : PumpWitness net before selected) : Marking places :=
  fun place => witness.endpoint place - before place

theorem endpoint_eq_add_gain (witness : PumpWitness net before selected) :
    witness.endpoint = addMarking before witness.gain := by
  funext place
  have enough := witness.grows.1 place
  change witness.endpoint place = before place + (witness.endpoint place - before place)
  omega

theorem gain_positive (witness : PumpWitness net before selected) (place : Fin places)
    (chosen : selected place = true) : 0 < witness.gain place := by
  have strict := witness.grows.2 place chosen
  change 0 < witness.endpoint place - before place
  omega

def iteratedEndpoint (witness : PumpWitness net before selected) (steps : Nat) : Marking places :=
  fun place => before place + steps * witness.gain place

/-- A supplied pump executes at every repetition count, with the exact
affine endpoint. Execution lifting preserves every intermediate guard. -/
theorem repeat_execution (witness : PumpWitness net before selected) (steps : Nat) :
    net.Execution before (repeatWord witness.word steps) (witness.iteratedEndpoint steps) := by
  induction steps with
  | zero =>
      have endpoint : witness.iteratedEndpoint 0 = before := by
        funext place
        change before place + 0 * witness.gain place = before place
        rw [Nat.zero_mul, Nat.add_zero]
      rw [endpoint]
      exact .nil _
  | succ steps ih =>
      have shifted := witness.execution.add_marking (fun place => steps * witness.gain place)
      have endpoint : addMarking witness.endpoint (fun place => steps * witness.gain place) =
          witness.iteratedEndpoint (steps + 1) := by
        funext place
        have first := congrFun witness.endpoint_eq_add_gain place
        change witness.endpoint place = before place + witness.gain place at first
        change witness.endpoint place + steps * witness.gain place =
          before place + (steps + 1) * witness.gain place
        rw [Nat.add_mul, Nat.one_mul]
        omega
      change net.Execution (witness.iteratedEndpoint steps) witness.word _ at shifted
      rw [endpoint] at shifted
      exact ih.append shifted

/-- Every requested increment is attained or exceeded simultaneously in
all selected places, by the computed repeated word above. -/
theorem repeat_above (witness : PumpWitness net before selected) (threshold : Nat)
    (place : Fin places) (chosen : selected place = true) :
    before place + threshold ≤ witness.iteratedEndpoint threshold place := by
  have positive : 1 ≤ witness.gain place := witness.gain_positive place chosen
  have multiplied := Nat.mul_le_mul_left threshold positive
  rw [Nat.mul_one] at multiplied
  exact Nat.add_le_add_left multiplied (before place)

theorem word_ne_nil (witness : PumpWitness net before selected) (place : Fin places)
    (chosen : selected place = true) : witness.word ≠ [] := by
  intro empty
  have computed := (run_eq_some_iff net before witness.endpoint witness.word).mpr witness.execution
  rw [empty] at computed
  change some before = some witness.endpoint at computed
  have same := Option.some.inj computed
  have strict := witness.grows.2 place chosen
  rw [← same] at strict
  exact Nat.lt_irrefl _ strict

/-- A reverse-net witness stores an actual original-net word as well:
reverse the stored list and exchange its endpoints. -/
theorem reverse_execution (witness : PumpWitness net.reverse before selected) :
    net.Execution witness.endpoint witness.word.reverse before := by
  simpa only [reverse_reverse] using witness.execution.reverse

theorem repeat_reverse_execution (witness : PumpWitness net.reverse before selected) (steps : Nat) :
    net.Execution (witness.iteratedEndpoint steps) (repeatWord witness.word steps).reverse before := by
  simpa only [reverse_reverse] using (witness.repeat_execution steps).reverse

end PumpWitness

inductive PumpResult (net : Thesis.Causality.PetriNet places transitions)
    (before : Marking places) (selected : Fin places → Bool) where
  | positive (witness : PumpWitness net before selected)
  | negative (refuted : ¬ net.Pumpable before selected)

def PumpResult.isPositive {before : Marking places} {selected : Fin places → Bool} :
    PumpResult net before selected → Bool
  | .positive _ => true
  | .negative _ => false

theorem PumpResult.positive_exact {before : Marking places} {selected : Fin places → Bool}
    (result : PumpResult net before selected) : result.isPositive = true ↔ net.Pumpable before selected := by
  cases result with
  | positive witness => exact ⟨fun _ => witness.pumpable, fun _ => rfl⟩
  | negative refuted =>
      constructor
      · intro impossible; cases impossible
      · intro pumpable; exact False.elim (refuted pumpable)

/-- One exact coverability call supplies both computational data and the
negative proof. The source equality belongs to that result; no marking
function equality is decided and no word is chosen from an existence proof. -/
def classifyPump (net : Thesis.Causality.PetriNet places transitions)
    (before : Marking places) (selected : Fin places → Bool) : PumpResult net before selected :=
  match net.classifyCoverability before (pumpTarget before selected) with
  | .positive witness source =>
      .positive {
        word := witness.word
        endpoint := witness.endpoint
        execution := by simpa only [source] using witness.execution
        grows := (pumpTarget_exact before witness.endpoint selected).mp witness.covers }
  | .negative refuted =>
      .negative (fun pumpable => refuted ((pumpable_iff_coverable net before selected).mp pumpable))

theorem classifyPump_exact (net : Thesis.Causality.PetriNet places transitions)
    (before : Marking places) (selected : Fin places → Bool) :
    (net.classifyPump before selected).isPositive = true ↔ net.Pumpable before selected :=
  (net.classifyPump before selected).positive_exact

theorem classifyPump_negative_iff (net : Thesis.Causality.PetriNet places transitions)
    (before : Marking places) (selected : Fin places → Bool) :
    (net.classifyPump before selected).isPositive = false ↔ ¬ net.Pumpable before selected := by
  cases result : net.classifyPump before selected with
  | positive witness =>
      constructor
      · intro impossible; cases impossible
      · intro refuted; exact False.elim (refuted witness.pumpable)
  | negative refuted => exact ⟨fun _ => refuted, fun _ => rfl⟩

def BackwardPumpable (net : Thesis.Causality.PetriNet places transitions)
    (before : Marking places) (selected : Fin places → Bool) : Prop :=
  ∃ word larger, net.Execution larger word before ∧ GrowsOn before larger selected

theorem backwardPumpable_iff_reverse (net : Thesis.Causality.PetriNet places transitions)
    (before : Marking places) (selected : Fin places → Bool) :
    net.BackwardPumpable before selected ↔ net.reverse.Pumpable before selected := by
  constructor
  · rintro ⟨word, larger, execution, grows⟩
    exact ⟨word.reverse, larger, execution.reverse, grows⟩
  · rintro ⟨word, larger, execution, grows⟩
    exact ⟨word.reverse, larger, by simpa only [reverse_reverse] using execution.reverse, grows⟩

/-- Positive data are stored in the reversed net. `reverse_execution` and
`repeat_reverse_execution` expose their original-net executions explicitly. -/
def classifyBackwardPump (net : Thesis.Causality.PetriNet places transitions)
    (before : Marking places) (selected : Fin places → Bool) : PumpResult net.reverse before selected :=
  net.reverse.classifyPump before selected

theorem classifyBackwardPump_exact (net : Thesis.Causality.PetriNet places transitions)
    (before : Marking places) (selected : Fin places → Bool) :
    (net.classifyBackwardPump before selected).isPositive = true ↔ net.BackwardPumpable before selected :=
  (classifyPump_exact net.reverse before selected).trans (backwardPumpable_iff_reverse net before selected).symm

theorem classifyBackwardPump_negative_iff (net : Thesis.Causality.PetriNet places transitions)
    (before : Marking places) (selected : Fin places → Bool) :
    (net.classifyBackwardPump before selected).isPositive = false ↔ ¬ net.BackwardPumpable before selected := by
  rw [classifyBackwardPump, classifyPump_negative_iff, ← backwardPumpable_iff_reverse]

end Thesis.Causality.PetriNet
