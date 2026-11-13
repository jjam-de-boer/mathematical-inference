import Thesis.Causality.PetriNet

namespace Thesis.Causality.PetriNet

/-!
# Exact reversal of finite Petri executions

Reversal exchanges consumption and production, retaining every transition
index. It does not merely negate a displacement: the reversed transition
must have all the tokens produced by the original transition. Original
enabling and the exact successor equation prove that this requirement holds.

A supplied execution reverses its literal transition word and exchanges its
endpoints. These statements concern enabled executions, including empty
words; neither coverability nor a solution of a token-balance equation is
substituted for execution. The construction later allows backward pumping
to reuse an ordinary forward test, without choosing an existential word.
-/

variable {places transitions : Nat}
variable {net : Thesis.Causality.PetriNet places transitions}

def reverse (net : Thesis.Causality.PetriNet places transitions) :
    Thesis.Causality.PetriNet places transitions where
  consume := net.produce
  produce := net.consume

theorem reverse_reverse (net : Thesis.Causality.PetriNet places transitions) :
    net.reverse.reverse = net := rfl

/-- Enabling is proved before undoing natural subtraction. In particular,
a transition with both consumption and production retains its guard. -/
theorem Fires.reverse {before after : Marking places} {transition : Fin transitions}
    (fired : net.Fires before transition after) : net.reverse.Fires after transition before := by
  constructor
  · intro place
    have ready := fired.1 place
    have result := congrFun fired.2 place
    change after place = before place - net.consume transition place + net.produce transition place at result
    change net.produce transition place ≤ after place
    omega
  · funext place
    have ready := fired.1 place
    have result := congrFun fired.2 place
    change after place = before place - net.consume transition place + net.produce transition place at result
    change before place = after place - net.produce transition place + net.consume transition place
    omega

theorem fires_reverse_iff (net : Thesis.Causality.PetriNet places transitions)
    (before after : Marking places) (transition : Fin transitions) :
    net.reverse.Fires after transition before ↔ net.Fires before transition after :=
  ⟨fun fired => fired.reverse, fun fired => fired.reverse⟩

/-- Reverse the supplied word itself, not only its transition counts. -/
theorem Execution.reverse {before after : Marking places} {word : List (Fin transitions)}
    (execution : net.Execution before word after) :
    net.reverse.Execution after word.reverse before := by
  induction execution with
  | nil => exact .nil _
  | cons fired remaining ih =>
      simpa only [List.reverse_cons] using ih.append (.cons fired.reverse (.nil _))

theorem execution_reverse_iff (net : Thesis.Causality.PetriNet places transitions)
    (before after : Marking places) (word : List (Fin transitions)) :
    net.reverse.Execution after word.reverse before ↔ net.Execution before word after := by
  constructor
  · intro execution
    simpa only [reverse_reverse, List.reverse_reverse] using execution.reverse
  · exact Execution.reverse

theorem Reachable.reverse {before after : Marking places}
    (reachable : net.Reachable before after) : net.reverse.Reachable after before := by
  rcases reachable with ⟨word, execution⟩
  exact ⟨word.reverse, execution.reverse⟩

theorem reachable_reverse_iff (net : Thesis.Causality.PetriNet places transitions)
    (before after : Marking places) : net.reverse.Reachable after before ↔ net.Reachable before after :=
  ⟨fun reachable => reachable.reverse, fun reachable => reachable.reverse⟩

end Thesis.Causality.PetriNet
