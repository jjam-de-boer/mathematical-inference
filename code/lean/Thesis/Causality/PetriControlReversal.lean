import Thesis.Causality.PetriControl
import Thesis.Causality.PetriReversal

namespace Thesis.Causality.ControlledPetriNet

open PetriNet

/-!
# Reversal of actual controlled executions

Reversing a controlled system exchanges both the counter consumption and
production tables and every edge's source and destination states. Transition
indices are retained. Reversing only the counter displacement would forget
control guards, including those of a self-loop.

Compilation commutes with this construction. The existing raw execution
reversal can therefore be decoded from its known encoded source, keeping
the reversed literal word and both exact endpoints. This route does not
attempt to decode an unknown original source from an encoded final marking.
No reversal equivalence for coverability is asserted: coverability permits
counter overshoot, whereas these execution statements retain exact endpoints.
-/

variable {places states transitions : Nat}
variable {system : ControlledPetriNet places states transitions}

def reverse (system : ControlledPetriNet places states transitions) :
    ControlledPetriNet places states transitions where
  net := system.net.reverse
  source := system.target
  target := system.source

theorem reverse_reverse (system : ControlledPetriNet places states transitions) :
    system.reverse.reverse = system := rfl

/-- Each compiled table is literally the corresponding swapped table;
the control token's consumption and production are reversed as well. -/
theorem compiled_reverse (system : ControlledPetriNet places states transitions) :
    system.reverse.compiled = system.compiled.reverse := rfl

theorem Fires.reverse {state next : Fin states} {before after : Marking places} {edge : Fin transitions}
    (fired : system.Fires state before edge next after) :
    system.reverse.Fires next after edge state before :=
  ⟨fired.2.1, fired.1, fired.2.2.reverse⟩

theorem fires_reverse_iff (system : ControlledPetriNet places states transitions)
    (state next : Fin states) (before after : Marking places) (edge : Fin transitions) :
    system.reverse.Fires next after edge state before ↔ system.Fires state before edge next after :=
  ⟨fun fired => fired.reverse, fun fired => fired.reverse⟩

/-- Decode in the reversed system, starting at the known original final
configuration. Every counter enabling condition is retained by raw reversal. -/
theorem Execution.reverse {state next : Fin states} {before after : Marking places}
    {word : List (Fin transitions)} (execution : system.Execution state before word next after) :
    system.reverse.Execution next after word.reverse state before := by
  apply (execution_compiled_iff system.reverse _ _ _ _ _).mp
  simpa only [compiled_reverse] using execution.compile.reverse

theorem execution_reverse_iff (system : ControlledPetriNet places states transitions)
    (state next : Fin states) (before after : Marking places) (word : List (Fin transitions)) :
    system.reverse.Execution next after word.reverse state before ↔
      system.Execution state before word next after := by
  constructor
  · intro execution
    simpa only [reverse_reverse, List.reverse_reverse] using execution.reverse
  · exact Execution.reverse

theorem Reachable.reverse {state next : Fin states} {before after : Marking places}
    (reachable : system.Reachable state before next after) :
    system.reverse.Reachable next after state before := by
  rcases reachable with ⟨word, execution⟩
  exact ⟨word.reverse, execution.reverse⟩

theorem reachable_reverse_iff (system : ControlledPetriNet places states transitions)
    (state next : Fin states) (before after : Marking places) :
    system.reverse.Reachable next after state before ↔ system.Reachable state before next after :=
  ⟨fun reachable => reachable.reverse, fun reachable => reachable.reverse⟩

end Thesis.Causality.ControlledPetriNet
