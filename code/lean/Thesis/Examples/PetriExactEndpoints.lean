import Thesis.Causality.PetriExactEndpointReduction

namespace Thesis.Causality.Examples.PetriExactEndpoints

open PetriNet Thesis.Causality.PetriExactEndpoints

/-!
# Exact endpoint reduction regressions

The positive run supplies a token in setup, transfers it along a
state-changing edge, and drains the two produced tokens in cleanup.
Decoding recovers the actual original endpoints, including the nonzero
counter before cleanup. Alternative words check the phase boundary and
the distinction between leaving a counter free and fixing it exactly.
An ordinary net with no places or transitions exercises the empty word.
-/

def counters (first second : Nat) : Marking 2 :=
  fun place => if place = 0 then first else second

def transfer : ControlledPetriNet 2 2 1 where
  net := ⟨fun _ => counters 1 0, fun _ => counters 0 2⟩
  source := fun _ => 0
  target := fun _ => 1

def query : Query 2 2 1 where
  system := transfer
  start := 0
  finish := 1
  source := fun place => if place = 0 then none else some 0
  target := fun place => if place = 0 then some 0 else none

def witness : Witness query where
  before := counters 1 0
  after := counters 0 2
  word := [0]
  source_matches := by
    intro place
    by_cases first : place = 0
    · simp only [query, if_pos first]
    · simp only [query, counters, if_neg first]
  target_matches := by
    intro place
    by_cases first : place = 0
    · simp only [query, counters, if_pos first]
    · simp only [query, if_neg first]
  execution := ⟨rfl, (check_exact transfer.net _ _ _).mp (by decide +kernel)⟩

def label (edge : Edge 2 1) : Fin (edgeCount 2 1) := edge.encode

theorem encoded_word_has_both_adjustments :
    query.encodeWord witness =
      [.fill 0, .enter, .original 0, .leave, .drain 1, .drain 1].map label := rfl

theorem compiled_run_checks :
    query.compiled.check query.initial (query.encodeWord witness) query.final = true := by
  decide +kernel

def decoded : Witness query := query.decode _ ((check_exact query.compiled _ _ _).mp compiled_run_checks)

theorem decoded_values_and_word :
    (decoded.before 0, decoded.before 1, decoded.word, decoded.after 0, decoded.after 1) =
      (1, 0, [0], 0, 2) := rfl

theorem original_edges_require_entering :
    query.compiled.check query.initial
      ([.original 0, .leave, .drain 1, .drain 1].map label) query.final = false := by
  decide +kernel

/-- Cleanup may drain free counters but cannot turn an overshoot of a
fixed target coordinate into an exact hit. -/
def fixedTarget : Query 2 2 1 :=
  { query with target := fun place => if place = 0 then some 0 else some 1 }

theorem fixed_target_cannot_be_drained :
    fixedTarget.compiled.check fixedTarget.initial
      ([.fill 0, .enter, .original 0, .leave, .drain 1].map label) fixedTarget.final = false := by
  decide +kernel

def emptyNet : Thesis.Causality.PetriNet 0 0 := ⟨Fin.elim0, Fin.elim0⟩

def emptyQuery := ordinaryQuery emptyNet Fin.elim0 Fin.elim0

def emptyWitness : Witness emptyQuery where
  before := Fin.elim0
  after := Fin.elim0
  word := []
  source_matches := fun place => Fin.elim0 place
  target_matches := fun place => Fin.elim0 place
  execution := ⟨rfl, .nil _⟩

theorem empty_original_word_still_switches_phases :
    emptyQuery.encodeWord emptyWitness = [Edge.encode .enter, Edge.encode .leave] ∧
      emptyQuery.compiled.check emptyQuery.initial (emptyQuery.encodeWord emptyWitness)
        emptyQuery.final = true :=
  ⟨rfl, by decide +kernel⟩

end Thesis.Causality.Examples.PetriExactEndpoints
