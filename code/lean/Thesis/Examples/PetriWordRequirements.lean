import Thesis.Causality.PetriWordRequirements
import Thesis.Causality.PetriControl

namespace Thesis.Causality.Examples.PetriWordRequirements

open Thesis.Causality.PetriNet

/-!
# Guards, common surplus and the order of resource quantifiers

A zero-effect edge still needs its consumed tokens. Likewise, two words
with the same transition counts can have different least sources because
their prefix guards differ. The exact pair also admits draining words;
it is not restricted to the nonnegative gains of a pumping witness.

The transfer fixture supplies a finite resource family for every repetition
count, but no one finite source enables all counts. Both claims are proved
for arbitrary counts. All concrete executions use the given word, and the
general pair theorem keeps the same surplus at both endpoints.

An invalid control path remains invalid even when its counter word has no
initial requirements. These examples add no partial-endpoint classifier,
unbounded word search, native decision axiom or runtime pilot.
-/

def tokens (count : Nat) : Marking 1 := fun _ => count

def guardedLoop : Thesis.Causality.PetriNet 1 1 where
  consume := fun _ _ => 2
  produce := fun _ _ => 2

theorem zero_effect_guard_retained :
    (guardedLoop.wordRequirements [0]).source = tokens 2 ∧
      (guardedLoop.wordRequirements [0]).endpoint = tokens 2 := ⟨rfl, rfl⟩

theorem insufficient_tokens_rejected : guardedLoop.run (tokens 1) [0] = none := by decide +kernel

/-- Both endpoints receive five extra tokens. This uses the general
word-pair theorem, rather than evaluating a new search procedure. -/
theorem common_surplus_execution : guardedLoop.run (tokens 7) [0] = some (tokens 7) :=
  ((guardedLoop.wordRequirements [0]).run_exact _ _).mpr ⟨tokens 5, rfl, rfl⟩

theorem independent_endpoint_padding_rejected : ¬ guardedLoop.Execution (tokens 2) [0] (tokens 3) := by
  intro execution
  obtain ⟨extra, source, endpoint⟩ := ((guardedLoop.wordRequirements [0]).execution_iff _ _).mp execution
  have first := congrFun source (0 : Fin 1)
  have last := congrFun endpoint (0 : Fin 1)
  change 2 = 2 + extra 0 at first
  change 3 = 2 + extra 0 at last
  omega

def ordered : Thesis.Causality.PetriNet 1 2 where
  consume := fun edge _ => if edge = 0 then 2 else 0
  produce := fun edge _ => if edge = 0 then 0 else 2

/-- The words have identical overall effect and identical edge counts,
but producing before consuming changes the exact initial requirement. -/
theorem order_changes_requirements :
    (ordered.wordRequirements [0, 1]).source = tokens 2 ∧
      (ordered.wordRequirements [1, 0]).source = tokens 0 ∧
      ordered.run (tokens 0) [0, 1] = none ∧
      ordered.run (tokens 0) [1, 0] = some (tokens 0) := by
  exact ⟨rfl, rfl, by decide +kernel, rfl⟩

def draining : Thesis.Causality.PetriNet 1 1 where
  consume := fun _ _ => 3
  produce := fun _ _ => 1

theorem draining_pair :
    (draining.wordRequirements [0]).source = tokens 3 ∧
      (draining.wordRequirements [0]).endpoint = tokens 1 ∧
      draining.run (tokens 5) [0] = some (tokens 3) :=
  ⟨rfl, rfl, ((draining.wordRequirements [0]).run_exact _ _).mpr ⟨tokens 2, rfl, rfl⟩⟩

/-- A paired query retains the second firing's prefix guard: an overall
loss of four tokens still requires five initially, not merely four. -/
theorem paired_draining_prefix_guards :
    draining.wordRequirementsAt [0, 0] 0 = (5, 1) ∧
      draining.run (tokens 4) [0, 0] = none ∧
      draining.run (tokens 5) [0, 0] = some (tokens 1) :=
  ⟨rfl, by decide +kernel, rfl⟩

theorem empty_word_preserves_endpoint (net : Thesis.Causality.PetriNet places transitions)
    (before after : Marking places) :
    net.Execution before [] after ↔ before = after := by
  constructor
  · intro execution
    cases execution
    rfl
  · intro equal
    cases equal
    exact .nil _

theorem zero_places_word (net : Thesis.Causality.PetriNet 0 transitions) (word : List (Fin transitions)) :
    net.Execution Fin.elim0 word Fin.elim0 := by
  have execution := (net.wordRequirements word).execution
  have source : (net.wordRequirements word).source = Fin.elim0 := by funext place; exact Fin.elim0 place
  have endpoint : (net.wordRequirements word).endpoint = Fin.elim0 := by funext place; exact Fin.elim0 place
  simpa only [source, endpoint] using execution

def wrongControl : ControlledPetriNet 1 2 1 where
  net := { consume := fun _ _ => 0, produce := fun _ _ => 1 }
  source := fun _ => 1
  target := fun _ => 1

theorem counter_requirements_do_not_remove_control_guards :
    (wrongControl.net.wordRequirements [0]).source = tokens 0 ∧
      ¬ wrongControl.Execution 0 (tokens 0) [0] 1 (tokens 1) := by
  refine ⟨rfl, ?_⟩
  intro execution
  have impossible := execution.1
  change none = some (1 : Fin 2) at impossible
  cases impossible

def pair (first second : Nat) : Marking 2 := fun place => if place = 0 then first else second

def transfer : Thesis.Causality.PetriNet 2 1 where
  consume := fun _ => pair 0 1
  produce := fun _ => pair 1 0

/-- Exactly one initial second-coordinate token is needed per copy.
The first coordinate starts at zero and receives all transferred tokens. -/
theorem transfer_pair (steps : Nat) :
    (transfer.wordRequirements (List.replicate steps 0)).source = pair 0 steps ∧
      (transfer.wordRequirements (List.replicate steps 0)).endpoint = pair steps 0 := by
  induction steps with
  | zero =>
      constructor
      · rw [List.replicate_zero, wordRequirements_nil_source]
        funext place
        simp only [pair, ite_self]
      · rw [List.replicate_zero, wordRequirements_nil_endpoint]
        funext place
        simp only [pair, ite_self]
  | succ steps ih =>
      constructor
      · rw [List.replicate_succ, wordRequirements_cons_source, ih.1]
        funext place
        by_cases first : place = 0
        · subst place
          change 0 + (0 - 1) = 0
          rfl
        · have second : place = 1 := by omega
          subst place
          change 1 + (steps - 0) = steps + 1
          omega
      · rw [List.replicate_succ, wordRequirements_cons_endpoint, ih.1, ih.2]
        funext place
        by_cases first : place = 0
        · subst place
          change steps + (1 - 0) = steps + 1
          rfl
        · have second : place = 1 := by omega
          subst place
          change 0 + (0 - steps) = 0
          omega

theorem transfer_with_per_count_supply (steps : Nat) :
    transfer.Execution (pair 0 steps) (List.replicate steps 0) (pair steps 0) := by
  have execution := (transfer.wordRequirements (List.replicate steps 0)).execution
  rw [(transfer_pair steps).1, (transfer_pair steps).2] at execution
  exact execution

/-- A finite second coordinate is exhausted after that many copies,
independently of the first coordinate or the requested final marking. -/
theorem no_uniform_finite_supply :
    ¬ ∃ before : Marking 2, ∀ steps, ∃ after,
      transfer.Execution before (List.replicate steps 0) after := by
  rintro ⟨before, allCounts⟩
  obtain ⟨after, execution⟩ := allCounts (before 1 + 1)
  have bound := (transfer.wordRequirements (List.replicate (before 1 + 1) 0)).least execution (1 : Fin 2)
  rw [(transfer_pair (before 1 + 1)).1] at bound
  change before 1 + 1 ≤ before 1 at bound
  omega

theorem per_repetition_supply_not_uniform :
    (∀ steps, transfer.Execution (pair 0 steps) (List.replicate steps 0) (pair steps 0)) ∧
      ¬ ∃ before : Marking 2, ∀ steps, ∃ after,
        transfer.Execution before (List.replicate steps 0) after :=
  ⟨transfer_with_per_count_supply, no_uniform_finite_supply⟩

end Thesis.Causality.Examples.PetriWordRequirements
