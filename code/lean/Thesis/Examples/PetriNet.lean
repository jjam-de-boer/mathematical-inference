import Thesis.Causality.PetriNet

namespace Thesis.Causality.Examples.PetriNet

open Thesis.Causality.PetriNet

/-!
# A coverable target that no execution reaches

The sole transition consumes one token and produces three. Starting with
one token, every firing adds exactly two, so every finite execution ends
with one plus twice its length. Three tokens cover the target of two tokens,
but the length identity rules out exact reachability of two for every word.
This is an unbounded mathematical obstruction, not an unsuccessful bounded
search or a runtime observation. Explicit executions also reach arbitrarily
large markings; no finite token bound is hidden in the definitions.

Small checked examples separately exercise insufficient consumption and the
empty-word endpoint comparison. They are kernel-checked decisions of supplied
words, never a native execution axiom or a general reachability algorithm.
-/

def growth : Causality.PetriNet 1 1 where
  consume := fun _ _ => 1
  produce := fun _ _ => 3

def marking (tokens : Nat) : Marking 1 := fun _ => tokens

private theorem firing_adds_two {before after : Marking 1} {transition : Fin 1}
    (step : growth.Fires before transition after) : after 0 = before 0 + 2 := by
  have ready := step.1 0
  have result := congrFun step.2 0
  change 1 ≤ before 0 at ready
  change after 0 = before 0 - 1 + 3 at result
  omega

/-- The number of firings controls every possible result, not only the
particular execution words used by the following positive witnesses. -/
theorem execution_tokens {before after : Marking 1} {word : List (Fin 1)}
    (execution : growth.Execution before word after) : after 0 = before 0 + 2 * word.length := by
  induction execution with
  | nil => simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]
  | cons fired remaining ih =>
      have changed := firing_adds_two fired
      simp only [List.length_cons]
      omega

theorem one_firing_checked : growth.check (marking 1) [0] (marking 3) = true := by decide +kernel

theorem two_coverable : growth.Coverable (marking 1) (marking 2) := by
  refine ⟨marking 3, ⟨[0], (check_exact growth _ _ _).mp one_firing_checked⟩, ?_⟩
  intro place
  exact Nat.le_of_lt (by decide : 2 < 3)

/-- No length bound is imposed on the rejected execution word. -/
theorem two_not_reachable : ¬ growth.Reachable (marking 1) (marking 2) := by
  rintro ⟨word, execution⟩
  have count := execution_tokens execution
  change 2 = 1 + 2 * word.length at count
  omega

theorem coverability_does_not_imply_reachability :
    growth.Coverable (marking 1) (marking 2) ∧ ¬ growth.Reachable (marking 1) (marking 2) :=
  ⟨two_coverable, two_not_reachable⟩

/-- These are explicit finite executions for every natural number of
steps, rather than representatives selected from an existential statement. -/
theorem repeated_execution (steps : Nat) :
    growth.Execution (marking 1) (List.replicate steps 0) (marking (1 + 2 * steps)) := by
  induction steps with
  | zero => exact .nil _
  | succ steps ih =>
      have next : growth.Execution (marking (1 + 2 * steps)) [0] (marking (1 + 2 * (steps + 1))) := by
        refine .cons ?_ (.nil _)
        constructor
        · intro place
          change 1 ≤ 1 + 2 * steps
          omega
        · funext place
          change 1 + 2 * (steps + 1) = (1 + 2 * steps) - 1 + 3
          omega
      simpa only [List.replicate_succ'] using ih.append next

theorem arbitrarily_large_reachable (bound : Nat) :
    ∃ after, growth.Reachable (marking 1) after ∧ bound ≤ after 0 := by
  refine ⟨marking (1 + 2 * bound), ⟨List.replicate bound 0, repeated_execution bound⟩, ?_⟩
  change bound ≤ 1 + 2 * bound
  omega

theorem insufficient_tokens_rejected : growth.check (marking 0) [0] (marking 3) = false := by decide +kernel
theorem empty_word_wrong_target_rejected : growth.check (marking 1) [] (marking 2) = false := by decide +kernel
theorem empty_word_same_target_checked : growth.check (marking 1) [] (marking 1) = true := by decide +kernel

end Thesis.Causality.Examples.PetriNet
