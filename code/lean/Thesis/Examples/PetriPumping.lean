import Thesis.Causality.PetriPumping

namespace Thesis.Causality.Examples.PetriPumping

open Thesis.Causality.PetriNet

/-!
# Finite-marking pumping and its boundedness boundary

The positive fixtures retain actual words and check their exact successors.
The general repetition theorem supplies executions at every natural count;
the classifier regressions use its proved exactness, not kernel evaluation
of the whole well-founded coverability solver. A two-transition transfer
also makes literal reversal order observable.

The three-place switch is the important negative regression. Its first
token is spent once to activate growth of the third coordinate. Every
requested third-coordinate value is then reachable, but no growing word
can restore the first token required by the original source. Failure of
that source's pumping test therefore does not bound the selected coordinate.
The obstruction concerns every finite word, not a bounded unsuccessful run.

Empty selections, zero places and zero transitions retain their intended
semantics. No runtime pilot or exact-reachability algorithm is added here.
-/

def tokens (count : Nat) : Marking 1 := fun _ => count

def growth : Thesis.Causality.PetriNet 1 1 where
  consume := fun _ _ => 1
  produce := fun _ _ => 2

def growthPump : PumpWitness growth (tokens 1) (fun _ => true) where
  word := [0]
  endpoint := tokens 2
  execution := (check_exact growth _ _ _).mp (by decide +kernel)
  grows := (pumpTarget_exact _ _ _).mp (by unfold Below; decide +kernel)

theorem growth_positive : (growth.classifyPump (tokens 1) (fun _ => true)).isPositive = true :=
  (classifyPump_exact _ _ _).mpr growthPump.pumpable

theorem growth_word_nonempty : growthPump.word ≠ [] := growthPump.word_ne_nil 0 rfl

theorem growth_repeated_endpoint (steps : Nat) :
    growthPump.iteratedEndpoint steps = tokens (1 + steps) := by
  funext place
  change 1 + steps * 1 = 1 + steps
  rw [Nat.mul_one]

theorem growth_repeated_execution (steps : Nat) :
    growth.Execution (tokens 1) (repeatWord [0] steps) (tokens (1 + steps)) := by
  have execution := growthPump.repeat_execution steps
  rw [growth_repeated_endpoint] at execution
  exact execution

theorem growth_zero_negative : (growth.classifyPump (tokens 0) (fun _ => true)).isPositive = false := by
  apply (classifyPump_negative_iff _ _ _).mpr
  rintro ⟨word, after, execution, grows⟩
  cases execution with
  | nil => exact Nat.lt_irrefl 0 (grows.2 0 rfl)
  | cons fired remaining =>
      have impossible := fired.1 (0 : Fin 1)
      change 1 ≤ 0 at impossible
      omega

/-- Draining cannot grow from one token, but its reverse can. Backward
positive words are actual executions from their larger original-net source. -/
def draining := growth.reverse

theorem draining_forward_negative :
    (draining.classifyPump (tokens 1) (fun _ => true)).isPositive = false := by
  apply (classifyPump_negative_iff _ _ _).mpr
  rintro ⟨word, after, execution, grows⟩
  cases execution with
  | nil => exact Nat.lt_irrefl 1 (grows.2 0 rfl)
  | cons fired remaining =>
      have impossible := fired.1 (0 : Fin 1)
      change 2 ≤ 1 at impossible
      omega

theorem draining_backward_positive :
    (draining.classifyBackwardPump (tokens 1) (fun _ => true)).isPositive = true :=
  (classifyBackwardPump_exact _ _ _).mpr
    ⟨[0], tokens 2, growthPump.execution.reverse, growthPump.grows⟩

theorem draining_backward_repeated (steps : Nat) :
    draining.Execution (tokens (1 + steps)) (repeatWord [0] steps).reverse (tokens 1) :=
  (growth_repeated_execution steps).reverse

def pair (first second : Nat) : Marking 2 := fun place => if place = 0 then first else second

def transfer : Thesis.Causality.PetriNet 2 2 where
  consume := fun transition => if transition = 0 then pair 2 0 else pair 0 1
  produce := fun transition => if transition = 0 then pair 0 1 else pair 1 0

theorem transfer_forward : transfer.Execution (pair 2 0) [0, 1] (pair 1 0) :=
  (check_exact transfer _ _ _).mp (by decide +kernel)

theorem transfer_reversed : transfer.reverse.Execution (pair 1 0) [1, 0] (pair 2 0) :=
  transfer_forward.reverse

theorem unreversed_order_rejected : transfer.reverse.check (pair 1 0) [0, 1] (pair 2 0) = false := by
  decide +kernel

def pairGrowth : Thesis.Causality.PetriNet 2 1 where
  consume := fun _ => pair 1 1
  produce := fun _ => pair 2 3

def pairPump : PumpWitness pairGrowth (pair 1 1) (fun _ => true) where
  word := [0]
  endpoint := pair 2 3
  execution := (check_exact pairGrowth _ _ _).mp (by decide +kernel)
  grows := (pumpTarget_exact _ _ _).mp (by unfold Below; decide +kernel)

theorem simultaneous_growth_positive :
    (pairGrowth.classifyPump (pair 1 1) (fun _ => true)).isPositive = true :=
  (classifyPump_exact _ _ _).mpr pairPump.pumpable

theorem simultaneous_threshold (threshold : Nat) :
    1 + threshold ≤ pairPump.iteratedEndpoint threshold 0 ∧
      1 + threshold ≤ pairPump.iteratedEndpoint threshold 1 :=
  ⟨pairPump.repeat_above threshold 0 rfl, pairPump.repeat_above threshold 1 rfl⟩

theorem empty_selection_positive (net : Thesis.Causality.PetriNet places transitions) (before : Marking places) :
    (net.classifyPump before (fun _ => false)).isPositive = true := by
  apply (classifyPump_exact _ _ _).mpr
  exact ⟨[], before, .nil _, Below.refl _, fun _ impossible => by cases impossible⟩

theorem zero_places_positive (net : Thesis.Causality.PetriNet 0 transitions) (before : Marking 0)
    (selected : Fin 0 → Bool) : (net.classifyPump before selected).isPositive = true := by
  apply (classifyPump_exact _ _ _).mpr
  exact ⟨[], before, .nil _, Below.refl _, fun place => Fin.elim0 place⟩

def noTransitions : Thesis.Causality.PetriNet 1 0 where
  consume := Fin.elim0
  produce := Fin.elim0

theorem no_transitions_negative :
    (noTransitions.classifyPump (tokens 1) (fun _ => true)).isPositive = false := by
  apply (classifyPump_negative_iff _ _ _).mpr
  rintro ⟨word, after, execution, grows⟩
  cases execution with
  | nil => exact Nat.lt_irrefl 1 (grows.2 0 rfl)
  | @cons before middle after transition rest fired remaining => exact Fin.elim0 transition

/-! The switch consumes its unique seed. Growth preserves the activation
token and adds one output token. All three are actual Petri places; the
activation is not an external control-state assumption. -/

def triple (seed active output : Nat) : Marking 3 :=
  fun place => if place = 0 then seed else if place = 1 then active else output

def switchedGrowth : Thesis.Causality.PetriNet 3 2 where
  consume := fun transition => if transition = 0 then triple 1 0 0 else triple 0 1 0
  produce := fun transition => if transition = 0 then triple 0 1 0 else triple 0 1 1

def thirdOnly : Fin 3 → Bool := fun place => decide (place = 2)

def activePump : PumpWitness switchedGrowth (triple 0 1 0) thirdOnly where
  word := [1]
  endpoint := triple 0 1 1
  execution := (check_exact switchedGrowth _ _ _).mp (by decide +kernel)
  grows := (pumpTarget_exact _ _ _).mp (by unfold Below; decide +kernel)

theorem active_repeated_endpoint (steps : Nat) : activePump.iteratedEndpoint steps = triple 0 1 steps := by
  funext place
  by_cases seed : place = 0
  · subst place
    change 0 + steps * 0 = 0
    rw [Nat.mul_zero]
  · by_cases active : place = 1
    · subst place
      change 1 + steps * 0 = 1
      rw [Nat.mul_zero, Nat.add_zero]
    · have output : place = 2 := by omega
      subst place
      change 0 + steps * 1 = steps
      rw [Nat.mul_one, Nat.zero_add]

theorem switched_execution (steps : Nat) :
    switchedGrowth.Execution (triple 1 0 0) ([0] ++ repeatWord [1] steps) (triple 0 1 steps) := by
  have switch : switchedGrowth.Execution (triple 1 0 0) [0] (triple 0 1 0) :=
    (check_exact switchedGrowth _ _ _).mp (by decide +kernel)
  have grow := activePump.repeat_execution steps
  rw [active_repeated_endpoint] at grow
  exact switch.append grow

/-- If the seed still exists, no output has yet been produced. This
invariant rules out every returning pump, despite arbitrary later growth. -/
private def SeedInvariant (marking : Marking 3) : Prop :=
  marking 0 + marking 1 = 1 ∧ (marking 0 = 1 → marking 2 = 0)

private theorem seedInvariant_preserved (before : Marking 3) (transition : Fin 2) (after : Marking 3)
    (fired : switchedGrowth.Fires before transition after) (invariant : SeedInvariant before) :
    SeedInvariant after := by
  have seed := congrFun fired.2 (0 : Fin 3)
  have active := congrFun fired.2 (1 : Fin 3)
  by_cases switch : transition = 0
  · subst transition
    have ready := fired.1 (0 : Fin 3)
    change 1 ≤ before 0 at ready
    change after 0 = before 0 - 1 at seed
    change after 1 = before 1 + 1 at active
    constructor
    · have sum := invariant.1
      omega
    · intro impossible
      have sum := invariant.1
      exact False.elim (by omega)
  · have grow : transition = 1 := by omega
    subst transition
    have ready := fired.1 (1 : Fin 3)
    change 1 ≤ before 1 at ready
    change after 0 = before 0 at seed
    change after 1 = before 1 - 1 + 1 at active
    constructor
    · have sum := invariant.1
      omega
    · intro impossible
      have sum := invariant.1
      exact False.elim (by omega)

theorem original_source_not_pumpable : ¬ switchedGrowth.Pumpable (triple 1 0 0) thirdOnly := by
  rintro ⟨word, after, execution, grows⟩
  have initial : SeedInvariant (triple 1 0 0) := ⟨rfl, fun _ => rfl⟩
  have invariant := execution.preserves SeedInvariant seedInvariant_preserved initial
  have seed := grows.1 (0 : Fin 3)
  change 1 ≤ after 0 at seed
  have same : after 0 = 1 := by have sum := invariant.1; omega
  have outputZero := invariant.2 same
  have strict := grows.2 (2 : Fin 3) rfl
  change 0 < after 2 at strict
  omega

theorem selected_coordinate_unbounded (threshold : Nat) :
    ∃ word after, switchedGrowth.Execution (triple 1 0 0) word after ∧ threshold ≤ after 2 :=
  ⟨[0] ++ repeatWord [1] threshold, triple 0 1 threshold, switched_execution threshold, Nat.le_refl _⟩

/-- A negative pumping answer refutes returning growth at the supplied
source. It does not refute arbitrarily large reachable selected values. -/
theorem failed_pump_does_not_bound_selected_coordinate :
    (switchedGrowth.classifyPump (triple 1 0 0) thirdOnly).isPositive = false ∧
      ∀ threshold, ∃ word after,
        switchedGrowth.Execution (triple 1 0 0) word after ∧ threshold ≤ after 2 :=
  ⟨(classifyPump_negative_iff _ _ _).mpr original_source_not_pumpable, selected_coordinate_unbounded⟩

end Thesis.Causality.Examples.PetriPumping
