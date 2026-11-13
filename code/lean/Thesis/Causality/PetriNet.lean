import Std

namespace Thesis.Causality

/-!
# Finite Petri nets and exact checking of supplied executions

Places and transitions have explicit finite indices. A marking assigns an
arbitrary natural number to each place: finiteness of the net never imposes
a bound on token counts or on the set of reachable markings. Consumption
must be enabled before subtraction is performed, so truncated natural
subtraction cannot manufacture a firing from an insufficient marking.

The relational execution semantics is independent of the executable checker.
The checker consumes one supplied transition word and compares the complete
resulting marking with its requested target, including for an empty word.
Its correctness theorem is exact reachability along that word, rather than
coverability or satisfaction of a linear balance equation. Finite coordinate
comparisons supply all equality decisions; no arbitrary function-equality
instance, choice of an execution, or general excluded middle is used.

Composition and invariant preservation are reusable execution theorems.
Reachable and Coverable quantify over unbounded finite executions, but this
module supplies no decision procedure for either existential problem. There
is no AC encoding, probability-formula search or terminating general solver
at this foundational stage.
-/

structure PetriNet (places transitions : Nat) where
  consume : Fin transitions → Fin places → Nat
  produce : Fin transitions → Fin places → Nat

namespace PetriNet

abbrev Marking (places : Nat) := Fin places → Nat

variable {places transitions : Nat}

/-- Pointwise comparison has its usual direction: the upper marking has
at least every token requested by the lower marking. -/
def Below (lower upper : Marking places) : Prop :=
  ∀ place, lower place ≤ upper place

/-- Compare every coordinate, without a global equality decision for
functions. In zero places the comparison is correctly vacuous. -/
def markingEq (left right : Marking places) : Bool :=
  (List.finRange places).all (fun place => decide (left place = right place))

theorem markingEq_exact (left right : Marking places) :
    markingEq left right = true ↔ left = right := by
  simp only [markingEq, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro equal
    funext place
    exact equal place (List.mem_finRange place)
  · intro equal place _
    exact congrFun equal place

def Enabled (net : PetriNet places transitions) (before : Marking places)
    (transition : Fin transitions) : Prop :=
  Below (net.consume transition) before

def enabled (net : PetriNet places transitions) (before : Marking places)
    (transition : Fin transitions) : Bool :=
  (List.finRange places).all (fun place => decide (net.consume transition place ≤ before place))

theorem enabled_exact (net : PetriNet places transitions) (before : Marking places)
    (transition : Fin transitions) : net.enabled before transition = true ↔ net.Enabled before transition := by
  simp only [enabled, Enabled, Below, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro ready place
    exact ready place (List.mem_finRange place)
  · intro ready place _
    exact ready place

/-- Independent one-step semantics: enabling and the entire resulting
marking are both required. A larger marking is not an exact result. -/
def Fires (net : PetriNet places transitions) (before : Marking places)
    (transition : Fin transitions) (after : Marking places) : Prop :=
  net.Enabled before transition ∧
    after = fun place => before place - net.consume transition place + net.produce transition place

def fire (net : PetriNet places transitions) (before : Marking places)
    (transition : Fin transitions) : Option (Marking places) :=
  if net.enabled before transition then
    some (fun place => before place - net.consume transition place + net.produce transition place)
  else none

theorem fire_eq_some_iff (net : PetriNet places transitions) (before after : Marking places)
    (transition : Fin transitions) : net.fire before transition = some after ↔ net.Fires before transition after := by
  unfold fire
  split
  · next ready =>
      constructor
      · intro equal
        exact ⟨(enabled_exact net before transition).mp ready, (Option.some.inj equal).symm⟩
      · intro step
        exact congrArg some step.2.symm
  · next blocked =>
      constructor
      · intro impossible
        cases impossible
      · intro step
        exact False.elim (blocked ((enabled_exact net before transition).mpr step.1))

/-- Every intermediate marking belongs to the relational semantics;
neither a firing failure nor a mismatched endpoint is silently discarded. -/
inductive Execution (net : PetriNet places transitions) :
    Marking places → List (Fin transitions) → Marking places → Prop where
  | nil (before) : Execution net before [] before
  | cons {before middle after transition rest} :
      net.Fires before transition middle → Execution net middle rest after →
        Execution net before (transition :: rest) after

def run (net : PetriNet places transitions) :
    Marking places → List (Fin transitions) → Option (Marking places)
  | before, [] => some before
  | before, transition :: rest =>
      (net.fire before transition).bind (fun middle => net.run middle rest)

/-- Exact correspondence for any supplied finite word. The proof derives
all intermediate markings from the actual option computations. -/
theorem run_eq_some_iff (net : PetriNet places transitions) (before after : Marking places)
    (word : List (Fin transitions)) : net.run before word = some after ↔ net.Execution before word after := by
  induction word generalizing before after with
  | nil =>
      constructor
      · intro equal
        cases Option.some.inj equal
        exact .nil _
      · intro execution
        cases execution
        rfl
  | cons transition rest ih =>
      change (net.fire before transition).bind (fun middle => net.run middle rest) = some after ↔ _
      rw [Option.bind_eq_some_iff]
      constructor
      · rintro ⟨middle, fired, remaining⟩
        exact .cons ((fire_eq_some_iff net before middle transition).mp fired) ((ih middle after).mp remaining)
      · intro execution
        cases execution with
        | cons fired remaining =>
            exact ⟨_, (fire_eq_some_iff net _ _ transition).mpr fired, (ih _ after).mpr remaining⟩

/-- Check the requested endpoint after executing the whole word. The
empty word therefore succeeds exactly when the two markings are equal. -/
def check (net : PetriNet places transitions) (before : Marking places)
    (word : List (Fin transitions)) (after : Marking places) : Bool :=
  match net.run before word with
  | none => false
  | some actual => markingEq actual after

theorem check_exact (net : PetriNet places transitions) (before after : Marking places)
    (word : List (Fin transitions)) : net.check before word after = true ↔ net.Execution before word after := by
  rw [← run_eq_some_iff]
  unfold check
  cases computed : net.run before word with
  | none => simp only [Bool.false_eq_true, reduceCtorEq]
  | some actual =>
      constructor
      · intro accepted
        exact congrArg some ((markingEq_exact actual after).mp accepted)
      · intro equal
        exact (markingEq_exact actual after).mpr (Option.some.inj equal)

theorem check_nil (net : PetriNet places transitions) (before after : Marking places) :
    net.check before [] after = true ↔ before = after := markingEq_exact before after

/-- Execution is sequential composition, retaining the middle marking
actually computed by the first word. Failed prefixes remain failed. -/
theorem run_append (net : PetriNet places transitions) (before : Marking places)
    (first second : List (Fin transitions)) :
    net.run before (first ++ second) = (net.run before first).bind (fun middle => net.run middle second) := by
  induction first generalizing before with
  | nil => rfl
  | cons transition rest ih =>
      simp only [List.cons_append, run]
      cases computed : net.fire before transition with
      | none => rfl
      | some middle => exact ih middle

theorem Execution.append {net : PetriNet places transitions} {before middle after : Marking places}
    {first second : List (Fin transitions)} (left : net.Execution before first middle)
    (right : net.Execution middle second after) : net.Execution before (first ++ second) after := by
  apply (run_eq_some_iff net _ _ _).mp
  rw [run_append, (run_eq_some_iff net _ _ _).mpr left, Option.bind_some]
  exact (run_eq_some_iff net _ _ _).mpr right

/-- An invariant is proved for actual enabled firings, not merely for
the integer displacement equation of a transition. -/
theorem Execution.preserves {net : PetriNet places transitions} (property : Marking places → Prop)
    (closed : ∀ before transition after, net.Fires before transition after → property before → property after)
    {before after : Marking places} {word : List (Fin transitions)}
    (execution : net.Execution before word after) : property before → property after := by
  induction execution with
  | nil => exact id
  | cons fired remaining ih =>
      intro initial
      exact ih (closed _ _ _ fired initial)

def Reachable (net : PetriNet places transitions) (before after : Marking places) : Prop :=
  ∃ word, net.Execution before word after

theorem reachable_refl (net : PetriNet places transitions) (before : Marking places) : net.Reachable before before :=
  ⟨[], .nil _⟩

theorem Reachable.trans {net : PetriNet places transitions} {before middle after : Marking places}
    (left : net.Reachable before middle) (right : net.Reachable middle after) : net.Reachable before after := by
  rcases left with ⟨first, left⟩
  rcases right with ⟨second, right⟩
  exact ⟨first ++ second, left.append right⟩

/-- Coverability permits a larger final marking; exact reachability
requires equality. No decision of either unbounded existential is inferred. -/
def Coverable (net : PetriNet places transitions) (before target : Marking places) : Prop :=
  ∃ after, net.Reachable before after ∧ Below target after

theorem Reachable.coverable {net : PetriNet places transitions} {before after : Marking places}
    (reachable : net.Reachable before after) : net.Coverable before after :=
  ⟨after, reachable, fun _ => Nat.le_refl _⟩

end PetriNet
end Thesis.Causality
