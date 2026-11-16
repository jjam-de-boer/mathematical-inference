import Thesis.Causality.PetriWordRequirements

namespace Thesis.Causality.PetriNet

/-!
# Exact completion of partial endpoints for a supplied word

A partial marking fixes a coordinate with `some n` and leaves it unspecified
with `none`. A fixed zero is an exact zero, not an absent constraint. These
are endpoint equalities, not the strict upper bounds of coordinate boxes.

The supplied word's least source and its actual endpoint determine every
execution: both endpoints receive the same nonnegative surplus in each
coordinate. A fixed endpoint forces that coordinate's surplus. Two fixed
endpoints must force the same surplus; with neither fixed, zero suffices.
Values below the canonical pair are rejected before natural subtraction.

The finite coordinate recursion computes actual endpoints and an execution
proof, or refutes every completion for this literal word. Each visited
coordinate requests its canonical pair once and retains its numeric data.
Later endpoint reads do not rerun the word fold. No counter magnitude or word
length cutoff, choice, or general propositional excluded middle is needed.

This is an ordinary-net supplied-word checker. It neither searches for a
word nor validates finite control, and it does not decide exact reachability
when the word is unspecified.
-/

abbrev PartialMarking (places : Nat) := Fin places → Option Nat

variable {places transitions : Nat}
variable {net : Thesis.Causality.PetriNet places transitions}

/-- Every supplied number is retained literally; unknown coordinates impose
no condition. In particular, `some 0` and `none` have different meanings. -/
def PartialMarking.Matches (specified : PartialMarking places) (full : Marking places) : Prop :=
  ∀ place, match specified place with
    | none => True
    | some value => full place = value

private def CoordinateFits (before after : Option Nat) (source endpoint : Nat) : Prop :=
  (match before with | none => True | some value => source = value) ∧
  (match after with | none => True | some value => endpoint = value)

private inductive CoordinateResult (required endpoint : Nat) (before after : Option Nat) where
  | positive (extra : Nat) (fits : CoordinateFits before after (required + extra) (endpoint + extra))
  | negative (refuted : ¬ ∃ extra, CoordinateFits before after (required + extra) (endpoint + extra))

/-- Only decidable natural arithmetic is tested. An unconstrained coordinate
selects zero surplus, without claiming that other surpluses are impossible. -/
private def classifyCoordinate (required endpoint : Nat) :
    (before after : Option Nat) → CoordinateResult required endpoint before after
  | none, none => .positive 0 ⟨trivial, trivial⟩
  | some before, none =>
      if enough : required ≤ before then
        .positive (before - required) ⟨by dsimp [CoordinateFits]; omega, trivial⟩
      else .negative (by
        rintro ⟨extra, fits⟩
        have same := fits.1
        change required + extra = before at same
        omega)
  | none, some after =>
      if enough : endpoint ≤ after then
        .positive (after - endpoint) ⟨trivial, by dsimp [CoordinateFits]; omega⟩
      else .negative (by
        rintro ⟨extra, fits⟩
        have same := fits.2
        change endpoint + extra = after at same
        omega)
  | some before, some after =>
      if compatible : required ≤ before ∧ endpoint ≤ after ∧ before - required = after - endpoint then
        .positive (before - required) (by
          rcases compatible with ⟨sourceEnough, targetEnough, sameSurplus⟩
          constructor <;> dsimp [CoordinateFits] <;> omega)
      else .negative (by
        rintro ⟨extra, fits⟩
        have source := fits.1
        have target := fits.2
        change required + extra = before at source
        change endpoint + extra = after at target
        apply compatible
        exact ⟨by omega, by omega, by omega⟩)

/-- Numeric coordinate data are retained, rather than calling the pair
function again when the eventual witness's endpoints are read. -/
private structure PairCompletion (pairs : Fin places → Nat × Nat)
    (source target : PartialMarking places) where
  extra : Marking places
  before : Marking places
  after : Marking places
  source_exact : before = fun place => (pairs place).1 + extra place
  target_exact : after = fun place => (pairs place).2 + extra place
  source_matches : source.Matches before
  target_matches : target.Matches after

private inductive PairResult (pairs : Fin places → Nat × Nat) (source target : PartialMarking places) where
  | positive (witness : PairCompletion pairs source target)
  | negative (refuted : PairCompletion pairs source target → False)

/-- Finite recursion assembles the actual coordinate data. A failed head
excludes every surplus there; a failed tail excludes every full completion.
No witness is extracted from a propositional existence statement. -/
private def classifyPairs : {places : Nat} → (pairs : Fin places → Nat × Nat) →
    (source target : PartialMarking places) → PairResult pairs source target
  | 0, _, _, _ => .positive {
      extra := Fin.elim0
      before := Fin.elim0
      after := Fin.elim0
      source_exact := by funext place; exact Fin.elim0 place
      target_exact := by funext place; exact Fin.elim0 place
      source_matches := fun place => Fin.elim0 place
      target_matches := fun place => Fin.elim0 place }
  | n + 1, pairs, source, target =>
      let pair := pairs 0
      match classifyCoordinate pair.1 pair.2 (source 0) (target 0) with
      | .negative refuted => .negative (by
          intro witness
          apply refuted
          refine ⟨witness.extra 0, ?_, ?_⟩
          · have matched := witness.source_matches 0
            rw [witness.source_exact] at matched
            exact matched
          · have matched := witness.target_matches 0
            rw [witness.target_exact] at matched
            exact matched)
      | .positive extra fits =>
          match classifyPairs (fun place : Fin n => pairs place.succ)
              (fun place => source place.succ) (fun place => target place.succ) with
          | .negative refuted => .negative (fun witness => refuted {
              extra := fun place => witness.extra place.succ
              before := fun place => witness.before place.succ
              after := fun place => witness.after place.succ
              source_exact := by funext place; exact congrFun witness.source_exact place.succ
              target_exact := by funext place; exact congrFun witness.target_exact place.succ
              source_matches := fun place => witness.source_matches place.succ
              target_matches := fun place => witness.target_matches place.succ })
          | .positive tail => .positive {
              extra := Fin.cases extra tail.extra
              before := Fin.cases (pair.1 + extra) tail.before
              after := Fin.cases (pair.2 + extra) tail.after
              source_exact := by
                funext place
                exact Fin.cases rfl (fun other => congrFun tail.source_exact other) place
              target_exact := by
                funext place
                exact Fin.cases rfl (fun other => congrFun tail.target_exact other) place
              source_matches := fun place => Fin.cases fits.1 tail.source_matches place
              target_matches := fun place => Fin.cases fits.2 tail.target_matches place }

/-- Both completed endpoints and their enabled execution use the literal
supplied word. This is stronger than a token-balance equation. -/
structure WordCompletionWitness (net : Thesis.Causality.PetriNet places transitions)
    (word : List (Fin transitions)) (source target : PartialMarking places) where
  before : Marking places
  after : Marking places
  source_matches : source.Matches before
  target_matches : target.Matches after
  execution : net.Execution before word after

def WordCompletable (net : Thesis.Causality.PetriNet places transitions)
    (word : List (Fin transitions)) (source target : PartialMarking places) : Prop :=
  ∃ before after, source.Matches before ∧ target.Matches after ∧ net.Execution before word after

theorem WordCompletionWitness.completable {word : List (Fin transitions)} {source target : PartialMarking places}
    (witness : WordCompletionWitness net word source target) : net.WordCompletable word source target :=
  ⟨witness.before, witness.after, witness.source_matches, witness.target_matches, witness.execution⟩

theorem WordCompletionWitness.run_exact {word : List (Fin transitions)} {source target : PartialMarking places}
    (witness : WordCompletionWitness net word source target) :
    net.run witness.before word = some witness.after :=
  (run_eq_some_iff net _ _ _).mpr witness.execution

inductive WordCompletionResult (net : Thesis.Causality.PetriNet places transitions)
    (word : List (Fin transitions)) (source target : PartialMarking places) where
  | positive (witness : WordCompletionWitness net word source target)
  | negative (refuted : ¬ net.WordCompletable word source target)

def WordCompletionResult.isPositive {word : List (Fin transitions)} {source target : PartialMarking places} :
    WordCompletionResult net word source target → Bool
  | .positive _ => true
  | .negative _ => false

theorem WordCompletionResult.positive_exact {word : List (Fin transitions)} {source target : PartialMarking places}
    (result : WordCompletionResult net word source target) :
    result.isPositive = true ↔ net.WordCompletable word source target := by
  cases result with
  | positive witness => exact ⟨fun _ => witness.completable, fun _ => rfl⟩
  | negative refuted =>
      constructor
      · intro impossible; cases impossible
      · intro completion; exact False.elim (refuted completion)

theorem WordCompletionResult.negative_exact {word : List (Fin transitions)} {source target : PartialMarking places}
    (result : WordCompletionResult net word source target) :
    result.isPositive = false ↔ ¬ net.WordCompletable word source target := by
  cases result with
  | positive witness =>
      constructor
      · intro impossible; cases impossible
      · intro refuted; exact False.elim (refuted witness.completable)
  | negative refuted => exact ⟨fun _ => refuted, fun _ => rfl⟩

/-- Compute one compatible pair, or refute every pair. The old execution
theorem certifies the stored numbers only in proof fields; the numeric path
uses one paired word evaluation per visited coordinate. -/
def classifyWordCompletion (net : Thesis.Causality.PetriNet places transitions)
    (word : List (Fin transitions)) (source target : PartialMarking places) :
    WordCompletionResult net word source target :=
  match classifyPairs (fun place => net.wordRequirementsAt word place) source target with
  | .positive witness => .positive {
      before := witness.before
      after := witness.after
      source_matches := witness.source_matches
      target_matches := witness.target_matches
      execution := ((net.wordRequirements word).execution_iff _ _).mpr
        ⟨witness.extra, witness.source_exact, witness.target_exact⟩ }
  | .negative refuted => .negative (by
      rintro ⟨before, after, sourceMatches, targetMatches, execution⟩
      obtain ⟨extra, sourceExact, targetExact⟩ := ((net.wordRequirements word).execution_iff _ _).mp execution
      exact refuted {
        extra := extra
        before := before
        after := after
        source_exact := sourceExact
        target_exact := targetExact
        source_matches := sourceMatches
        target_matches := targetMatches })

theorem classifyWordCompletion_exact (net : Thesis.Causality.PetriNet places transitions)
    (word : List (Fin transitions)) (source target : PartialMarking places) :
    (net.classifyWordCompletion word source target).isPositive = true ↔ net.WordCompletable word source target :=
  (net.classifyWordCompletion word source target).positive_exact

theorem classifyWordCompletion_negative_iff (net : Thesis.Causality.PetriNet places transitions)
    (word : List (Fin transitions)) (source target : PartialMarking places) :
    (net.classifyWordCompletion word source target).isPositive = false ↔ ¬ net.WordCompletable word source target :=
  (net.classifyWordCompletion word source target).negative_exact

end Thesis.Causality.PetriNet
