import Thesis.Causality.ReachabilityCorrectness
import Thesis.Probability.FiniteVectorWitness

namespace Thesis.Causality.FiniteLabelledReachability

open Probability

/-!
# Finite reachability with computed transition-word witnesses

The existing finite-graph theorem bounds a reachable path by the carrier's
enumeration length. This module retains actual labels in a materialized
dynamic table, so success returns a computed word rather than selecting an
inhabitant of a propositional existence theorem. Each table layer stores
one optional word per finite state, with the target fixed during the search.

The transition function may reject a label. Equality comes from the supplied
two-sided finite presentation, and the label list is supplied explicitly.
An empty word is accepted only at the target. The result is exact finite
reachability for the listed labels; no unbounded-state problem becomes
finite by an assumed cutoff.
-/

variable {α : Type} {β : Type}

def same (states : FiniteWitness α) (left right : α) : Bool :=
  decide (states.encode left = states.encode right)

theorem same_exact (states : FiniteWitness α) (left right : α) :
    same states left right = true ↔ left = right := by
  rw [same, decide_eq_true_eq]
  constructor
  · intro equal
    exact (states.decode_encode left).symm.trans ((congrArg states.decode equal).trans (states.decode_encode right))
  · intro equal
    exact congrArg states.encode equal

def edge (states : FiniteWitness α) (labels : List β) (advance : α → β → Option α)
    (source target : α) : Bool :=
  labels.any (fun label => (advance source label).any (fun next => same states next target))

theorem edge_exact (states : FiniteWitness α) (labels : List β) (advance : α → β → Option α)
    (source target : α) : edge states labels advance source target = true ↔
      ∃ label ∈ labels, advance source label = some target := by
  simp only [edge, List.any_eq_true]
  constructor
  · rintro ⟨label, listed, accepted⟩
    cases computed : advance source label with
    | none => simp only [computed, Option.any_none, Bool.false_eq_true] at accepted
    | some next =>
        have equal := (same_exact states next target).mp (by simpa only [computed, Option.any_some] using accepted)
        exact ⟨label, listed, computed.trans (congrArg some equal)⟩
  · rintro ⟨label, listed, computed⟩
    exact ⟨label, listed, by simp only [computed, Option.any_some, (same_exact states target target).mpr rfl]⟩

def run (advance : α → β → Option α) : α → List β → Option α
  | source, [] => some source
  | source, label :: rest => (advance source label).bind (fun next => run advance next rest)

/-- Literal word concatenation composes partial executions. A rejected
prefix stays rejected; no intermediate state is selected by an oracle. -/
theorem run_append (advance : α → β → Option α) (source : α) (first second : List β) :
    run advance source (first ++ second) =
      (run advance source first).bind (fun middle => run advance middle second) := by
  induction first generalizing source with
  | nil => rfl
  | cons label rest ih =>
      cases computed : advance source label with
      | none => simp only [List.cons_append, run, computed, Option.bind_none]
      | some next =>
          simpa only [List.cons_append, run, computed, Option.bind_some] using ih next

/-- A supplied computed word yields an old finite-graph path. The list
coverage premise concerns labels, not a choice of a path or intermediate. -/
theorem reachable_of_run (states : FiniteWitness α) (labels : List β) (advance : α → β → Option α)
    (complete : ∀ label, label ∈ labels) {source target : α} {word : List β}
    (accepted : run advance source word = some target) :
    FiniteReachability.Reachable (edge states labels advance) source target := by
  induction word generalizing source with
  | nil =>
      cases Option.some.inj accepted
      exact .refl _ _
  | cons label rest ih =>
      rcases Option.bind_eq_some_iff.mp accepted with ⟨next, first, tail⟩
      exact FiniteReachability.Reachable.prepend
        ((edge_exact states labels advance source next).mpr ⟨label, complete label, first⟩) (ih tail)

private theorem firstSome_present (values : List α) (read : α → Option β)
    (value : α) (listed : value ∈ values) (present : (read value).isSome = true) :
    (values.findSome? read).isSome = true := by
  cases result : values.findSome? read with
  | some found => rfl
  | none =>
      have absent := (List.findSome?_eq_none_iff.mp result) value listed
      simp only [absent, Option.isSome_none, Bool.false_eq_true] at present

/-- The stored vector evaluates every entry once per layer. Earlier
words are read by their explicit finite code, not recomputed by a closure. -/
def wordsTo (states : FiniteWitness α) (labels : List β) (advance : α → β → Option α)
    (target : α) : Nat → Vector (Option (List β)) states.card
  | 0 => vectorOfFn (fun index => if same states (states.decode index) target then some [] else none)
  | fuel + 1 =>
      let previous := wordsTo states labels advance target fuel
      vectorOfFn (fun index =>
        if same states (states.decode index) target then some []
        else labels.findSome? (fun label => (advance (states.decode index) label).bind
          (fun next => (previous[states.encode next]).map (fun rest => label :: rest))))

theorem wordsTo_sound (states : FiniteWitness α) (labels : List β) (advance : α → β → Option α)
    (target : α) (fuel : Nat) (source : α) (word : List β)
    (found : (wordsTo states labels advance target fuel)[states.encode source] = some word) :
    run advance source word = some target := by
  induction fuel generalizing source word with
  | zero =>
      simp only [wordsTo, Fin.getElem_fin, getElem_vectorOfFn, states.decode_encode] at found
      split at found
      · next equal =>
          cases Option.some.inj found
          exact congrArg some ((same_exact states source target).mp equal)
      · cases found
  | succ fuel ih =>
      simp only [wordsTo, Fin.getElem_fin, getElem_vectorOfFn, states.decode_encode] at found
      split at found
      · next equal =>
          cases Option.some.inj found
          exact congrArg some ((same_exact states source target).mp equal)
      · rcases List.exists_of_findSome?_eq_some found with ⟨label, _listed, candidate⟩
        rcases Option.bind_eq_some_iff.mp candidate with ⟨next, advanced, previous⟩
        rcases Option.map_eq_some_iff.mp previous with ⟨rest, earlier, equal⟩
        cases equal
        change (advance source label).bind (fun middle => run advance middle rest) = some target
        rw [advanced, Option.bind_some]
        exact ih next rest earlier

theorem wordsTo_complete (states : FiniteWitness α) (labels : List β) (advance : α → β → Option α)
    (fuel : Nat) : ∀ {length source target},
      FiniteReachability.ExactWalk (edge states labels advance) length source target → length ≤ fuel →
      ((wordsTo states labels advance target fuel)[states.encode source]).isSome = true := by
  induction fuel with
  | zero =>
      intro length source target walk bound
      have lengthZero : length = 0 := Nat.eq_zero_of_le_zero bound
      cases lengthZero
      have equal := walk.eq_of_length_zero
      simp only [wordsTo, Fin.getElem_fin, getElem_vectorOfFn, states.decode_encode,
        (same_exact states source target).mpr equal, if_true, Option.isSome_some]
  | succ fuel ih =>
      intro length source target walk bound
      simp only [wordsTo, Fin.getElem_fin, getElem_vectorOfFn, states.decode_encode]
      split
      · rfl
      · next different =>
          cases walk with
          | refl => exact False.elim (different ((same_exact states _ _).mpr rfl))
          | step first rest =>
              rcases (edge_exact states labels advance _ _).mp first with ⟨label, listed, advanced⟩
              have earlier := ih rest (Nat.le_of_succ_le_succ bound)
              apply firstSome_present _ _ label listed
              simp only [advanced, Option.bind_some]
              cases computed : (wordsTo states labels advance target fuel)[states.encode _] with
              | none => simp only [computed, Option.isSome_none, Bool.false_eq_true] at earlier
              | some word => rfl

inductive Result (advance : α → β → Option α) (states : FiniteWitness α) (labels : List β)
    (source target : α) where
  | found (word : List β) (accepted : run advance source word = some target)
  | unreachable (missing : ¬ FiniteReachability.Reachable (edge states labels advance) source target)

/-- Total finite search. The fuel is proved sufficient by the existing
finite-carrier theorem; rejection is not a user-supplied depth cutoff. -/
def solve (states : FiniteWitness α) (labels : List β) (advance : α → β → Option α)
    (source target : α) : Result advance states labels source target :=
  match computed : (wordsTo states labels advance target states.enumeration.length)[states.encode source] with
  | some word => .found word (wordsTo_sound states labels advance target _ source word computed)
  | none => .unreachable (by
      intro reachable
      rcases FiniteReachability.boundedWalk_of_reachable (same states) states.enumeration
        (edge states labels advance) (same_exact states) states.enumeration_complete reachable with
        ⟨length, bound, ⟨walk⟩⟩
      have present := wordsTo_complete states labels advance _ walk bound
      simp only [computed, Option.isSome_none, Bool.false_eq_true] at present)

end Thesis.Causality.FiniteLabelledReachability
