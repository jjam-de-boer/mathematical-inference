import Thesis.Causality.FiniteLabelledReachability

namespace Thesis.Causality.FiniteLabelledReachability

open Probability

/-!
# Repetition inside the original successful word

On a finite carrier with N enumerated states, the first N transitions of
a successful word visit N+1 states. Two of those visits coincide. This
module computes their indices and factors the original word into a literal
prefix, a nonempty loop, and a suffix. The loop ends within those first N
transitions; every supplied label and both execution endpoints are retained.

This stronger word-preservation property is needed when a later argument
must keep track of a nonzero digit after the loop. Endpoint-preserving walk
shortening alone does not retain that information.

All searches are over explicit finite index lists. Prefix states come from
the actual partial execution, with its successful full run ruling out a
failed prefix. No representative is selected from an abstract existence
theorem, and no equality or finiteness oracle is assumed. The labels need
neither a finite presentation nor decidable equality.

This module does not assert that the suffix contains a positive digit or
classify unbounded coordinates. N is the carrier's enumeration length,
not an assumed cutoff on an unbounded-state system.
-/

variable {α β : Type}

private structure RepeatedIndices (values : Fin size → α) where
  earlier : Fin size
  later : Fin size
  increasing : earlier.val < later.val
  equal : values earlier = values later

private def findRepeatedIndices (states : FiniteWitness α) (values : Fin size → α) :
    Option (RepeatedIndices values) :=
  (List.finRange size).findSome? (fun earlier =>
    (List.finRange size).findSome? (fun later =>
      if increasing : earlier.val < later.val then
        if equal : same states (values earlier) (values later) = true then
          some ⟨earlier, later, increasing, (same_exact states _ _).mp equal⟩
        else none
      else none))

private theorem finRange_nodup (size : Nat) : (List.finRange size).Nodup := by
  induction size with
  | zero => exact List.Pairwise.nil
  | succ size ih =>
      rw [List.finRange_succ]
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro listed
        rcases List.mem_map.mp listed with ⟨index, _, equal⟩
        exact (Fin.succ_ne_zero index) equal
      · exact List.Pairwise.map Fin.succ
          (fun left right different equal => different (Fin.ext (Nat.succ.inj (congrArg Fin.val equal)))) ih

/-- The failed finite search would make N+1 visits injective in an
enumeration of length N, contradicting the constructive list bound. -/
private def repeatedIndices (states : FiniteWitness α)
    (values : Fin (states.enumeration.length + 1) → α) : RepeatedIndices values :=
  match computed : findRepeatedIndices states values with
  | some indices => indices
  | none => False.elim (by
      have separated : ∀ earlier later, earlier.val < later.val → values earlier ≠ values later := by
        intro earlier later increasing equal
        have outer := (List.findSome?_eq_none_iff.mp computed) earlier (List.mem_finRange earlier)
        have inner := (List.findSome?_eq_none_iff.mp outer) later (List.mem_finRange later)
        rw [dif_pos increasing, dif_pos ((same_exact states _ _).mpr equal)] at inner
        cases inner
      have injective : ∀ earlier later, values earlier = values later → earlier = later := by
        intro earlier later equal
        apply Fin.ext
        by_cases forward : earlier.val < later.val
        · exact False.elim (separated earlier later forward equal)
        · by_cases backward : later.val < earlier.val
          · exact False.elim (separated later earlier backward equal.symm)
          · omega
      have distinct : ((List.finRange (states.enumeration.length + 1)).map values).Nodup :=
        List.Pairwise.map values (fun left right different equal => different (injective left right equal))
          (finRange_nodup _)
      have bound := Causality.nodup_length_le_of_subset (same states) (same_exact states)
        _ states.enumeration distinct (fun node _ => states.enumeration_complete node)
      rw [List.length_map, List.length_finRange] at bound
      omega)

/-- A successful whole word computes every prefix endpoint, including
an overlong take. Failure is eliminated using literal take/drop composition. -/
private def prefixEndpoint (advance : α → β → Option α) (source target : α) (word : List β)
    (accepted : run advance source word = some target) (count : Nat) :
    {middle : α // run advance source (word.take count) = some middle} :=
  match computed : run advance source (word.take count) with
  | some middle => ⟨middle, rfl⟩
  | none => False.elim (by
      have composed := run_append advance source (word.take count) (word.drop count)
      rw [List.take_append_drop, accepted, computed, Option.bind_none] at composed
      cases composed)

/-- Structural take/drop composition. The pinned standard `List.take_add`
proof reaches a classical minimum lemma, so prove this equality directly
by the consumed prefix length under the project's transitive axiom policy. -/
private theorem take_add_constructive (word : List β) (left right : Nat) :
    word.take (left + right) = word.take left ++ (word.drop left).take right := by
  induction left generalizing word with
  | zero => simp only [Nat.zero_add, List.take_zero, List.drop_zero, List.nil_append]
  | succ left ih =>
      cases word with
      | nil => simp only [List.take_nil, List.drop_nil, List.append_nil]
      | cons label rest =>
          simp only [Nat.succ_add, List.take_succ_cons, List.drop_succ_cons, List.cons_append]
          exact congrArg (List.cons label) (ih rest)

/-- Actual factors and checked runs, with a strict nonempty loop. The
literal join and positional bound preserve information lost by shortening. -/
structure WordRepetition (advance : α → β → Option α) (source target : α) (word : List β) (bound : Nat) where
  initial : List β
  cycle : List β
  suffix : List β
  middle : α
  word_eq : word = initial ++ (cycle ++ suffix)
  initial_run : run advance source initial = some middle
  cycle_run : run advance middle cycle = some middle
  suffix_run : run advance middle suffix = some target
  nonempty : cycle ≠ []
  within : initial.length + cycle.length ≤ bound

/-- Compute repetition before the carrier bound in the supplied successful
word. The input length premise ensures enough visits; it is not a search
bound assumed sufficient for arbitrary reachability. -/
def factorRepetition (states : FiniteWitness α) (advance : α → β → Option α)
    (source target : α) (word : List β) (accepted : run advance source word = some target)
    (long : states.enumeration.length ≤ word.length) :
    WordRepetition advance source target word states.enumeration.length := by
  let endpoints := fun index : Fin (states.enumeration.length + 1) =>
    (prefixEndpoint advance source target word accepted index.val).val
  let indices := repeatedIndices states endpoints
  let first := prefixEndpoint advance source target word accepted indices.earlier.val
  let second := prefixEndpoint advance source target word accepted indices.later.val
  have equal : first.val = second.val := indices.equal
  have increasing := indices.increasing
  have laterBound : indices.later.val ≤ states.enumeration.length := by
    have bounded := indices.later.isLt
    omega
  have firstBound : indices.earlier.val ≤ word.length := by omega
  have laterWord : indices.later.val ≤ word.length := Nat.le_trans laterBound long
  have addition : indices.earlier.val + (indices.later.val - indices.earlier.val) = indices.later.val := by omega
  have firstTwo : word.take indices.earlier.val ++ (word.drop indices.earlier.val).take
      (indices.later.val - indices.earlier.val) = word.take indices.later.val := by
    rw [← take_add_constructive, addition]
  have cycleRun := run_append advance source (word.take indices.earlier.val)
    ((word.drop indices.earlier.val).take (indices.later.val - indices.earlier.val))
  rw [firstTwo, second.property, first.property, Option.bind_some] at cycleRun
  have suffixRun := run_append advance source (word.take indices.later.val) (word.drop indices.later.val)
  rw [List.take_append_drop, accepted, second.property, Option.bind_some] at suffixRun
  have cycleLength : ((word.drop indices.earlier.val).take
      (indices.later.val - indices.earlier.val)).length = indices.later.val - indices.earlier.val := by
    rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
  refine {
    initial := word.take indices.earlier.val
    cycle := (word.drop indices.earlier.val).take (indices.later.val - indices.earlier.val)
    suffix := word.drop indices.later.val
    middle := first.val
    word_eq := ?_
    initial_run := first.property
    cycle_run := cycleRun.symm.trans (congrArg some equal.symm)
    suffix_run := ?_
    nonempty := ?_
    within := ?_ }
  · rw [← List.append_assoc, firstTwo, List.take_append_drop]
  · rw [equal]
    exact suffixRun.symm
  · intro empty
    have lengthZero := congrArg List.length empty
    rw [cycleLength, List.length_nil] at lengthZero
    omega
  · rw [List.length_take_of_le firstBound, cycleLength]
    omega

end Thesis.Causality.FiniteLabelledReachability
