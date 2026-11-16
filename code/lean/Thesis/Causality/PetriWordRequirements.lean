import Thesis.Causality.PetriPredecessors

namespace Thesis.Causality.PetriNet

/-!
# Least counter requirements and the exact effect of a supplied word

Every supplied finite transition word has a least enabled source marking
and an actual endpoint at that source. A prefix edge must first meet its
consumption guard, then supply the remaining word's requirements. Production
can supply those later requirements but cannot erase the prefix guard.

The resulting pair describes the whole execution relation along that word:
every other execution adds the same nonnegative counter surplus to both
endpoints. The surplus is computed from the supplied source, rather than
chosen from an existential statement. In particular, the source and final
marking cannot be completed independently when some coordinates are unknown.

The public numeric evaluator carries source and endpoint together in one
forward fold per requested coordinate. It builds no chain of suffix-marking
functions. Reading the two legacy fields separately may perform two folds;
callers needing both values can use the paired evaluator directly. This is
not a cache of all coordinates, or a bound on natural-number arithmetic cost.

All counters and words here are finite, with no fixed magnitude or length
cutoff. The pair may drain counters as well as grow them; no pumping premise
is imposed. This is counter execution for one given word. Finite control
still checks its path separately, and no partial-endpoint classifier or
search for a suitable word is introduced.
-/

variable {places transitions : Nat}
variable {net : Thesis.Causality.PetriNet places transitions}

/-- Actual execution data and coordinatewise minimality. The endpoints
belong to the supplied word; no external reachability certificate is required. -/
structure WordRequirements (net : Thesis.Causality.PetriNet places transitions)
    (word : List (Fin transitions)) where
  source : Marking places
  endpoint : Marking places
  execution : net.Execution source word endpoint
  least : ∀ {before after}, net.Execution before word after → Below source before

/-- A proof specification by backward recursion. If the suffix needs `r`
and ends at `e`, a prefix consuming `c` and producing `p` needs `c + (r-p)`
and ends at `e + (p-r)`. The public evaluator below uses this construction
only in erased proof fields, not to compute its numeric endpoints. -/
private def wordRequirementsSpec (net : Thesis.Causality.PetriNet places transitions) :
    (word : List (Fin transitions)) → WordRequirements net word
  | [] => {
      source := fun _ => 0
      endpoint := fun _ => 0
      execution := .nil _
      least := fun _ _ => Nat.zero_le _ }
  | edge :: rest => by
      let tail := wordRequirementsSpec net rest
      let extra := fun place => net.produce edge place - tail.source place
      refine {
        source := net.predecessor edge tail.source
        endpoint := addMarking tail.endpoint extra
        execution := ?_
        least := ?_ }
      · have first : net.Fires (net.predecessor edge tail.source) edge (addMarking tail.source extra) := by
          constructor
          · intro place
            change net.consume edge place ≤
              net.consume edge place + (tail.source place - net.produce edge place)
            omega
          · funext place
            change tail.source place + (net.produce edge place - tail.source place) =
              (net.consume edge place + (tail.source place - net.produce edge place)) -
                net.consume edge place + net.produce edge place
            omega
        exact .cons first (tail.execution.add_marking extra)
      · intro before after execution
        cases execution with
        | cons first remaining => exact predecessor_le_of_fires first (tail.least remaining)

/-- Compose exact pairs in execution order. The left endpoint may need
extra credit to enable the right pair; the same credit shifts both ends. -/
private def composeRequirements (left right : Nat × Nat) : Nat × Nat :=
  (left.1 + (right.1 - left.2), right.2 + (left.2 - right.1))

private theorem composeRequirements_right_identity (value : Nat × Nat) :
    composeRequirements value (0, 0) = value := by
  rcases value with ⟨source, endpoint⟩
  apply Prod.ext <;> dsimp [composeRequirements] <;> omega

private theorem composeRequirements_left_identity (value : Nat × Nat) :
    composeRequirements (0, 0) value = value := by
  rcases value with ⟨source, endpoint⟩
  apply Prod.ext <;> dsimp [composeRequirements] <;> omega

/-- Associativity retains prefix enabling requirements, not merely the
signed overall effect. Only arithmetic on the six supplied naturals is used. -/
private theorem composeRequirements_assoc (first second third : Nat × Nat) :
    composeRequirements (composeRequirements first second) third =
      composeRequirements first (composeRequirements second third) := by
  rcases first with ⟨firstSource, firstEnd⟩
  rcases second with ⟨secondSource, secondEnd⟩
  rcases third with ⟨thirdSource, thirdEnd⟩
  apply Prod.ext <;> dsimp [composeRequirements] <;> omega

/-- Return both counter values in one left-to-right word traversal for
this coordinate. The accumulator is a numeric pair, not a marking closure
whose evaluation recursively replays suffix requirements. -/
def wordRequirementsAt (net : Thesis.Causality.PetriNet places transitions)
    (word : List (Fin transitions)) (place : Fin places) : Nat × Nat :=
  word.foldl (fun values edge => composeRequirements values (net.consume edge place, net.produce edge place)) (0, 0)

/-- The stronger accumulator statement relates the forward fold to the
backward specification without reversing or copying the supplied word. -/
private theorem wordRequirementsFold_eq_spec (net : Thesis.Causality.PetriNet places transitions)
    (word : List (Fin transitions)) (place : Fin places) (initial : Nat × Nat) :
    word.foldl (fun values edge => composeRequirements values (net.consume edge place, net.produce edge place)) initial =
      composeRequirements initial
        ((wordRequirementsSpec net word).source place, (wordRequirementsSpec net word).endpoint place) := by
  induction word generalizing initial with
  | nil =>
      change initial = composeRequirements initial (0, 0)
      exact (composeRequirements_right_identity initial).symm
  | cons edge rest ih =>
      rw [List.foldl_cons, ih, composeRequirements_assoc]
      rfl

private theorem wordRequirementsAt_eq_spec (net : Thesis.Causality.PetriNet places transitions)
    (word : List (Fin transitions)) (place : Fin places) :
    net.wordRequirementsAt word place =
      ((wordRequirementsSpec net word).source place, (wordRequirementsSpec net word).endpoint place) := by
  exact (wordRequirementsFold_eq_spec net word place (0, 0)).trans (composeRequirements_left_identity _)

/-- Keep the existing public record. Its numeric fields use the forward
paired fold; the private specification certifies them only inside proofs.
Consequently proof erasure removes the specification from this runtime path. -/
def wordRequirements (net : Thesis.Causality.PetriNet places transitions)
    (word : List (Fin transitions)) : WordRequirements net word where
  source := fun place => (net.wordRequirementsAt word place).1
  endpoint := fun place => (net.wordRequirementsAt word place).2
  execution := by
    have source : (fun place => (net.wordRequirementsAt word place).1) =
        (wordRequirementsSpec net word).source := by
      funext place
      exact congrArg Prod.fst (wordRequirementsAt_eq_spec net word place)
    have endpoint : (fun place => (net.wordRequirementsAt word place).2) =
        (wordRequirementsSpec net word).endpoint := by
      funext place
      exact congrArg Prod.snd (wordRequirementsAt_eq_spec net word place)
    rw [source, endpoint]
    exact (wordRequirementsSpec net word).execution
  least := by
    intro before after execution place
    change (net.wordRequirementsAt word place).1 ≤ before place
    rw [wordRequirementsAt_eq_spec]
    exact (wordRequirementsSpec net word).least execution place

/-- Paired clients can request both values once. Reading `.source` and
`.endpoint` independently remains valid but does not memoize this pair. -/
theorem wordRequirementsAt_exact (net : Thesis.Causality.PetriNet places transitions)
    (word : List (Fin transitions)) (place : Fin places) :
    net.wordRequirementsAt word place =
      ((net.wordRequirements word).source place, (net.wordRequirements word).endpoint place) := rfl

private theorem wordRequirements_source_eq_spec (net : Thesis.Causality.PetriNet places transitions)
    (word : List (Fin transitions)) :
    (net.wordRequirements word).source = (wordRequirementsSpec net word).source := by
  funext place
  exact congrArg Prod.fst (wordRequirementsAt_eq_spec net word place)

private theorem wordRequirements_endpoint_eq_spec (net : Thesis.Causality.PetriNet places transitions)
    (word : List (Fin transitions)) :
    (net.wordRequirements word).endpoint = (wordRequirementsSpec net word).endpoint := by
  funext place
  exact congrArg Prod.snd (wordRequirementsAt_eq_spec net word place)

theorem wordRequirements_nil_source (net : Thesis.Causality.PetriNet places transitions) :
    (net.wordRequirements []).source = fun _ => 0 := rfl

theorem wordRequirements_nil_endpoint (net : Thesis.Causality.PetriNet places transitions) :
    (net.wordRequirements []).endpoint = fun _ => 0 := rfl

theorem wordRequirements_cons_source (net : Thesis.Causality.PetriNet places transitions)
    (edge : Fin transitions) (rest : List (Fin transitions)) :
    (net.wordRequirements (edge :: rest)).source = net.predecessor edge (net.wordRequirements rest).source := by
  rw [wordRequirements_source_eq_spec, wordRequirements_source_eq_spec]
  rfl

theorem wordRequirements_cons_endpoint (net : Thesis.Causality.PetriNet places transitions)
    (edge : Fin transitions) (rest : List (Fin transitions)) :
    (net.wordRequirements (edge :: rest)).endpoint =
      addMarking (net.wordRequirements rest).endpoint
        (fun place => net.produce edge place - (net.wordRequirements rest).source place) := by
  rw [wordRequirements_endpoint_eq_spec, wordRequirements_endpoint_eq_spec, wordRequirements_source_eq_spec]
  rfl

namespace WordRequirements

variable {word : List (Fin transitions)}

def surplus (requirements : WordRequirements net word) (before : Marking places) : Marking places :=
  fun place => before place - requirements.source place

theorem source_eq_add_surplus (requirements : WordRequirements net word) (before : Marking places)
    (enough : Below requirements.source before) :
    before = addMarking requirements.source (requirements.surplus before) := by
  funext place
  have bound := enough place
  change before place = requirements.source place + (before place - requirements.source place)
  omega

/-- Execute from any sufficiently large supplied source. The returned
endpoint is literal arithmetic on the stored pair and the computed surplus. -/
def execute (requirements : WordRequirements net word) (before : Marking places)
    (enough : Below requirements.source before) :
    {after : Marking places // net.Execution before word after} :=
  ⟨addMarking requirements.endpoint (requirements.surplus before), by
    have execution := requirements.execution.add_marking (requirements.surplus before)
    rw [← requirements.source_eq_add_surplus before enough] at execution
    exact execution⟩

/-- Necessity is about actual executions, not just the overall balance
equation. Minimality and determinism force the same surplus at the end. -/
theorem endpoint_eq_add_surplus (requirements : WordRequirements net word) {before after : Marking places}
    (execution : net.Execution before word after) :
    after = addMarking requirements.endpoint (requirements.surplus before) := by
  let computed := requirements.execute before (requirements.least execution)
  exact Option.some.inj (((run_eq_some_iff net _ _ _).mpr execution).symm.trans
    ((run_eq_some_iff net _ _ _).mpr computed.property))

/-- This is the full exact relation for the given word. A common surplus
is essential; separate source and target padding would admit invalid runs. -/
theorem execution_iff (requirements : WordRequirements net word) (before after : Marking places) :
    net.Execution before word after ↔ ∃ extra : Marking places,
      before = addMarking requirements.source extra ∧ after = addMarking requirements.endpoint extra := by
  constructor
  · intro execution
    exact ⟨requirements.surplus before,
      requirements.source_eq_add_surplus before (requirements.least execution),
      requirements.endpoint_eq_add_surplus execution⟩
  · rintro ⟨extra, rfl, rfl⟩
    exact requirements.execution.add_marking extra

theorem executable_iff (requirements : WordRequirements net word) (before : Marking places) :
    (∃ after, net.Execution before word after) ↔ Below requirements.source before := by
  constructor
  · rintro ⟨after, execution⟩
    exact requirements.least execution
  · intro enough
    let computed := requirements.execute before enough
    exact ⟨computed.val, computed.property⟩

theorem run_exact (requirements : WordRequirements net word) (before after : Marking places) :
    net.run before word = some after ↔ ∃ extra : Marking places,
      before = addMarking requirements.source extra ∧ after = addMarking requirements.endpoint extra :=
  (run_eq_some_iff net before after word).trans (requirements.execution_iff before after)

end WordRequirements
end Thesis.Causality.PetriNet
