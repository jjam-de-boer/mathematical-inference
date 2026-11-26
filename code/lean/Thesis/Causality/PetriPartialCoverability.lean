import Thesis.Causality.PetriCoverabilitySearch
import Thesis.Causality.PetriWordCompletion

namespace Thesis.Causality.PetriNet

open CoordinateBoxes

/-!
# Coverability from a partially specified source

A specified source coordinate has an exact value. An unspecified coordinate
may supply any finite number of tokens. The target gives lower bounds on the
actual endpoint, and the word is found by the solver.

Saturation already lists sufficient starting markings with executable words.
An entry can serve a partial source exactly when its requirements fit every
fixed coordinate. On free coordinates use the entry's own requirements; on
fixed coordinates keep the supplied values. The existing lifting theorem
then runs the stored word from that completed source. A failed scan excludes
all completions because any covering source dominates a listed entry.
-/

variable {places transitions : Nat}
variable {net : Thesis.Causality.PetriNet places transitions} {target : Marking places}

/-- Keep every prescribed value, using the supplied requirements only on
unspecified coordinates. This fills a fixed zero with zero. -/
def PartialMarking.completeFrom (specified : PartialMarking places)
    (required : Marking places) : Marking places :=
  fun place => match specified place with
    | none => required place
    | some value => value

theorem PartialMarking.completeFrom_matches (specified : PartialMarking places)
    (required : Marking places) : specified.Matches (specified.completeFrom required) := by
  intro place
  cases fixed : specified place <;> simp only [completeFrom, fixed]

/-- If any matching source provides the required tokens, so does the
displayed completion. Its free coordinates use exactly the required values. -/
theorem PartialMarking.below_completeFrom_of_matches {specified : PartialMarking places}
    {before required : Marking places} (matchesSource : specified.Matches before)
    (enough : Below required before) : Below required (specified.completeFrom required) := by
  intro place
  cases fixed : specified place with
  | none =>
      simpa only [completeFrom, fixed] using Nat.le_refl (required place)
  | some value =>
      have preserved : before place = value := by
        have atPlace := matchesSource place
        rw [fixed] at atPlace
        exact atPlace
      simpa only [completeFrom, fixed, preserved] using enough place

/-- Existence of a matching starting marking and a finite covering word. -/
def PartialCoverable (net : Thesis.Causality.PetriNet places transitions)
    (specified : PartialMarking places) (target : Marking places) : Prop :=
  ∃ before, specified.Matches before ∧ net.Coverable before target

/-- The stored witness gives the completed source, the literal word, and
the actual endpoint. The source proof retains all prescribed coordinates. -/
structure PartialCoverabilityWitness (net : Thesis.Causality.PetriNet places transitions)
    (specified : PartialMarking places) (target : Marking places) where
  witness : CoverabilityWitness net target
  source_matches : specified.Matches witness.source

theorem PartialCoverabilityWitness.coverable {specified : PartialMarking places}
    (result : PartialCoverabilityWitness net specified target) :
    net.PartialCoverable specified target :=
  ⟨result.witness.source, result.source_matches, result.witness.coverable⟩

/-- Test just the displayed completion of each entry. The first hit is
lifted once, so a failed candidate never constructs a new execution. -/
def scanPartialCoverage (entries : List (CoverabilityWitness net target))
    (specified : PartialMarking places) : Option (PartialCoverabilityWitness net specified target) :=
  let fits := fun entry : CoverabilityWitness net target =>
    markingBelow entry.source (specified.completeFrom entry.source)
  match found : entries.find? fits with
  | some entry =>
      let before := specified.completeFrom entry.source
      let checked := List.find?_some found
      let enough := (markingBelow_exact entry.source before).mp checked
      some ⟨entry.lift before enough, specified.completeFrom_matches entry.source⟩
  | none => none

/-- Scanning the finite witness list excludes precisely the matching
sources in its upward closure. Saturation is only needed when applying
this result to all executions. -/
theorem scanPartialCoverage_none_iff (entries : List (CoverabilityWitness net target))
    (specified : PartialMarking places) :
    scanPartialCoverage entries specified = none ↔
      ¬ ∃ before, specified.Matches before ∧ Covered (entries.map (fun entry => entry.source)) before := by
  unfold scanPartialCoverage
  dsimp only
  split
  · next entry found =>
      constructor
      · intro impossible
        cases impossible
      · intro missing
        let before := specified.completeFrom entry.source
        have checked := List.find?_some found
        have enough := (markingBelow_exact entry.source before).mp checked
        exact False.elim (missing ⟨before, specified.completeFrom_matches entry.source,
          entry.source, List.mem_map_of_mem (List.mem_of_find?_eq_some found), enough⟩)
  · next missing =>
      constructor
      · rintro _ ⟨before, sourceFits, point, listed, enough⟩
        obtain ⟨entry, entryListed, rfl⟩ := List.mem_map.mp listed
        have completed := PartialMarking.below_completeFrom_of_matches sourceFits enough
        exact (List.find?_eq_none.mp missing) entry entryListed ((markingBelow_exact _ _).mpr completed)
      · intro _
        rfl

inductive PartialCoverabilityResult (net : Thesis.Causality.PetriNet places transitions)
    (specified : PartialMarking places) (target : Marking places) where
  | positive (witness : PartialCoverabilityWitness net specified target)
  | negative (refuted : ¬ net.PartialCoverable specified target)

def PartialCoverabilityResult.isPositive {specified : PartialMarking places} :
    PartialCoverabilityResult net specified target → Bool
  | .positive _ => true
  | .negative _ => false

/-- Saturate once for the target, then search the witnessed basis. A miss
excludes every finite token supply and every finite word. -/
def classifyPartialCoverability (net : Thesis.Causality.PetriNet places transitions)
    (specified : PartialMarking places) (target : Marking places) :
    PartialCoverabilityResult net specified target :=
  let certificate := net.saturate target
  match checked : scanPartialCoverage certificate.entries specified with
  | some witness => .positive witness
  | none => .negative (by
      rintro ⟨before, sourceFits, coverable⟩
      apply (scanPartialCoverage_none_iff _ _).mp checked
      exact ⟨before, sourceFits, (certificate.coverable_iff_covered before).mp coverable⟩)

theorem classifyPartialCoverability_exact (net : Thesis.Causality.PetriNet places transitions)
    (specified : PartialMarking places) (target : Marking places) :
    (net.classifyPartialCoverability specified target).isPositive = true ↔
      net.PartialCoverable specified target := by
  cases net.classifyPartialCoverability specified target with
  | positive witness => exact ⟨fun _ => witness.coverable, fun _ => rfl⟩
  | negative refuted =>
      exact ⟨fun impossible => Bool.noConfusion impossible, fun possible => False.elim (refuted possible)⟩

theorem classifyPartialCoverability_negative_iff (net : Thesis.Causality.PetriNet places transitions)
    (specified : PartialMarking places) (target : Marking places) :
    (net.classifyPartialCoverability specified target).isPositive = false ↔
      ¬ net.PartialCoverable specified target := by
  cases net.classifyPartialCoverability specified target with
  | positive witness =>
      exact ⟨fun impossible => Bool.noConfusion impossible,
        fun refuted => False.elim (refuted witness.coverable)⟩
  | negative refuted => exact ⟨fun _ => refuted, fun _ => rfl⟩

end Thesis.Causality.PetriNet
