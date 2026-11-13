import Thesis.Causality.CoordinateBoxScan
import Thesis.Causality.PetriCoverabilityScan
import Thesis.Examples.PetriCoverability

namespace Thesis.Causality.Examples.PetriCoverabilityScan

open PetriNet CoordinateBoxes
open Thesis.Causality.Examples.PetriCoverability

/-!
# Finite scan data and failure regressions

The exchange fixture checks returned data, not only success flags. A
coverage hit skips the first entry and lifts the selected real execution
to a larger source. Fresh-predecessor scans skip covered transitions and
whole entries while retaining the entire current basis for each coverage
test. In particular, an earlier entry can cover a later predecessor even
after traversal has passed it.

Box scans retain the literal prefix and suffix of one occurrence. The
premature-discard fixture finds the central box and correctly fails on
the two remaining arms. A zero cap is empty; overlapping and duplicate
unbounded boxes still have distinct list occurrences. Empty bases, empty
box lists, zero places and zero transitions use the same exact interfaces.

Only finite supplied lists are scanned. Failure to find current basis
coverage is not itself non-coverability, and an empty saturated basis
still needs the semantic certificate's separate target-coverage premise.
There is no recursive saturation or general coverability solver here.
-/

def coverageEntries := [initialWitness, secondWitness, queryWitness]

def coverageSnapshot (before : Marking 2) :=
  (scanCoverage coverageEntries before).map fun hit =>
    let witness := hit.witness
    (witness.word, (witness.source 0, witness.source 1),
      (witness.endpoint 0, witness.endpoint 1), exchange.check before witness.word witness.endpoint)

/-- The first source needs two tokens in its first coordinate and is
skipped. The second entry supplies word [2], lifted by the extra y-token. -/
theorem coverage_returns_lifted_execution :
    coverageSnapshot (pair 1 4) = some ([2], (1, 4), (2, 2), true) := by
  decide +kernel

theorem coverage_zero_missing : scanCoverage coverageEntries (pair 0 0) = none := rfl

theorem coverage_zero_outside_basis :
    ¬ Covered (coverageEntries.map (fun entry => entry.source)) (pair 0 0) :=
  (scanCoverage_none_iff _ _).mp coverage_zero_missing

theorem coverage_empty_missing (before : Marking 2) :
    scanCoverage ([] : List (CoverabilityWitness exchange target)) before = none := rfl

def freshSnapshot (entries : List (CoverabilityWitness exchange target)) :
    Option ((Fin 3 × List (Fin 3)) × ((Nat × Nat) × (Nat × Nat)) × (Bool × Bool)) :=
  (scanFreshPredecessor entries).map fun hit =>
    let witness := hit.witness
    ((hit.transition, witness.word), ((witness.source 0, witness.source 1),
      (witness.endpoint 0, witness.endpoint 1)),
      ((scanCoverage entries witness.source).isSome,
      exchange.check witness.source witness.word witness.endpoint))

theorem fresh_returns_uncovered_execution :
    freshSnapshot coverageEntries = some ((0, [0]), ((3, 0), (2, 2)), (false, true)) := by
  decide +kernel

/-- The already-listed source (3,0) covers transition 0's predecessor.
The scan therefore returns transition 1, with its actual one-step word. -/
theorem fresh_skips_covered_transition :
    freshSnapshot [initialWitness, initialWitness.prepend 0] =
      some ((1, [1]), ((0, 3), (2, 1)), (false, true)) := by
  decide +kernel

def laterEntries := [initialWitness, secondWitness, initialWitness.prepend 0,
  initialWitness.prepend 1, queryWitness]

/-- All predecessors of the first three entries are covered. While
checking the second entry, its transition-0 predecessor is covered only
by the first entry: dropping the already-scanned basis prefix would return
the wrong candidate. The genuine hit is the fourth entry's [0,1] word. -/
theorem fresh_retains_the_whole_basis :
    freshSnapshot laterEntries = some ((0, [0, 1]), ((1, 1), (2, 1)), (false, true)) := by
  decide +kernel

theorem saturated_seed_missing : scanFreshPredecessor seedCertificate.entries = none := rfl

theorem saturated_seed_certified :
    Saturated needsSeed (seedCertificate.entries.map (fun entry => entry.source)) :=
  (scanFreshPredecessor_none_iff _).mp saturated_seed_missing

theorem empty_predecessors_missing :
    scanFreshPredecessor ([] : List (CoverabilityWitness exchange target)) = none := rfl

def boxSnapshot (boxes : List (Box 2)) (point : Marking 2) :=
  (locateBox boxes point).map fun location =>
    (location.before.length, location.after.length, contains location.box point)

theorem central_box_location :
    boxSnapshot [leftArm, central, rightArm] query = some (1, 1, true) := by
  decide +kernel

theorem discarded_region_missing : locateBox [leftArm, rightArm] query = none :=
  (locateBox_none_iff _ _).mpr query_outside_remaining

theorem discarded_region_missing_computed :
    (locateBox [leftArm, rightArm] query).isSome = false := by decide +kernel

/-- The location really supplies the context needed by the existing
termination relation. No comparison of whole box functions is required. -/
theorem located_replacement_decreases {boxes : List (Box 2)} {point : Marking 2}
    (location : BoxLocation boxes point) :
    WorkStep 2 (location.before ++ split location.box point ++ location.after) boxes :=
  Eq.mpr (congrArg
    (fun old => WorkStep 2 (location.before ++ split location.box point ++ location.after) old)
    location.reconstruct)
    (split_in_context location.before location.after location.box point location.inside)

def zeroBound : Box 2 := fun _ => some 0

theorem zero_bound_and_duplicate_boxes :
    boxSnapshot [zeroBound, unrestricted, unrestricted] (pair 0 0) = some (1, 1, true) := by
  decide +kernel

theorem finite_bound_is_strict : contains central (pair 2 0) = false := by decide +kernel

theorem empty_boxes_missing (point : Marking 2) : locateBox [] point = none := rfl

def emptyBox : Box 0 := Fin.elim0

theorem empty_places_coverage (before : Marking 0) :
    (scanCoverage emptyCertificate.entries before).isSome = true := rfl

theorem empty_transitions_saturated : scanFreshPredecessor emptyCertificate.entries = none := rfl

theorem empty_places_box_location (point : Marking 0) :
    ((locateBox [emptyBox] point).map fun location =>
      (location.before.length, location.after.length)) = some (0, 0) := rfl

/-- Retain the review's combined case as a scan integration check:
an overshooting prefix precedes a nonempty suffix, then basis coverage
lifts that whole real word once more to the requested source. -/
def overshootSnapshot :=
  (scanCoverage [(initialWitness.prepend 0).prepend 0] (pair 4 1)).map fun hit =>
    let witness := hit.witness
    (witness.word, (witness.endpoint 0, witness.endpoint 1),
      exchange.check (pair 4 1) witness.word witness.endpoint)

theorem overshoot_before_nonempty_suffix : overshootSnapshot = some ([0, 0], (2, 5), true) := by
  decide +kernel

end Thesis.Causality.Examples.PetriCoverabilityScan
