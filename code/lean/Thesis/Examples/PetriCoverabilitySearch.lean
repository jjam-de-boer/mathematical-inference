import Thesis.Causality.PetriCoverabilitySearch
import Thesis.Examples.PetriCoverability
import Thesis.Examples.PetriNet

namespace Thesis.Causality.Examples.PetriCoverabilitySearch

open Thesis.Causality.PetriNet Thesis.Causality.CoordinateBoxes
open Thesis.Causality.Examples.PetriCoverability

/-!
# Saturation and complete classifier regressions

The three-token seed problem needs two genuinely fresh insertions. The
finite scans identify both actual witnesses, the certified state updates
produce sources [1,2,3], and the final scan proves saturation. Two guarded
equation rewrites check the recursive construction; no large accessibility
proof is normalized to execute the entire well-founded function.

Public classifier results are checked against independently supplied words
or unbounded mathematical refutations. A positive overshoot example retains
the existing proof that exact reachability fails. Zero places, zero
transitions, and an already saturated initial state are also checked.

These are kernel proof checks. No native decision axiom, runtime solver
pilot, increased resource limit, or pumping/exact-reachability algorithm is
introduced by this example module.
-/

def threeStart := SaturationState.initial needsSeed (tokens 3)

def firstHit : FreshPredecessor threeStart.entries where
  entry := CoverabilityWitness.initial needsSeed (tokens 3)
  listed := List.mem_cons_self
  transition := 0
  uncovered := (scanCoverage_none_iff _ _).mp (by rfl)

def threeMiddle := (threeStart.advance firstHit).val

def secondHit : FreshPredecessor threeMiddle.entries where
  entry := firstHit.witness
  listed := List.mem_cons_self
  transition := 0
  uncovered := (scanCoverage_none_iff _ _).mp (by rfl)

def threeEnd := (threeMiddle.advance secondHit).val

theorem first_fresh_selected : scanFreshPredecessor threeStart.entries = some firstHit := rfl
theorem second_fresh_selected : scanFreshPredecessor threeMiddle.entries = some secondHit := rfl
theorem third_scan_stops : scanFreshPredecessor threeEnd.entries = none := rfl

/-- Both updates preserve the computed witness data and produce the
expected strict upper bound on the remaining one-dimensional box. -/
theorem two_update_data :
    (threeEnd.entries.map (fun entry => entry.source 0), threeEnd.boxes.map (fun box => box 0)) =
      ([1, 2, 3], [some 1]) := rfl

theorem three_token_saturation_sources :
    (needsSeed.saturate (tokens 3)).entries.map (fun entry => entry.source 0) = [1, 2, 3] := by
  change (saturateFrom threeStart).entries.map (fun entry => entry.source 0) = _
  rw [saturateFrom_advance threeStart firstHit first_fresh_selected]
  change (saturateFrom threeMiddle).entries.map (fun entry => entry.source 0) = _
  rw [saturateFrom_advance threeMiddle secondHit second_fresh_selected]
  change (saturateFrom threeEnd).entries.map (fun entry => entry.source 0) = _
  rw [saturateFrom_stopped_entries threeEnd third_scan_stops]
  rfl

theorem already_saturated_sources :
    (needsSeed.saturate (tokens 1)).entries.map (fun entry => entry.source 0) = [1] := by
  unfold saturate
  rw [saturateFrom_stopped_entries _ (by rfl)]
  rfl

theorem two_step_covering_word : needsSeed.Execution (tokens 1) [0, 0] (tokens 3) :=
  (check_exact needsSeed _ _ _).mp (by decide +kernel)

theorem three_token_positive :
    (needsSeed.classifyCoverability (tokens 1) (tokens 3)).isPositive = true :=
  (classifyCoverability_exact needsSeed _ _).mpr
    ⟨tokens 3, ⟨[0, 0], two_step_covering_word⟩, Below.refl _⟩

/-- The existing zero-seed obstruction excludes every finite word.
Covering three tokens would also cover one, contradicting that theorem. -/
theorem three_token_negative :
    (needsSeed.classifyCoverability (tokens 0) (tokens 3)).isPositive = false := by
  apply (classifyCoverability_negative_iff needsSeed _ _).mpr
  rintro ⟨after, reachable, enough⟩
  apply zero_seed_not_coverable
  refine ⟨after, reachable, ?_⟩
  exact (show Below (tokens 1) (tokens 3) from fun _ =>
    (by decide +kernel : 1 ≤ 3)).trans enough

/-- A positive classifier answer permits overshoot. It cannot be reused
as an exact-reachability decision, even on this one-transition net. -/
theorem positive_with_unreachable_exact_target :
    (Thesis.Causality.Examples.PetriNet.growth.classifyCoverability
      (Thesis.Causality.Examples.PetriNet.marking 1) (Thesis.Causality.Examples.PetriNet.marking 2)).isPositive = true ∧
    ¬ Thesis.Causality.Examples.PetriNet.growth.Reachable
      (Thesis.Causality.Examples.PetriNet.marking 1) (Thesis.Causality.Examples.PetriNet.marking 2) :=
  ⟨(classifyCoverability_exact _ _ _).mpr Thesis.Causality.Examples.PetriNet.two_coverable,
    Thesis.Causality.Examples.PetriNet.two_not_reachable⟩

def noTransitions : Thesis.Causality.PetriNet 1 0 where
  consume := Fin.elim0
  produce := Fin.elim0

theorem no_transition_sources :
    (noTransitions.saturate (tokens 2)).entries.map (fun entry => entry.source 0) = [2] := by
  unfold saturate
  rw [saturateFrom_stopped_entries _ (by rfl)]
  rfl

theorem no_transition_negative :
    (noTransitions.classifyCoverability (tokens 0) (tokens 2)).isPositive = false := by
  apply (classifyCoverability_negative_iff noTransitions _ _).mpr
  rintro ⟨after, ⟨word, execution⟩, enough⟩
  cases execution with
  | nil =>
      have impossible := enough 0
      change 2 ≤ 0 at impossible
      omega
  | @cons before middle after transition rest fired remaining => exact Fin.elim0 transition

theorem no_transition_positive :
    (noTransitions.classifyCoverability (tokens 3) (tokens 2)).isPositive = true := by
  apply (classifyCoverability_exact noTransitions _ _).mpr
  exact ⟨tokens 3, ⟨[], .nil _⟩, fun _ => (by decide +kernel : 2 ≤ 3)⟩

theorem zero_places_positive (before : Marking 0) :
    (emptyNet.classifyCoverability before Fin.elim0).isPositive = true :=
  (classifyCoverability_exact emptyNet _ _).mpr (empty_dimensions_coverable before)

end Thesis.Causality.Examples.PetriCoverabilitySearch
