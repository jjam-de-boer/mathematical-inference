import Thesis.Causality.PetriControlCoverability
import Thesis.Examples.PetriControl

namespace Thesis.Causality.Examples.PetriControlCoverability

open Thesis.Causality.PetriNet
open Thesis.Causality.ControlledPetriNet
open Thesis.Causality.Examples.PetriControl

/-!
# Original-space controlled coverability regressions

The guard fixture has the correct control token but consumes two ordinary
counter tokens. One token cannot start any nonempty word; two tokens enable
a firing that produces four, genuinely overshooting the target of three.
An already covered target is still accepted through the empty word, even
when that transition is disabled.

A supplied compiled witness has a raw endpoint. Its conversion is checked
for the unchanged word and recovered original counter value, and its
original-space certificate proves the public classifier's positive result.
Negative proofs exclude all finite words. Existing fixtures separately check
an unreachable target state, a state-changing positive query, no edges and
zero counter places. No kernel normalization of the complete search, native
decision axiom, runtime pilot or new controlled pumping adapter is used.
-/

def guarded : ControlledPetriNet 1 2 1 where
  net := { consume := fun _ _ => 2, produce := fun _ _ => 4 }
  source := fun _ => 0
  target := fun _ => 0

theorem matching_control_insufficient_tokens :
    guarded.compiled.check (encode (0 : Fin 2) (tokens 1)) [0] (encode (0 : Fin 2) (tokens 3)) = false := by
  decide +kernel

/-- No nonempty execution can start. The empty execution falls short of
the requested target, so failure is about every word, not just one step. -/
theorem insufficient_not_coverable : ¬ guarded.Coverable 0 (tokens 1) 0 (tokens 2) := by
  rintro ⟨word, after, ⟨_, execution⟩, covers⟩
  cases execution with
  | nil =>
      have impossible := covers (0 : Fin 1)
      change 2 ≤ 1 at impossible
      omega
  | cons fired remaining =>
      have impossible := fired.1 (0 : Fin 1)
      change 2 ≤ 1 at impossible
      omega

theorem insufficient_classifier_negative :
    (guarded.classifyCoverability 0 (tokens 1) 0 (tokens 2)).isPositive = false :=
  (ControlledPetriNet.classifyCoverability_negative_iff _ _ _ _ _).mpr insufficient_not_coverable

/-- A flat three-coordinate marking, rather than an assumed `encode`
shape, exercises the actual witness-to-original-space conversion. -/
def rawGuardEndpoint : Marking 3 :=
  fun place => if place = 0 then 4 else if place = 1 then 1 else 0

def compiledGuardWitness : PetriNet.CoverabilityWitness guarded.compiled (encode (0 : Fin 2) (tokens 3)) where
  source := encode (0 : Fin 2) (tokens 2)
  word := [0]
  endpoint := rawGuardEndpoint
  execution := (PetriNet.check_exact guarded.compiled _ _ _).mp (by decide +kernel)
  covers := by unfold Below; decide +kernel

def recoveredGuard : ControlledPetriNet.CoverabilityWitness guarded 0 (tokens 2) 0 (tokens 3) :=
  ControlledPetriNet.CoverabilityWitness.ofCompiled compiledGuardWitness rfl

theorem recovered_word : recoveredGuard.word = [0] := rfl

theorem recovered_counter_value : recoveredGuard.endpoint 0 = 4 := rfl

theorem recovered_overshoot : 3 < recoveredGuard.endpoint 0 := by decide +kernel

theorem recovered_exact_control : guarded.controlRun 0 recoveredGuard.word = some 0 :=
  recoveredGuard.execution.1

theorem sufficient_classifier_positive :
    (guarded.classifyCoverability 0 (tokens 2) 0 (tokens 3)).isPositive = true :=
  (ControlledPetriNet.classifyCoverability_exact _ _ _ _ _).mpr recoveredGuard.coverable

/-- A blocked transition does not prevent covering a target already held
at the correct control state. No artificial nonempty-word premise is added. -/
theorem already_covered_with_disabled_edge :
    (guarded.classifyCoverability 0 (tokens 1) 0 (tokens 1)).isPositive = true :=
  (ControlledPetriNet.classifyCoverability_exact _ _ _ _ _).mpr
    ⟨[], tokens 1, ⟨rfl, .nil _⟩, fun _ => Nat.le_refl _⟩

private theorem guarded_control_returns (word : List (Fin 1)) : guarded.controlRun 0 word = some 0 := by
  induction word with
  | nil => rfl
  | cons edge rest ih =>
      exact (controlRun_cons_iff guarded _ _ _ _).mpr ⟨rfl, ih⟩

theorem wrong_target_state_not_coverable : ¬ guarded.Coverable 0 (tokens 2) 1 (tokens 3) := by
  rintro ⟨word, after, execution, _⟩
  have same : (0 : Fin 2) = 1 :=
    Option.some.inj ((guarded_control_returns word).symm.trans execution.1)
  exact (by decide +kernel : (0 : Fin 2) ≠ 1) same

theorem wrong_target_classifier_negative :
    (guarded.classifyCoverability 0 (tokens 2) 1 (tokens 3)).isPositive = false :=
  (ControlledPetriNet.classifyCoverability_negative_iff _ _ _ _ _).mpr wrong_target_state_not_coverable

/-- Coverability can reach a different state. Returning to the source is
a requirement of pumping, not of this ordinary controlled query. -/
theorem state_changing_classifier_positive :
    (move.classifyCoverability 0 (tokens 0) 1 (tokens 1)).isPositive = true :=
  (ControlledPetriNet.classifyCoverability_exact _ _ _ _ _).mpr move_covers_destination

theorem no_edges_same_state_positive :
    (noEdges.classifyCoverability 0 (tokens 3) 0 (tokens 2)).isPositive = true :=
  (ControlledPetriNet.classifyCoverability_exact _ _ _ _ _).mpr no_edges_same_state_coverable

theorem no_edges_other_state_negative :
    (noEdges.classifyCoverability 0 (tokens 3) 1 (tokens 2)).isPositive = false :=
  (ControlledPetriNet.classifyCoverability_negative_iff _ _ _ _ _).mpr no_edges_other_state_not_coverable

theorem zero_counter_classifier_positive :
    (controlOnly.classifyCoverability 0 Fin.elim0 1 Fin.elim0).isPositive = true := by
  apply (ControlledPetriNet.classifyCoverability_exact _ _ _ _ _).mpr
  apply (coverable_compiled_iff controlOnly _ _ _ _).mp
  exact ⟨encode (1 : Fin 2) (Fin.elim0 : Marking 0), ⟨[0], zero_counter_places⟩,
    fun _ => Nat.le_refl _⟩

end Thesis.Causality.Examples.PetriControlCoverability
