import Thesis.Causality.PetriWordCompletion

namespace Thesis.Causality.Examples.PetriWordCompletion

open Thesis.Causality.PetriNet

/-!
# Exact partial endpoints: guards, forced surpluses and unknown coordinates

The two firings of the draining fixture have least endpoints 5 → 1. These
checks exercise all four combinations of fixed and unknown coordinates.
Both fixed values must use the same surplus, even when each separately
exceeds its canonical endpoint. Fixed zero is distinguished from unknown.

The two-counter transfer uses different surpluses in different coordinates;
only the source/target surplus *within* each coordinate must agree. Empty
words still require equal completed endpoints. With no coordinates, the
counter constraints are vacuous for every supplied finite word. This file
contains kernel-checked regressions, not a runtime pilot or a word search.
-/

variable {places transitions : Nat}

def free : PartialMarking places := fun _ => none

def fixed (value : Nat) : PartialMarking 1 := fun _ => some value

def draining : Thesis.Causality.PetriNet 1 1 where
  consume := fun _ _ => 3
  produce := fun _ _ => 1

/-- Read both stored values at one coordinate. This projects the actual
returned witness, rather than independently checking the arithmetic formula. -/
private def resultAt {net : Thesis.Causality.PetriNet places transitions}
    {word : List (Fin transitions)} {source target : PartialMarking places}
    (result : WordCompletionResult net word source target) (place : Fin places) : Option (Nat × Nat) :=
  match result with
  | .positive witness => some (witness.before place, witness.after place)
  | .negative _ => none

theorem both_unknown_choose_zero_surplus :
    resultAt (draining.classifyWordCompletion [0, 0] free free) 0 = some (5, 1) := rfl

theorem source_forces_target :
    resultAt (draining.classifyWordCompletion [0, 0] (fixed 8) free) 0 = some (8, 4) := rfl

theorem target_forces_source :
    resultAt (draining.classifyWordCompletion [0, 0] free (fixed 4)) 0 = some (8, 4) := rfl

theorem compatible_fixed_endpoints :
    resultAt (draining.classifyWordCompletion [0, 0] (fixed 8) (fixed 4)) 0 = some (8, 4) := rfl

/-- Both endpoints individually exceed the canonical values, but their
surpluses 3 and 4 disagree. No independently padded execution is accepted. -/
theorem unequal_surpluses_refuted :
    ¬ draining.WordCompletable [0, 0] (fixed 8) (fixed 5) :=
  (classifyWordCompletion_negative_iff draining [0, 0] (fixed 8) (fixed 5)).mp rfl

/-- Overall token loss is four, yet the second firing needs an initial
five. Completing the unspecified target cannot repair a source of four. -/
theorem insufficient_prefix_supply_refuted :
    ¬ draining.WordCompletable [0, 0] (fixed 4) free :=
  (classifyWordCompletion_negative_iff draining [0, 0] (fixed 4) free).mp rfl

theorem target_below_canonical_refuted :
    ¬ draining.WordCompletable [0, 0] free (fixed 0) :=
  (classifyWordCompletion_negative_iff draining [0, 0] free (fixed 0)).mp rfl

def growth : Thesis.Causality.PetriNet 1 1 where
  consume := fun _ _ => 0
  produce := fun _ _ => 2

theorem fixed_zero_is_not_unknown :
    ¬ growth.WordCompletable [0] (fixed 0) (fixed 3) ∧
      resultAt (growth.classifyWordCompletion [0] free (fixed 3)) 0 = some (1, 3) :=
  ⟨(classifyWordCompletion_negative_iff growth [0] (fixed 0) (fixed 3)).mp rfl, rfl⟩

theorem empty_word_completes_equal_values :
    resultAt (draining.classifyWordCompletion [] free (fixed 7)) 0 = some (7, 7) := rfl

theorem empty_word_does_not_change_fixed_value :
    ¬ draining.WordCompletable [] (fixed 7) (fixed 8) :=
  (classifyWordCompletion_negative_iff draining [] (fixed 7) (fixed 8)).mp rfl

def transfer : Thesis.Causality.PetriNet 2 1 where
  consume := fun _ place => if place = 0 then 0 else 1
  produce := fun _ place => if place = 0 then 1 else 0

def mixedSource : PartialMarking 2 := fun place => if place = 0 then some 3 else none

def mixedTarget : PartialMarking 2 := fun place => if place = 0 then none else some 4

/-- Surplus 3 at the first coordinate and 4 at the second are independent.
The same supplied word executes (3,6) → (5,4), with both constraints exact. -/
theorem mixed_coordinates_use_separate_surpluses :
    resultAt (transfer.classifyWordCompletion [0, 0] mixedSource mixedTarget) 0 = some (3, 5) ∧
      resultAt (transfer.classifyWordCompletion [0, 0] mixedSource mixedTarget) 1 = some (6, 4) :=
  ⟨rfl, rfl⟩

theorem mixed_coordinates_have_actual_execution :
    transfer.WordCompletable [0, 0] mixedSource mixedTarget :=
  (classifyWordCompletion_exact transfer [0, 0] mixedSource mixedTarget).mp rfl

def lateSource : PartialMarking 2 := fun place => if place = 0 then some 3 else some 5

def lateTarget : PartialMarking 2 := fun place => if place = 0 then some 5 else some 4

/-- The first coordinate accepts surplus 3 at both ends. The second needs
surplus 3 at the source but 4 at the target, so rejection must propagate from
the recursive tail after the head has passed. The actual endpoint is (5,3). -/
theorem later_coordinate_rejection : ¬ transfer.WordCompletable [0, 0] lateSource lateTarget :=
  (classifyWordCompletion_negative_iff transfer [0, 0] lateSource lateTarget).mp rfl

/-- No canonical-coordinate evaluation is required when there are no
places. The supplied transitions still constitute the literal word. -/
theorem zero_places_accept_every_supplied_word (net : Thesis.Causality.PetriNet 0 transitions)
    (word : List (Fin transitions)) :
    net.WordCompletable word Fin.elim0 Fin.elim0 :=
  (classifyWordCompletion_exact net word Fin.elim0 Fin.elim0).mp rfl

end Thesis.Causality.Examples.PetriWordCompletion
