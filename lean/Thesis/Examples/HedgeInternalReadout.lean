import Thesis.CausalTransport.HedgeReadoutPlan
import Thesis.Examples.HedgeReadout

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeInternalReadout

open Probability
open HedgePrivateReadout

/-!
# Positivity at a real internal forest pivot, in an unordered repeated plan

The existing three-node fixture extracts a hedge from `P(Y | do(X))` on
`X → R → Y`, with `X ↔ R`.  In its large kept forest, `X` has the child
`R`, so replacing `X` is not a sink-only update.  We verify that coordinate
from the extracted forest rather than passing in a different kept map.

The plan updates `R`, then the earlier `X`, then repeats both updates.  It is
neither increasing nor pivot-distinct.  Nevertheless the new general support
theorem proves full observational positivity of both actual folded SCMs.
Every restoring bit fixes the entire old target assignment, including the
kept child of `X`; no intermediate non-influence proof is supplied.

This tests positivity only.  Replacing an internal vertex can change another
mechanism's output, so the same plan is deliberately not asserted to preserve
observational equality or the original interventional gap.  Those remain the
separate load-bearing obligations of the unrestricted routed countermodel.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- The extracted action vertex has a genuine kept child.  The other
candidate edges are ruled out by the fixture's directed signature; a missing
child would incorrectly make `X` one of its already computed common roots. -/
theorem action_kept_child : extraction.witness.child actionNode = some rootNode := by
  cases childEq : extraction.witness.child actionNode with
  | none =>
      have inside : extraction.witness.large actionNode = true := by
        rw [extraction.large_eq]
        decide +kernel
      have root := (extraction.witness.large_forest.roots_exact actionNode).mpr ⟨inside, childEq⟩
      rw [extracted_roots] at root
      have excluded : rootMask actionNode = false := by decide +kernel
      rw [excluded] at root
      cases root
  | some child =>
      have edge := (extraction.witness.large_forest.child_edge actionNode child childEq).2.2
      have onlyChild : forall child : Fin signature.count,
          signature.directed actionNode child = true -> child = rootNode := by decide +kernel
      exact congrArg some (onlyChild child edge)

theorem action_not_a_kept_sink : extraction.witness.child actionNode ≠ none := by
  rw [action_kept_child]
  exact Option.some_ne_none rootNode

def rootStep : HedgeReadoutStep signature where
  pivot := rootNode
  noise := hedgeReadoutNoise
  injectOld := false
  parentSignal := fun _ => false

def actionStep : HedgeReadoutStep signature where
  pivot := actionNode
  noise := hedgeReadoutNoise
  injectOld := false
  parentSignal := fun _ => false

def plan : List (HedgeReadoutStep signature) := [rootStep, actionStep, rootStep, actionStep]

theorem plan_not_ordered : Not (plan.Pairwise (fun first second => first.pivot.val < second.pivot.val)) := by
  decide +kernel

theorem action_updated_twice : (plan.filter (fun step => step.pivot == actionNode)).length = 2 := by
  decide +kernel

theorem plan_noise_positive : forall step, step ∈ plan ->
    forall bit, step.noise.EventPositive (FiniteProbRecord.singletonEvent bit) := by
  intro step listed bit
  have sameNoise : step.noise = hedgeReadoutNoise := by
    rcases List.mem_cons.mp listed with same | listed
    · subst step; rfl
    rcases List.mem_cons.mp listed with same | listed
    · subst step; rfl
    rcases List.mem_cons.mp listed with same | listed
    · subst step; rfl
    have same := List.mem_singleton.mp listed
    subst step
    rfl
  rw [sameNoise]
  exact hedgeReadoutNoise_positive bit

noncomputable def left :=
  (extraction.witness.largeCarrierDefectParityModel rich).withHedgeReadouts rich plan

noncomputable def right :=
  (extraction.witness.smallCarrierDefectParityModel rich).withHedgeReadouts rich plan

/-- Graph compatibility is retained by every private source, independently
of whether the repeated plan has the ordering needed by other theorems. -/
theorem left_compatible : Compatible left graph :=
  FiniteLatentSCM.withHedgeReadouts_compatible _
    (extraction.witness.largeCarrierDefectParityModel_compatible rich) rich plan

theorem right_compatible : Compatible right graph :=
  FiniteLatentSCM.withHedgeReadouts_compatible _
    (extraction.witness.smallCarrierDefectParityModel_compatible rich) rich plan

/-- These calls supply neither sink readiness nor a finite ordering proof.
The general theorem constructs support through all four actual product priors. -/
theorem left_positive : ObservationallyPositive left :=
  FiniteLatentSCM.withHedgeReadouts_positive _
    (extraction.witness.largeCarrierDefectParityModel_positive rich) rich plan plan_noise_positive

theorem right_positive : ObservationallyPositive right :=
  FiniteLatentSCM.withHedgeReadouts_positive _
    (extraction.witness.smallCarrierDefectParityModel_positive rich) rich plan plan_noise_positive

end HedgeInternalReadout
end Examples
end Causality
end Thesis
