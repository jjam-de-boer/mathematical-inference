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

The unordered plan tests positivity only.  A separate local regression below
checks the exact signal channel at its genuine internal pivot, and parity
substitution with odd and even repeated pivot occurrences.  Those local
theorems need no non-influence proof either: acyclicity keeps every parent
unchanged.  Replacing an internal vertex can nevertheless change a later
mechanism's output, so the same plan is deliberately not asserted to preserve
observational equality or the original interventional gap.  Those remain the
separate load-bearing obligations of the unrestricted routed countermodel.

The final negative regression checks that this distinction is essential:
overwriting the internal action vertex by the same supported private noise
on both sides destroys their old observational equality.  The two new models
remain compatible and positive.  This refutes a blanket extension to all
internal updates; it does not refute a more carefully constructed routing
argument whose pivots are free under the original query.
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

/-! ## Exact local channels do not require an internal pivot to be ignored -/

/-- Unlike the support-only plan's overwrite, this step retains the old
action bit before applying biased private noise.  Its pivot is the actual
internal vertex whose kept child was checked above, not a substituted sink. -/
def internalSignalStep : HedgeLinearReadoutStep signature where
  pivot := actionNode
  noise := hedgeReadoutNoise
  injectOld := true
  parents := []
  parent_edges := by intro _ listed; cases listed

/-- The one-pivot channel theorem applies with no sink or non-influence
argument.  Intervening at a later coordinate is allowed, but the internal
pivot must remain free; fixing it would erase the readout response. -/
theorem internal_signal_channel
    (intervention : (node : Fin signature.count) -> Option (signature.Value node))
    (free : intervention actionNode = none) :
    QProb.Equiv
      (((internalSignalStep.toReadoutStep rich).apply rich
        (extraction.witness.largeCarrierDefectParityModel rich)).interventionalValue
        intervention (fun sample => hedgeIsSecond rich actionNode (sample actionNode)))
      (((extraction.witness.largeCarrierDefectParityModel rich).noisyInterventionalSignal
        intervention (hedgeReadoutSignal rich actionNode true (internalSignalStep.parentSignal rich))
        hedgeReadoutNoise).probVal id) :=
  FiniteLatentSCM.withHedgeReadout_signal_equiv _ rich actionNode hedgeReadoutNoise true
    (internalSignalStep.parentSignal rich) intervention free

/-- Three occurrences retain the same private bit once, while two cancel
it.  The event substitution keeps duplicates rather than silently replacing
them by a node set. -/
theorem odd_pivot_retains_noise :
    internalSignalStep.noiseActive [actionNode, actionNode, actionNode] = true := by decide +kernel

theorem even_pivot_cancels_noise :
    internalSignalStep.noiseActive [actionNode, actionNode] = false := by decide +kernel

/-- Biased-channel reflection for an odd repeated event at a real internal
vertex.  Both actual carrier models enter the general prefix-local theorem;
neither supplies an `OtherMechanismsIgnore` proof.  This tests the exact local
event identity, not separation of the original query, whose action fixes `X`. -/
theorem internal_parity_equiv_iff
    (intervention : (node : Fin signature.count) -> Option (signature.Value node))
    (free : intervention actionNode = none) :
    QProb.Equiv
      (((internalSignalStep.toReadoutStep rich).apply rich
        (extraction.witness.largeCarrierDefectParityModel rich)).interventionalValue
        intervention (hedgeParityList rich [actionNode, actionNode, actionNode]))
      (((internalSignalStep.toReadoutStep rich).apply rich
        (extraction.witness.smallCarrierDefectParityModel rich)).interventionalValue
        intervention (hedgeParityList rich [actionNode, actionNode, actionNode])) ↔
    QProb.Equiv
      ((extraction.witness.largeCarrierDefectParityModel rich).interventionalValue intervention
        (hedgeParityList rich (internalSignalStep.pullbackNodes [actionNode, actionNode, actionNode])))
      ((extraction.witness.smallCarrierDefectParityModel rich).interventionalValue intervention
        (hedgeParityList rich (internalSignalStep.pullbackNodes [actionNode, actionNode, actionNode]))) :=
  internalSignalStep.interventionalValue_equiv_iff_of_prefix _ _ rich
    [actionNode, actionNode, actionNode] (by decide +kernel) intervention free 1 (by decide)
    hedgeReadoutNoise_bias

/-! ## Internal replacements need not preserve the whole observational law -/

/-- The fixture's complete kept map, used only to expose the finite table
for the kernel-checked negative regression.  It is proved equal to the
extracted map below; no forest is silently replaced in the construction. -/
private def fixtureChild : ForestChild signature :=
  fun node => if node = actionNode then some rootNode else none

private theorem extracted_child : extraction.witness.child = fixtureChild := by
  funext node
  have casesNode : forall node : Fin signature.count,
      node = actionNode ∨ node = rootNode ∨ node = outcomeNode := by decide +kernel
  rcases casesNode node with same | same | same
  · subst node
    rw [action_kept_child]
    rfl
  · subst node
    have root : extraction.witness.roots rootNode = true := by rw [extracted_roots]; decide +kernel
    have none := ((extraction.witness.large_forest.roots_exact rootNode).mp root).2
    rw [none]
    rfl
  · subst node
    rw [outcome_kept_child_none]
    rfl

private theorem extracted_actionRoot : extraction.witness.actionRoot = rootNode := by
  have root := extraction.witness.actionRoot_in_roots
  rw [extracted_roots] at root
  exact of_decide_eq_true root

noncomputable def actionOverwriteLeft :=
  (extraction.witness.largeCarrierDefectParityModel rich).withHedgeReadout rich actionNode
    hedgeReadoutNoise false (fun _ => false)

noncomputable def actionOverwriteRight :=
  (extraction.witness.smallCarrierDefectParityModel rich).withHedgeReadout rich actionNode
    hedgeReadoutNoise false (fun _ => false)

/-- The failure of observational equality below is not caused by leaving
the original positive graph model class.  Private incidence retains graph
compatibility, and the general restoring bit supplies full support. -/
theorem actionOverwriteLeft_mem : (GraphModelClass.positive graph).Mem actionOverwriteLeft :=
  ⟨FiniteLatentSCM.withHedgeReadout_compatible _
      (extraction.witness.largeCarrierDefectParityModel_compatible rich) rich actionNode
      hedgeReadoutNoise false (fun _ => false),
    FiniteLatentSCM.withHedgeReadout_positive _
      (extraction.witness.largeCarrierDefectParityModel_positive rich) rich actionNode
      hedgeReadoutNoise hedgeReadoutNoise_positive false (fun _ => false)⟩

theorem actionOverwriteRight_mem : (GraphModelClass.positive graph).Mem actionOverwriteRight :=
  ⟨FiniteLatentSCM.withHedgeReadout_compatible _
      (extraction.witness.smallCarrierDefectParityModel_compatible rich) rich actionNode
      hedgeReadoutNoise false (fun _ => false),
    FiniteLatentSCM.withHedgeReadout_positive _
      (extraction.witness.smallCarrierDefectParityModel_positive rich) rich actionNode
      hedgeReadoutNoise hedgeReadoutNoise_positive false (fun _ => false)⟩

/-- A root-coordinate event distinguishes the new observational laws.
Only the large mechanism reads the overwritten action at the kept child;
the small mechanism omits that parent, so the common update need not be a
common transformation of the entire old observed assignment.

The original carrier pair is observationally equivalent by the general
hedge theorem.  Here all forest data are first identified with their actual
computed fixture coordinates, then the finite probability comparison is
checked by the Lean kernel, not `native_decide`.  The pivot is an action
vertex: this example rules out an unrestricted internal-update preservation
lemma, not every possible free-pivot routing construction. -/
theorem actionOverwrite_not_observationally_equivalent :
    Not (ObservationallyEquivalent actionOverwriteLeft actionOverwriteRight) := by
  have separated : Not (QProb.Equiv
      (actionOverwriteLeft.observationalValue (fun sample => hedgeIsSecond rich rootNode (sample rootNode)))
      (actionOverwriteRight.observationalValue (fun sample => hedgeIsSecond rich rootNode (sample rootNode)))) := by
    unfold actionOverwriteLeft actionOverwriteRight HedgeWitness.largeCarrierDefectParityModel
      HedgeWitness.smallCarrierDefectParityModel HedgeWitness.largeParityModel HedgeWitness.smallParityModel
    rw [extracted_actionRoot, extracted_child, extraction.large_eq, extraction.small_eq]
    decide +kernel
  intro observational
  exact separated (observational (fun sample => hedgeIsSecond rich rootNode (sample rootNode)))

end HedgeInternalReadout
end Examples
end Causality
end Thesis
