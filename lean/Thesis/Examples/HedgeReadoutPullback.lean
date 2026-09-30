import Thesis.CausalTransport.HedgeRoutedCounterexample
import Thesis.Examples.KernelFailureExtraction

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeMergedReadout

open Probability

/-!
# Two hedge roots merge before reaching the original outcome

The directed graph has `X → R₁`, `X → R₂`, `R₁ → M`, `R₂ → M`, and
`M → Y`.  Only `X,R₁,R₂` are bidirected-confounded.  Corrected ID fails on
`P(Y | do(X))`; the general extractor retains both common roots `R₁,R₂`.
Neither root is an outcome, and neither modified route vertex is confounded.

The two-step plan injects `R₁ XOR R₂` at `M` and copies `M` at `Y`, with
independent positive biased noise at both vertices.  Backward substitution
automatically restores the full two-root parity.  The general constructor
then supplies positive original-query countermodels with the same complete
observational law.  No intermediate kernel separation or observed-law
equation is supplied to it.

Separate duplicate-coordinate checks exercise cancellation of a noise bit
and cancellation of the source as well.  These are semantic checks of the
general finite-plan theorem, not additional bounded-depth failure unpackers.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def signature : ObservedSignature where
  count := 5
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    ((parent.val = 0 ∧ (child.val = 1 ∨ child.val = 2)) ∨
      ((parent.val = 1 ∨ parent.val = 2) ∧ child.val = 3) ∨
      (parent.val = 3 ∧ child.val = 4))
  directed_earlier := by
    intro parent child edge
    have selected := of_decide_eq_true edge
    rcases selected with ⟨_, _ | _⟩ | ⟨(_ | _), _⟩ | ⟨_, _⟩ <;> omega

def graph : ObservedGraph signature where
  bidirected := fun left right => decide (left ≠ right ∧ left.val < 3 ∧ right.val < 3)
  bidirected_symmetric := by
    intro left right edge
    have selected := of_decide_eq_true edge
    exact decide_eq_true ⟨Ne.symm selected.1, selected.2.2, selected.2.1⟩
  bidirected_irreflexive := by
    intro node
    exact decide_eq_false (fun selected => selected.1 rfl)

def actionNode : Fin signature.count := ⟨0, by decide⟩
def firstRoot : Fin signature.count := ⟨1, by decide⟩
def secondRoot : Fin signature.count := ⟨2, by decide⟩
def mergeNode : Fin signature.count := ⟨3, by decide⟩
def outcomeNode : Fin signature.count := ⟨4, by decide⟩
def forestHost : NodeSet signature := fun node => decide (node.val < 3)
def rootMask : NodeSet signature := fun node => decide (node.val = 1 ∨ node.val = 2)

def query : JointKernelQuery signature where
  outcome := NodeSet.singleton outcomeNode
  action := NodeSet.singleton actionNode
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => false
  second := fun _ => true
  first_enumerated := fun _ => List.mem_cons_self
  second_enumerated := fun _ => List.mem_cons.mpr (Or.inr List.mem_cons_self)
  different := fun _ => Bool.false_ne_true

private def computedFailure : IdentificationFail signature :=
  match identifyJointKernel graph query with
  | .failed fail => fail
  | _ => ⟨NodeSet.empty, NodeSet.empty⟩

theorem query_failed : identifyJointKernel graph query = .failed ⟨forestHost, rootMask⟩ := by
  have failed : identifyJointKernel graph query = .failed computedFailure := rfl
  have large : computedFailure.remaining = forestHost :=
    (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)
  have small : computedFailure.free = rootMask :=
    (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)
  have coordinates : computedFailure = ⟨forestHost, rootMask⟩ := by
    cases record : computedFailure with
    | mk remaining free =>
        rw [record] at large small
        cases large
        cases small
        rfl
  exact failed.trans (congrArg IdentificationOutcome.failed coordinates)

noncomputable def extraction := identifyJointKernelFailedHedge query query_failed

private theorem root_child_none (node : Fin signature.count) (selected : rootMask node = true) :
    extraction.witness.child node = none := by
  have noInternalEdge : forall parent child : Fin signature.count,
      rootMask parent = true -> forestHost child = true -> signature.directed parent child = false := by decide +kernel
  cases childEq : extraction.witness.child node with
  | none => rfl
  | some child =>
      have edge := extraction.witness.large_forest.child_edge node child childEq
      have included : forestHost child = true := by simpa only [extraction.large_eq] using edge.2.1
      rw [noInternalEdge node child selected included] at edge
      cases edge.2.2

theorem extracted_roots : extraction.witness.roots = rootMask := by
  funext node
  cases selected : rootMask node with
  | false =>
      cases root : extraction.witness.roots node with
      | false => rfl
      | true =>
          have small := ((extraction.witness.small_forest.roots_exact node).mp root).1
          rw [extraction.small_eq] at small
          change rootMask node = true at small
          rw [selected] at small
          cases small
  | true =>
      apply (extraction.witness.large_forest.roots_exact node).mpr
      have small : extraction.witness.small node = true := by rw [extraction.small_eq]; exact selected
      exact ⟨extraction.witness.small_subset_large node small, root_child_none node selected⟩

theorem extracted_root_members : NodeSet.members extraction.witness.roots = [firstRoot, secondRoot] := by
  rw [extracted_roots]
  decide +kernel

private theorem outside_child_none (node : Fin signature.count) (outside : forestHost node = false) :
    extraction.witness.child node = none :=
  extraction.witness.large_forest.child_off_set node (by rw [extraction.large_eq]; exact outside)

/-! ## A merging plan, followed by a real extra routing edge -/

def noise : FiniteProbRecord Bool := ⟨[(false, 2), (true, 1)], 3, by decide, rfl⟩

def mergeStep : HedgeLinearReadoutStep signature where
  pivot := mergeNode
  noise := noise
  injectOld := false
  parents := [firstRoot, secondRoot]
  parent_edges := by
    intro parent listed
    rcases List.mem_cons.mp listed with same | listed
    · subst parent; decide +kernel
    · have same : parent = secondRoot := List.mem_singleton.mp listed
      subst parent; decide +kernel

def outcomeStep : HedgeLinearReadoutStep signature where
  pivot := outcomeNode
  noise := noise
  injectOld := false
  parents := [mergeNode]
  parent_edges := by
    intro parent listed
    have same : parent = mergeNode := List.mem_singleton.mp listed
    subst parent
    decide +kernel

def plan : List (HedgeLinearReadoutStep signature) := [mergeStep, outcomeStep]

theorem plan_ordered : plan.Pairwise (fun first second => first.pivot.val < second.pivot.val) := by decide +kernel

theorem plan_sinks : forall step, step ∈ plan -> extraction.witness.child step.pivot = none := by
  intro step listed
  rcases List.mem_cons.mp listed with same | listed
  · subst step
    exact outside_child_none mergeNode (by decide +kernel)
  · have same : step = outcomeStep := List.mem_singleton.mp listed
    subst step
    exact outside_child_none outcomeNode (by decide +kernel)

theorem plan_free : forall step, step ∈ plan -> query.action step.pivot = false := by decide +kernel

theorem plan_noise_positive : forall step, step ∈ plan ->
    forall bit, step.noise.EventPositive (FiniteProbRecord.singletonEvent bit) := by
  intro step listed bit
  rcases List.mem_cons.mp listed with same | listed
  · subst step; cases bit <;> decide +kernel
  · have same : step = outcomeStep := List.mem_singleton.mp listed
    subst step; cases bit <;> decide +kernel

theorem plan_biased : forall step, step ∈ plan -> Exists fun gap =>
    0 < gap ∧ FiniteProbRecord.eventMass step.noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass step.noise.atoms id + gap := by
  intro step listed
  refine ⟨1, by decide, ?_⟩
  rcases List.mem_cons.mp listed with same | listed
  · subst step; decide +kernel
  · have same : step = outcomeStep := List.mem_singleton.mp listed
    subst step; decide +kernel

theorem plan_pullback : HedgeLinearReadoutPlan.pullbackNodes plan [outcomeNode] = [firstRoot, secondRoot] := rfl

/-- One actual query counterexample, with both roots recovered by the
general finite substitution theorem.  Copying only one root is not used. -/
noncomputable def originalCounterexample : CounterexampleIn (GraphModelClass.positive graph) query :=
  extraction.witness.positiveCounterexampleOfReadoutPlan rich plan plan_ordered plan_sinks plan_free
    plan_noise_positive plan_biased [outcomeNode]
    (by intro node listed; have same := List.mem_singleton.mp listed; subst node; decide +kernel)
    (by
      intro sample
      rw [plan_pullback]
      unfold hedgeRootParityEvent hedgeNodeXor
      rw [extracted_root_members]
      rfl)

theorem original_query_not_identifiable : Not ((GraphModelClass.positive graph).identifiable query) :=
  originalCounterexample.not_identifiable

/-! ## Duplicate coordinates cancel the same noise and source -/

theorem duplicate_outcome_noise_cancelled : outcomeStep.noiseActive [outcomeNode, outcomeNode] = false := rfl

theorem duplicate_outcome_effective_bias :
    FiniteProbRecord.eventMass (outcomeStep.effectiveNoise [outcomeNode, outcomeNode]).atoms (fun bit => !bit) = 3 ∧
      FiniteProbRecord.eventMass (outcomeStep.effectiveNoise [outcomeNode, outcomeNode]).atoms id = 0 := by decide +kernel

theorem duplicate_plan_pullback_cancelled (sample : signature.Assignment) :
    hedgeParityList rich (HedgeLinearReadoutPlan.pullbackNodes plan [outcomeNode, outcomeNode]) sample = false := by
  change hedgeParityList rich ([firstRoot, secondRoot] ++ [firstRoot, secondRoot]) sample = false
  rw [hedgeParityList_append]
  cases hedgeParityList rich [firstRoot, secondRoot] sample <;> rfl

end HedgeMergedReadout
end Examples
end Causality
end Thesis
