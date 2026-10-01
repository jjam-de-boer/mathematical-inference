import Thesis.CausalTransport.HedgeReadoutPlan
import Thesis.Examples.KernelFailureExtraction

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeCarrierReentryReplay

open Probability
open CurrentKernelFailureExtraction (partitionGraph)

/-!
# A finite nonbinary plan with outside-to-internal forest re-entry

The ambient chain is `A → R → E → B → Y`.  The large forest contains
`A,R,B,Y`, the small forest contains `R,B,Y`, and the common roots are `R,Y`.
Its kept edges are `A → R` and `B → Y`; the ambient route from the first root
to the queried outcome leaves the forest at `E` and re-enters at `B`.
Thus `B` is a permitted small-forest pivot but not a kept sink, and its child
`Y` genuinely responds to changes at that pivot.

These are directly checked subgraph forests, not an asserted normalization
of the ID extractor's chosen child map.  The regression exercises both the
automatically generated all-root plan and an unordered repeated manual plan.
All five observed alphabets have three values.  The complete updated SCMs
retain compatibility, strict positivity, and full observational equality.
No original-query separation claim is made: the general interventional
pullback through responding descendants remains a separate proof obligation.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def signature : ObservedSignature where
  count := 5
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide (child.val = parent.val + 1)
  directed_earlier := by
    intro parent child edge
    have next := of_decide_eq_true edge
    omega

def graph := partitionGraph signature (fun node => decide (node.val = 2))
def actionNode : Fin signature.count := ⟨0, by decide⟩
def firstRoot : Fin signature.count := ⟨1, by decide⟩
def outsideNode : Fin signature.count := ⟨2, by decide⟩
def internalNode : Fin signature.count := ⟨3, by decide⟩
def outcomeNode : Fin signature.count := ⟨4, by decide⟩
def large : NodeSet signature := fun node => decide (node.val ≠ 2)
def small : NodeSet signature := fun node => decide (node.val ≠ 0 ∧ node.val ≠ 2)
def child : ForestChild signature := closedForestChild large small
def roots : NodeSet signature := keptSinks large child

def query : JointKernelQuery signature where
  outcome := NodeSet.singleton outcomeNode
  action := NodeSet.singleton actionNode
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => ⟨0, by decide⟩
  second := fun _ => ⟨1, by decide⟩
  first_enumerated := fun _ => List.mem_finRange _
  second_enumerated := fun _ => List.mem_finRange _
  different := fun _ => (by decide : (⟨0, by decide⟩ : Fin 3) ≠ ⟨1, by decide⟩)

private theorem large_forest : CForest graph large roots child :=
  cForest_of_child graph large child (by decide +kernel) (by decide +kernel)

private theorem small_forest : CForest graph small roots (restrictChild small child) := by
  have sameRoots : keptSinks small (restrictChild small child) = roots :=
    (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)
  rw [← sameRoots]
  exact cForest_of_child graph small (restrictChild small child) (by decide +kernel) (by decide +kernel)

private theorem roots_reach : forall root, roots root = true ->
    Exists fun outcome => query.outcome outcome = true ∧
      DirectedReachableBy signature (fun parent child =>
        mutilatedDirected signature query.action parent child = true) root outcome := by
  intro root selected
  have onlyRoots : forall node : Fin signature.count, roots node = true ->
      node = firstRoot ∨ node = outcomeNode := by decide +kernel
  refine ⟨outcomeNode, by decide +kernel, ?_⟩
  cases onlyRoots root selected with
  | inl same =>
      subst root
      exact .tail (.tail (.tail (.refl firstRoot)
        (by decide +kernel : mutilatedDirected signature query.action firstRoot outsideNode = true))
        (by decide +kernel : mutilatedDirected signature query.action outsideNode internalNode = true))
        (by decide +kernel : mutilatedDirected signature query.action internalNode outcomeNode = true)
  | inr same => subst root; exact .refl outcomeNode

noncomputable def witness : HedgeWitness graph query :=
  HedgeWitness.ofForests query large small roots child large_forest small_forest
    (by
      change forall node : Fin signature.count, small node = true -> large node = true
      decide +kernel) (by decide +kernel)
    ((NodeSet.disjointBool_eq_true_iff _ _).mp (by decide +kernel)) roots_reach

theorem internal_in_small : witness.small internalNode = true := by decide +kernel
theorem internal_has_kept_child : witness.child internalNode = some outcomeNode := by decide +kernel
theorem outside_not_in_large : witness.large outsideNode = false := by decide +kernel

def noise : FiniteProbRecord Bool := ⟨[(false, 2), (true, 1)], 3, by decide, rfl⟩

private theorem noise_positive (bit : Bool) : noise.EventPositive (FiniteProbRecord.singletonEvent bit) := by
  cases bit <;> decide +kernel

/-! ## The generated all-root route really contains an internal kept pivot -/

/-- The route leaves at `E` and re-enters at `B`; it is not a sink-only
forest route dressed up as an internal-readout test. -/
theorem canonical_plan_pivots :
    (witness.rootReadoutPlan (fun _node => noise)).map (fun step => step.pivot) =
      [firstRoot, outsideNode, internalNode, outcomeNode] := by decide +kernel

private theorem canonical_allowed : forall node, witness.rootReadoutNodes node = true ->
    witness.small node = true ∨ witness.large node = false := by decide +kernel

theorem canonical_observationally_equivalent : ObservationallyEquivalent
    ((witness.largeCarrierDefectParityModel rich).withHedgeReadouts rich
      (HedgeLinearReadoutPlan.readouts rich (witness.rootReadoutPlan (fun _node => noise))))
    ((witness.smallCarrierDefectParityModel rich).withHedgeReadouts rich
      (HedgeLinearReadoutPlan.readouts rich (witness.rootReadoutPlan (fun _node => noise)))) :=
  witness.carrierDefectParityModels_rootReadoutPlan_observationally_equivalent_of_small_or_outside
    rich (fun _node => noise) canonical_allowed

private theorem canonical_noise_positive : forall instruction,
    instruction ∈ HedgeLinearReadoutPlan.readouts rich (witness.rootReadoutPlan (fun _node => noise)) ->
    forall bit, instruction.noise.EventPositive (FiniteProbRecord.singletonEvent bit) := by
  intro instruction listed bit
  rcases List.mem_map.mp listed with ⟨linear, inPlan, same⟩
  subst instruction
  rcases List.mem_map.mp inPlan with ⟨node, _member, same⟩
  subst linear
  exact noise_positive bit

theorem canonical_left_positive : ObservationallyPositive
    ((witness.largeCarrierDefectParityModel rich).withHedgeReadouts rich
      (HedgeLinearReadoutPlan.readouts rich (witness.rootReadoutPlan (fun _node => noise)))) :=
  FiniteLatentSCM.withHedgeReadouts_positive _ (witness.largeCarrierDefectParityModel_positive rich)
    rich _ canonical_noise_positive

theorem canonical_right_positive : ObservationallyPositive
    ((witness.smallCarrierDefectParityModel rich).withHedgeReadouts rich
      (HedgeLinearReadoutPlan.readouts rich (witness.rootReadoutPlan (fun _node => noise)))) :=
  FiniteLatentSCM.withHedgeReadouts_positive _ (witness.smallCarrierDefectParityModel_positive rich)
    rich _ canonical_noise_positive

theorem canonical_left_compatible : Compatible
    ((witness.largeCarrierDefectParityModel rich).withHedgeReadouts rich
      (HedgeLinearReadoutPlan.readouts rich (witness.rootReadoutPlan (fun _node => noise)))) graph :=
  FiniteLatentSCM.withHedgeReadouts_compatible _ (witness.largeCarrierDefectParityModel_compatible rich) rich _

theorem canonical_right_compatible : Compatible
    ((witness.smallCarrierDefectParityModel rich).withHedgeReadouts rich
      (HedgeLinearReadoutPlan.readouts rich (witness.rootReadoutPlan (fun _node => noise)))) graph :=
  FiniteLatentSCM.withHedgeReadouts_compatible _ (witness.smallCarrierDefectParityModel_compatible rich) rich _

/-! ## Arbitrary order and repeats with distinct actual noise factors -/

def outsideStep : HedgeReadoutStep signature where
  pivot := outsideNode
  noise := noise
  injectOld := false
  parentSignal := fun parents => hedgeIsSecond rich firstRoot (parents firstRoot (by decide +kernel))

def internalStep : HedgeReadoutStep signature where
  pivot := internalNode
  noise := noise
  injectOld := false
  parentSignal := fun parents => hedgeIsSecond rich outsideNode (parents outsideNode (by decide +kernel))

def outcomeStep : HedgeReadoutStep signature where
  pivot := outcomeNode
  noise := ⟨[(false, 1), (true, 3)], 4, by decide, rfl⟩
  injectOld := true
  parentSignal := fun parents => hedgeIsSecond rich internalNode (parents internalNode (by decide +kernel))

def plan : List (HedgeReadoutStep signature) := [outsideStep, internalStep, outcomeStep, internalStep]

theorem plan_not_ordered : Not (plan.Pairwise (fun first second => first.pivot.val < second.pivot.val)) := by
  decide +kernel

theorem internal_updated_twice : (plan.filter (fun step => step.pivot == internalNode)).length = 2 := by
  decide +kernel

private theorem plan_allowed : forall step, step ∈ plan ->
    witness.small step.pivot = true ∨ witness.large step.pivot = false := by
  intro step listed
  simp only [plan, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with same | same | same | same <;> subst step <;> decide +kernel

private theorem plan_noise_positive : forall step, step ∈ plan ->
    forall bit, step.noise.EventPositive (FiniteProbRecord.singletonEvent bit) := by
  intro step listed bit
  simp only [plan, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with same | same | same | same <;> subst step <;> cases bit <;> decide +kernel

noncomputable def left := (witness.largeCarrierDefectParityModel rich).withHedgeReadouts rich plan
noncomputable def right := (witness.smallCarrierDefectParityModel rich).withHedgeReadouts rich plan

theorem plan_observationally_equivalent : ObservationallyEquivalent left right :=
  witness.carrierDefectParityModels_withHedgeReadouts_observationally_equivalent_of_small_or_outside
    rich plan plan_allowed

theorem left_positive : ObservationallyPositive left :=
  FiniteLatentSCM.withHedgeReadouts_positive _ (witness.largeCarrierDefectParityModel_positive rich)
    rich plan plan_noise_positive

theorem right_positive : ObservationallyPositive right :=
  FiniteLatentSCM.withHedgeReadouts_positive _ (witness.smallCarrierDefectParityModel_positive rich)
    rich plan plan_noise_positive

theorem left_compatible : Compatible left graph :=
  FiniteLatentSCM.withHedgeReadouts_compatible _ (witness.largeCarrierDefectParityModel_compatible rich) rich plan

theorem right_compatible : Compatible right graph :=
  FiniteLatentSCM.withHedgeReadouts_compatible _ (witness.smallCarrierDefectParityModel_compatible rich) rich plan

end HedgeCarrierReentryReplay
end Examples
end Causality
end Thesis
