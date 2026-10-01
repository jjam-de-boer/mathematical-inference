import Thesis.CausalTransport.HedgeConditionalCompensatedReadout
import Thesis.CausalTransport.HedgeCompensatedPreimage
import Thesis.Examples.KernelFailureExtraction

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeConditionalProtectedReentry

open Probability
open CurrentKernelFailureExtraction (partitionGraph)

/-!
# A protected outer conditioner alongside responding forest re-entry

The three-value graph has directed edges `A → C → Y` and
`R → E → B → Y`; all vertices except `E` share a bidirected component.
The query is `P(Y | do(A), C)`.  A checked large forest keeps `A → C`,
`C → Y`, and `B → Y`, with common roots `R,Y`; its small forest is
`{R,B,Y}`.  The canonical numerator routes take `R` through the outside
vertex `E` and re-enter the small forest at the responding non-sink `B`.

`C` is a free outer-only conditioner, inside the large forest and later than
the internal readout `B`.  Thus the older outside-large denominator condition
is false, and the older kept-sink route condition is also false.  Local
mechanism closure protects `C` while the unprotected outcome responds to
both of its kept parents.  The new constructor matches the actual routed
denominator and refutes the original conditional in the same positive pair.

The exhausted exchange test and the actual joint/conditional engine failures
are checked separately.  These are explicit valid subgraph forests, not a
claim that the extractor selects this exact small set or child map.  No
latent-prior enumeration or caller-supplied countermodel is used.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def signature : ObservedSignature where
  count := 6
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    ((parent.val = 0 ∧ child.val = 4) ∨ (parent.val = 4 ∧ child.val = 5) ∨
      (parent.val = 1 ∧ child.val = 2) ∨ (parent.val = 2 ∧ child.val = 3) ∨
      (parent.val = 3 ∧ child.val = 5))
  directed_earlier := by
    intro parent child edge
    have selected := of_decide_eq_true edge
    omega

def graph := partitionGraph signature (fun node => decide (node.val = 2))
def actionNode : Fin signature.count := ⟨0, by decide⟩
def firstRoot : Fin signature.count := ⟨1, by decide⟩
def outsideNode : Fin signature.count := ⟨2, by decide⟩
def internalNode : Fin signature.count := ⟨3, by decide⟩
def conditionNode : Fin signature.count := ⟨4, by decide⟩
def outcomeNode : Fin signature.count := ⟨5, by decide⟩

def query : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton outcomeNode
  action := NodeSet.singleton actionNode
  condition := NodeSet.singleton conditionNode
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  action_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => ⟨0, by decide⟩
  second := fun _ => ⟨1, by decide⟩
  first_enumerated := fun _ => List.mem_finRange _
  second_enumerated := fun _ => List.mem_finRange _
  different := fun _ => (by decide : (⟨0, by decide⟩ : Fin 3) ≠ ⟨1, by decide⟩)

/-! ## Directly checked forests and canonical re-entry -/

def large : NodeSet signature := fun node => decide (node.val ≠ 2)
def small : NodeSet signature := fun node => decide (node.val = 1 ∨ node.val = 3 ∨ node.val = 5)
def child : ForestChild signature := fun parent => match parent.val with
  | 0 => some conditionNode
  | 3 => some outcomeNode
  | 4 => some outcomeNode
  | _ => none
def roots : NodeSet signature := keptSinks large child

private theorem large_forest : CForest graph large roots child :=
  cForest_of_child graph large child (by decide +kernel) (by decide +kernel)

private theorem small_forest : CForest graph small roots (restrictChild small child) := by
  have sameRoots : keptSinks small (restrictChild small child) = roots :=
    (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)
  rw [← sameRoots]
  exact cForest_of_child graph small (restrictChild small child) (by decide +kernel) (by decide +kernel)

private theorem roots_reach : forall root, roots root = true -> Exists fun outcome =>
    query.jointNumerator.outcome outcome = true ∧
      DirectedReachableBy signature (fun parent child =>
        mutilatedDirected signature query.action parent child = true) root outcome := by
  intro root selected
  have onlyRoots : forall node : Fin signature.count, roots node = true -> node = firstRoot ∨ node = outcomeNode :=
    by decide +kernel
  refine ⟨outcomeNode, by decide +kernel, ?_⟩
  cases onlyRoots root selected with
  | inl same =>
      subst root
      exact .tail (.tail (.tail (.refl firstRoot)
        (by decide +kernel : mutilatedDirected signature query.action firstRoot outsideNode = true))
        (by decide +kernel : mutilatedDirected signature query.action outsideNode internalNode = true))
        (by decide +kernel : mutilatedDirected signature query.action internalNode outcomeNode = true)
  | inr same => subst root; exact .refl outcomeNode

noncomputable def witness : HedgeWitness graph query.jointNumerator :=
  HedgeWitness.ofForests query.jointNumerator large small roots child large_forest small_forest
    (by
      change forall node : Fin signature.count, small node = true -> large node = true
      decide +kernel) (by decide +kernel)
    ((NodeSet.disjointBool_eq_true_iff _ _).mp (by decide +kernel)) roots_reach

private theorem allowed : forall node, witness.rootReadoutNodes node = true ->
    witness.small node = true ∨ witness.large node = false := by decide +kernel

private theorem condition_protected : NodeSet.Subset query.condition witness.carrierFlowProtectedNodes := by
  change forall node : Fin signature.count, query.condition node = true -> witness.carrierFlowProtectedNodes node = true
  decide +kernel

/-- The conditioner is really inside the large forest, is outer-only,
and occurs after the responding readout rather than before the whole plan. -/
theorem conditioner_is_late_outer : witness.large conditionNode = true ∧ witness.small conditionNode = false ∧
    internalNode.val < conditionNode.val ∧ conditionNode.val < outcomeNode.val := by decide +kernel

/-- The route uses a genuine non-sink whose kept child responds. -/
theorem routed_internal_has_kept_child : witness.rootReadoutNodes internalNode = true ∧
    witness.child internalNode = some outcomeNode := by decide +kernel

/-! ## The actual conditional countermodel and its preserved denominator -/

noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  witness.positiveConditionalCounterexampleOfCarrierFlowOfConditionProtected rich allowed condition_protected

/-- These same compensated endpoints have equal conditioning kernels.
The equality concerns full three-value outputs, not a Boolean-only marginal. -/
theorem denominator_matches : query.jointDenominator.ValueEquivalent counterexample.left counterexample.right :=
  witness.carrierDefectParityModels_carrierFlowReadoutPlan_valueEquivalent_of_protected rich
    (fun _node => FiniteProbRecord.biasedFlip 1 1 (by decide)) allowed query.jointDenominator condition_protected

theorem query_not_identifiable : Not ((GraphModelClass.positive graph).conditionalIdentifiable query) :=
  counterexample.not_identifiable

/-- A third-label action exercises the full protected value identity at
the free conditioner, separately from the `do(second)` separation witness. -/
def thirdLabelAction (node : Fin signature.count) : Option (signature.Value node) :=
  if node = actionNode then some ⟨2, by decide⟩ else none

theorem nested_conditioner_full_value_unchanged
    (unit : (witness.smallCarrierDefectParityModel rich).latent.Assignment) (bits : Fin signature.count -> Bool) :
    ((witness.smallCarrierDefectParityModel rich).withHedgeReadouts rich
        (witness.carrierFlowReadoutPlan rich (fun _node => FiniteProbRecord.biasedFlip 1 1 (by decide)))).evalUnder thirdLabelAction
        ((witness.smallCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits
          (witness.carrierFlowReadoutPlan rich (fun _node => FiniteProbRecord.biasedFlip 1 1 (by decide))) unit) conditionNode =
      (witness.smallCarrierDefectParityModel rich).evalUnder thirdLabelAction unit conditionNode :=
  witness.smallCarrierDefectParityModel_carrierFlowReadoutPlan_evalUnder_eq_of_protected rich
    (fun _node => FiniteProbRecord.biasedFlip 1 1 (by decide)) allowed thirdLabelAction bits unit conditionNode
    (condition_protected conditionNode (by decide +kernel))

/-! ## Preservation does not depend on order, distinctness, support, or bias -/

def balancedNoise : FiniteProbRecord Bool := ⟨[(false, 1), (true, 1)], 2, by decide, rfl⟩
def stayOnlyNoise : FiniteProbRecord Bool := ⟨[(false, 1)], 1, by decide, rfl⟩

/-- The internal pivot is installed twice, with different independent
factor records.  A balanced factor and a point mass deliberately violate the
separation/support premises: denominator preservation needs neither one. -/
noncomputable def descendingRepeatedPlan : List (HedgeReadoutStep signature) :=
  [witness.carrierFlowReadoutStep rich (fun _node => FiniteProbRecord.biasedFlip 1 1 (by decide)) outcomeNode,
    witness.carrierFlowReadoutStep rich (fun _node => balancedNoise) internalNode,
    witness.carrierFlowReadoutStep rich (fun _node => FiniteProbRecord.biasedFlip 1 1 (by decide)) outsideNode,
    witness.carrierFlowReadoutStep rich (fun _node => stayOnlyNoise) internalNode]

theorem descendingRepeatedPlan_pivots : descendingRepeatedPlan.map (fun step => step.pivot) =
    [outcomeNode, internalNode, outsideNode, internalNode] := rfl

theorem descendingRepeatedPlan_not_ordered :
    Not (descendingRepeatedPlan.Pairwise (fun first second => first.pivot.val < second.pivot.val)) := by decide +kernel

private theorem repeated_off_protected : forall step, step ∈ descendingRepeatedPlan ->
    witness.carrierFlowProtectedNodes step.pivot = false := by
  intro step listed
  have pivotListed : step.pivot ∈ descendingRepeatedPlan.map (fun next => next.pivot) :=
    List.mem_map.mpr ⟨step, listed, rfl⟩
  rw [descendingRepeatedPlan_pivots] at pivotListed
  exact (by decide +kernel : forall node : Fin signature.count,
    node ∈ [outcomeNode, internalNode, outsideNode, internalNode] -> witness.carrierFlowProtectedNodes node = false)
    step.pivot pivotListed

/-- Every actual fresh factor integrates out of the protected denominator,
even for this descending repeated plan with incompatible countermodel noise
conditions.  No claim of positivity or numerator separation is made for it. -/
theorem repeated_descending_denominator_left_preserved : query.jointDenominator.ValueEquivalent
    ((witness.largeCarrierDefectParityModel rich).withHedgeReadouts rich descendingRepeatedPlan)
    (witness.largeCarrierDefectParityModel rich) :=
  query.jointDenominator.withHedgeReadouts_valueEquivalent_of_mechanismsClosedOn
    (witness.largeCarrierDefectParityModel rich) rich witness.carrierFlowProtectedNodes
    (witness.largeCarrierDefectParityModel_mechanismsClosedOn_carrierFlowProtectedNodes rich allowed)
    descendingRepeatedPlan repeated_off_protected condition_protected

/-- The nested side retains its denominator under the same independent
repeated instructions, so preservation has not been proved for only one side. -/
theorem repeated_descending_denominator_right_preserved : query.jointDenominator.ValueEquivalent
    ((witness.smallCarrierDefectParityModel rich).withHedgeReadouts rich descendingRepeatedPlan)
    (witness.smallCarrierDefectParityModel rich) :=
  query.jointDenominator.withHedgeReadouts_valueEquivalent_of_mechanismsClosedOn
    (witness.smallCarrierDefectParityModel rich) rich witness.carrierFlowProtectedNodes
    (witness.smallCarrierDefectParityModel_mechanismsClosedOn_carrierFlowProtectedNodes rich allowed)
    descendingRepeatedPlan repeated_off_protected condition_protected

/-! ## Full-label preimages and integration over every actual fresh factor -/

private def internalParents : signature.ParentValues internalNode := fun parent _edge => rich.first parent

/-- An original third-label background is genuinely lost when its old
carrier emits `second` and the readout flips that value to bit zero.  The
new value is `first`, not the original third label. -/
theorem readout_erases_hidden_third_label :
    hedgeNoisyReadout rich internalNode true (fun _parents => false) internalParents
      (hedgeParityCarrierValue rich internalNode true ⟨2, by decide⟩) true = rich.first internalNode := by
  decide +kernel

/-- The bit equation alone accepts this proposed third-label target, but
the full-value preimage correctly rejects it.  This regression prevents a
Boolean-only fibre test from being mistaken for a full-alphabet cylinder. -/
theorem lost_label_preimage_rejected :
    hedgeReadoutRequiredCarrierBit rich internalNode (fun _parents => false) internalParents true ⟨2, by decide⟩ = true ∧
      hedgeReadoutCarrierBackgroundFits rich internalNode (fun _parents => false) internalParents true
        ⟨2, by decide⟩ ⟨2, by decide⟩ = false := by
  decide +kernel

/-- The generic exact preimage includes every pair of three-value labels
and both source/fresh bits; the parent signal is arbitrary as well. -/
theorem full_label_preimage (source signal fresh : Bool) (background target : Fin 3) :
    decide (hedgeNoisyReadout rich internalNode true (fun _parents => signal) internalParents
        (hedgeParityCarrierValue rich internalNode source background) fresh = target) =
      (decide (source = hedgeReadoutRequiredCarrierBit rich internalNode (fun _parents => signal)
          internalParents fresh target) &&
        hedgeReadoutCarrierBackgroundFits rich internalNode (fun _parents => signal) internalParents fresh target background) :=
  hedgeNoisyReadout_carrier_preimage rich internalNode (fun _parents => signal) internalParents source fresh background target

/-- Exercise full-event slice integration on the actual carrier priors.
The local protected-value theorem supplies each fixed-input comparison;
the new integrator then eliminates every real factor of the distinct-pivot
plan.  Noise records and interventions are arbitrary, so this argument does
not inherit support or bias assumptions from the counterexample constructor.

This fixture's conditioner remains protected.  The test validates the
integration boundary, not an unproved global pullback for installed
conditioners; that later proof must supply its own exact slice comparisons. -/
theorem fixed_slice_denominator_matches
    (noise : (node : Fin signature.count) -> FiniteProbRecord Bool)
    (intervention : (node : Fin signature.count) -> Option (signature.Value node))
    (reference : signature.Assignment) :
    QProb.Equiv
      (((witness.largeCarrierDefectParityModel rich).withHedgeReadouts rich (witness.carrierFlowReadoutPlan rich noise)).prior.probVal
        (fun unit => Kernel.agreesOn query.condition reference
          (((witness.largeCarrierDefectParityModel rich).withHedgeReadouts rich
            (witness.carrierFlowReadoutPlan rich noise)).evalUnder intervention unit)))
      (((witness.smallCarrierDefectParityModel rich).withHedgeReadouts rich (witness.carrierFlowReadoutPlan rich noise)).prior.probVal
        (fun unit => Kernel.agreesOn query.condition reference
          (((witness.smallCarrierDefectParityModel rich).withHedgeReadouts rich
            (witness.carrierFlowReadoutPlan rich noise)).evalUnder intervention unit))) := by
  let left := witness.largeCarrierDefectParityModel rich
  let right := witness.smallCarrierDefectParityModel rich
  let steps := witness.carrierFlowReadoutPlan rich noise
  let event := Kernel.agreesOn query.condition reference
  have localEvent : EventDependsOnlyOn (hedgeRootOmittedNodes witness.actionRoot) event := by
    intro first second agree
    apply Kernel.agreesOn_sample_congr
    intro child selected
    have different : child ≠ witness.actionRoot := by
      intro same
      subst child
      have omitted : query.condition witness.actionRoot = false := by decide +kernel
      rw [omitted] at selected
      cases selected
    exact agree child (decide_eq_true different)
  have baseEqual := witness.carrierDefectParityModels_interventional_probVal_equiv_of_rootOmitted
    rich witness.actionRoot witness.actionRoot_in_roots intervention event localEvent
  apply FiniteLatentSCM.withHedgeReadouts_prior_equiv_of_encodedSlices left right rich steps
    (witness.carrierFlowReadoutPlan_pivots_distinct rich noise)
  intro bits
  have leftEqual := left.prior.probVal_congr
    (fun unit => event ((left.withHedgeReadouts rich steps).evalUnder intervention
      (left.hedgeReadoutAssignment rich bits steps unit)))
    (fun unit => event (left.evalUnder intervention unit)) (by
      intro unit
      apply Kernel.agreesOn_sample_congr
      intro child selected
      exact witness.largeCarrierDefectParityModel_carrierFlowReadoutPlan_evalUnder_eq_of_protected rich noise allowed
        intervention bits unit child (condition_protected child selected))
  have rightEqual := right.prior.probVal_congr
    (fun unit => event ((right.withHedgeReadouts rich steps).evalUnder intervention
      (right.hedgeReadoutAssignment rich bits steps unit)))
    (fun unit => event (right.evalUnder intervention unit)) (by
      intro unit
      apply Kernel.agreesOn_sample_congr
      intro child selected
      exact witness.smallCarrierDefectParityModel_carrierFlowReadoutPlan_evalUnder_eq_of_protected rich noise allowed
        intervention bits unit child (condition_protected child selected))
  exact QProb.equiv_trans leftEqual (QProb.equiv_trans baseEqual (QProb.equiv_symm rightEqual))

/-! ## The conditional engine really reaches an irreducible failure -/

private def failed (result : IdentificationOutcome signature) : Bool :=
  match result with
  | .failed _ => true
  | _ => false

theorem no_exchange : (conditionalExchangeStep? graph query).isNone = true := by decide +kernel

theorem joint_program_failed : failed (identifyJointKernel graph query.jointNumerator) = true := by decide +kernel

theorem conditional_program_failed : failed (identifyConditionalKernel graph query) = true := by decide +kernel

end HedgeConditionalProtectedReentry
end Examples
end Causality
end Thesis
