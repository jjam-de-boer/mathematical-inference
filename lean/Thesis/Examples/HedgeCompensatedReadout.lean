import Thesis.CausalTransport.HedgeCompensatedReadout
import Thesis.Examples.HedgeCarrierReplayPlan

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeCompensatedReentry

open Probability
open HedgeCarrierReentryReplay (signature graph rich witness actionNode firstRoot outsideNode internalNode outcomeNode noise query)

/-!
# Actual compensated signal transport through forest re-entry

Reuse the three-value chain `A → R → E → B → Y`, with `E` outside the
forests and the genuine kept edge `B → Y`.  The ordinary root-only readout
would inject no old bit at `B` and would add `B` again at `Y`.  The compensated
plan instead retains `B`'s forest residual and leaves `Y`'s unchanged incoming
map to its own mechanism.  That prevents cancellation of the routed signal.

Besides full observational equality, positivity, and graph compatibility,
the regression checks actual interventional evaluation for every original
latent unit and every encoded fresh-bit family.  Its large outcome carries
the original two-root parity plus exactly the fresh noise parity.  The small
outcome carries the weighted defect plus that same noise parity, by the new
general conservation theorem.  No prior enumeration, guessed observational
table, binary-alphabet reduction, or zero-noise-only check is used.

These pointwise identities are not themselves a probability counterexample.
`HedgeCompensatedConservation` proves the corresponding general large-flow
identity; its companion regression also exercises a composite action and
nonbinary intervention labels.  `HedgeCompensatedCounterexample` then
integrates the actual fresh factors and proves separation of the original
query using the very same positive compensated model pair.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

noncomputable def plan := witness.carrierFlowReadoutPlan rich (fun _node => noise)
noncomputable def left := (witness.largeCarrierDefectParityModel rich).withHedgeReadouts rich plan
noncomputable def right := (witness.smallCarrierDefectParityModel rich).withHedgeReadouts rich plan

private theorem allowed : forall node, witness.rootReadoutNodes node = true ->
    witness.small node = true ∨ witness.large node = false := by decide +kernel

private theorem noise_positive : forall node, witness.smallOutcomeFlowNodes node = true ->
    forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit) := by
  intro _node _selected bit
  cases bit <;> decide +kernel

theorem observationally_equal : ObservationallyEquivalent left right :=
  witness.carrierDefectParityModels_carrierFlowReadoutPlan_observationally_equivalent rich (fun _node => noise) allowed

theorem left_positive : ObservationallyPositive left :=
  witness.largeCarrierDefectParityModel_carrierFlowReadoutPlan_positive rich (fun _node => noise) noise_positive

theorem right_positive : ObservationallyPositive right :=
  witness.smallCarrierDefectParityModel_carrierFlowReadoutPlan_positive rich (fun _node => noise) noise_positive

theorem left_compatible : Compatible left graph :=
  FiniteLatentSCM.withHedgeReadouts_compatible _ (witness.largeCarrierDefectParityModel_compatible rich) rich plan

theorem right_compatible : Compatible right graph :=
  FiniteLatentSCM.withHedgeReadouts_compatible _ (witness.smallCarrierDefectParityModel_compatible rich) rich plan

theorem plan_pivots : plan.map (fun step => step.pivot) = [firstRoot, outsideNode, internalNode, outcomeNode] :=
  by decide +kernel

/-- This internal non-root now injects its own original forest response,
which the root-only plan would discard. -/
theorem internal_retains_residual :
    (witness.carrierFlowReadoutStep rich (fun _node => noise) internalNode).injectOld = true ∧
      witness.roots internalNode = false := by decide +kernel

private def chain : ForestChild signature := fun parent => match parent.val with
  | 0 => some firstRoot
  | 1 => some outsideNode
  | 2 => some internalNode
  | 3 => some outcomeNode
  | _ => none

private theorem flow_successor : witness.largeOutcomeFlowSuccessor = chain := by
  funext parent
  have checked : forall node : Fin signature.count, witness.largeOutcomeFlowSuccessor node = chain node :=
    by decide +kernel
  exact checked parent

private theorem incoming_R (parents : signature.ParentValues firstRoot) :
    hedgeForestParentBitsFrom rich witness.largeOutcomeFlowSuccessor firstRoot parents =
      hedgeIsSecond rich actionNode (parents actionNode (by decide +kernel)) := by
  rw [flow_successor]
  change Bool.xor false (hedgeIsSecond rich actionNode (parents actionNode (by decide +kernel))) = _
  exact Bool.false_xor _

private theorem incoming_E (parents : signature.ParentValues outsideNode) :
    hedgeForestParentBitsFrom rich witness.largeOutcomeFlowSuccessor outsideNode parents =
      hedgeIsSecond rich firstRoot (parents firstRoot (by decide +kernel)) := by
  rw [flow_successor]
  change Bool.xor false (hedgeIsSecond rich firstRoot (parents firstRoot (by decide +kernel))) = _
  exact Bool.false_xor _

private theorem incoming_B (parents : signature.ParentValues internalNode) :
    hedgeForestParentBitsFrom rich witness.largeOutcomeFlowSuccessor internalNode parents =
      hedgeIsSecond rich outsideNode (parents outsideNode (by decide +kernel)) := by
  rw [flow_successor]
  change Bool.xor false (hedgeIsSecond rich outsideNode (parents outsideNode (by decide +kernel))) = _
  exact Bool.false_xor _

private theorem incoming_Y (parents : signature.ParentValues outcomeNode) :
    hedgeForestParentBitsFrom rich witness.largeOutcomeFlowSuccessor outcomeNode parents =
      hedgeIsSecond rich internalNode (parents internalNode (by decide +kernel)) := by
  rw [flow_successor]
  change Bool.xor false (hedgeIsSecond rich internalNode (parents internalNode (by decide +kernel))) = _
  exact Bool.false_xor _

private theorem old_incoming_R (parents : signature.ParentValues firstRoot) :
    hedgeForestParentBitsFrom rich witness.child firstRoot parents =
      hedgeIsSecond rich actionNode (parents actionNode (by decide +kernel)) :=
  (hedgeForestParentBitsFrom_congr_to_child rich firstRoot witness.child witness.largeOutcomeFlowSuccessor parents
    (by decide +kernel)).trans (incoming_R parents)

private theorem old_incoming_B (parents : signature.ParentValues internalNode) :
    hedgeForestParentBitsFrom rich witness.child internalNode parents = false :=
  (hedgeForestParentBitsFrom_congr_to_child rich internalNode witness.child (emptyChild signature) parents
    (by decide +kernel)).trans (hedgeForestParentBitsFrom_empty rich internalNode parents)

private theorem old_incoming_Y (parents : signature.ParentValues outcomeNode) :
    hedgeForestParentBitsFrom rich witness.child outcomeNode parents =
      hedgeIsSecond rich internalNode (parents internalNode (by decide +kernel)) :=
  (hedgeForestParentBitsFrom_congr_to_child rich outcomeNode witness.child witness.largeOutcomeFlowSuccessor parents
    (by decide +kernel)).trans (incoming_Y parents)

/-- At `Y` the old kept incoming map already is the desired flow map.
The readout adds no extra parent bit; its fresh noise is still present. -/
theorem outcome_does_not_double_count_parent (parents : signature.ParentValues outcomeNode) :
    (witness.carrierFlowReadoutStep rich (fun _node => noise) outcomeNode).parentSignal parents = false := by
  change Bool.xor (hedgeForestParentBitsFrom rich witness.child outcomeNode parents)
    (hedgeForestParentBitsFrom rich witness.largeOutcomeFlowSuccessor outcomeNode parents) = false
  rw [old_incoming_Y, incoming_Y, Bool.xor_self]

noncomputable def originalBits (unit : (witness.largeCarrierDefectParityModel rich).latent.Assignment)
    (node : Fin signature.count) : Bool :=
  hedgeIsSecond rich node ((witness.largeCarrierDefectParityModel rich).evalUnder (hedgeDoSecond rich query.action) unit node)

noncomputable def updatedBits (unit : (witness.largeCarrierDefectParityModel rich).latent.Assignment)
    (bits : Fin signature.count -> Bool) (node : Fin signature.count) : Bool :=
  hedgeIsSecond rich node (left.evalUnder (hedgeDoSecond rich query.action)
    ((witness.largeCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits plan unit) node)

noncomputable def residual (unit : (witness.largeCarrierDefectParityModel rich).latent.Assignment) :=
  hedgeCarrierResidualBit rich witness.child ((witness.largeCarrierDefectParityModel rich).eval unit)

private theorem action_fixed (model : ExactModel signature) (unit : model.latent.Assignment) :
    hedgeIsSecond rich actionNode (model.evalUnder (hedgeDoSecond rich query.action) unit actionNode) = true := by
  change hedgeIsSecond rich actionNode (model.evalNodeUnder (hedgeDoSecond rich query.action) unit actionNode) = true
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  rw [hedgeDoSecond_of_true rich query.action (by decide +kernel)]
  exact hedgeIsSecond_second rich actionNode

private theorem new_R (unit) (bits : Fin signature.count -> Bool) :
    updatedBits unit bits firstRoot = Bool.xor (Bool.xor (residual unit firstRoot) true) (bits firstRoot) := by
  have equation := witness.largeCarrierDefectParityModel_carrierFlowReadoutPlan_evalUnder_bit rich (fun _node => noise)
    bits unit (hedgeDoSecond rich query.action) firstRoot (by decide +kernel) (by decide +kernel)
  dsimp only at equation
  rw [incoming_R] at equation
  change updatedBits unit bits firstRoot = Bool.xor (Bool.xor (residual unit firstRoot)
    (updatedBits unit bits actionNode)) (bits firstRoot) at equation
  rw [show updatedBits unit bits actionNode = true from action_fixed left _] at equation
  exact equation

private theorem new_E (unit) (bits : Fin signature.count -> Bool) :
    updatedBits unit bits outsideNode = Bool.xor (updatedBits unit bits firstRoot) (bits outsideNode) := by
  have equation := witness.largeCarrierDefectParityModel_carrierFlowReadoutPlan_evalUnder_bit rich (fun _node => noise)
    bits unit (hedgeDoSecond rich query.action) outsideNode (by decide +kernel) (by decide +kernel)
  dsimp only at equation
  rw [incoming_E] at equation
  simpa only [show witness.large outsideNode = false from by decide +kernel,
    Bool.false_eq_true, if_false, Bool.false_xor] using equation

private theorem new_B (unit) (bits : Fin signature.count -> Bool) :
    updatedBits unit bits internalNode = Bool.xor
      (Bool.xor (residual unit internalNode) (updatedBits unit bits outsideNode)) (bits internalNode) := by
  have equation := witness.largeCarrierDefectParityModel_carrierFlowReadoutPlan_evalUnder_bit rich (fun _node => noise)
    bits unit (hedgeDoSecond rich query.action) internalNode (by decide +kernel) (by decide +kernel)
  dsimp only at equation
  rw [incoming_B] at equation
  exact equation

private theorem new_Y (unit) (bits : Fin signature.count -> Bool) :
    updatedBits unit bits outcomeNode = Bool.xor
      (Bool.xor (residual unit outcomeNode) (updatedBits unit bits internalNode)) (bits outcomeNode) := by
  have equation := witness.largeCarrierDefectParityModel_carrierFlowReadoutPlan_evalUnder_bit rich (fun _node => noise)
    bits unit (hedgeDoSecond rich query.action) outcomeNode (by decide +kernel) (by decide +kernel)
  dsimp only at equation
  rw [incoming_Y] at equation
  exact equation

private theorem old_R (unit) : originalBits unit firstRoot = Bool.xor (residual unit firstRoot) true := by
  have equation := witness.largeCarrierDefectParityModel_evalUnder_residual_bit rich unit
    (hedgeDoSecond rich query.action) firstRoot (by decide +kernel) (by decide +kernel)
  rw [old_incoming_R, action_fixed] at equation
  exact equation

private theorem old_B (unit) : originalBits unit internalNode = residual unit internalNode := by
  have equation := witness.largeCarrierDefectParityModel_evalUnder_residual_bit rich unit
    (hedgeDoSecond rich query.action) internalNode (by decide +kernel) (by decide +kernel)
  rw [old_incoming_B, Bool.xor_false] at equation
  exact equation

private theorem old_Y (unit) : originalBits unit outcomeNode =
    Bool.xor (residual unit outcomeNode) (residual unit internalNode) := by
  have equation := witness.largeCarrierDefectParityModel_evalUnder_residual_bit rich unit
    (hedgeDoSecond rich query.action) outcomeNode (by decide +kernel) (by decide +kernel)
  rw [old_incoming_Y] at equation
  change originalBits unit outcomeNode = Bool.xor (residual unit outcomeNode) (originalBits unit internalNode) at equation
  rw [old_B] at equation
  exact equation

/-- Every actual large-model execution carries the old common-root signal
to `Y`, with all four fresh factors explicitly retained.  This is not just
the zero-noise sweep or an assertion about one convenient latent witness. -/
theorem large_outcome_carries_root_signal (unit : (witness.largeCarrierDefectParityModel rich).latent.Assignment)
    (bits : Fin signature.count -> Bool) :
    updatedBits unit bits outcomeNode = Bool.xor
      (hedgeRootParityEvent rich witness.roots
        ((witness.largeCarrierDefectParityModel rich).evalUnder (hedgeDoSecond rich query.action) unit))
      (hedgeNodeXor witness.smallOutcomeFlowNodes bits) := by
  have rootsMembers : NodeSet.members witness.roots = [firstRoot, outcomeNode] := by decide +kernel
  have flowMembers : NodeSet.members witness.smallOutcomeFlowNodes =
      [firstRoot, outsideNode, internalNode, outcomeNode] := by decide +kernel
  simp only [hedgeRootParityEvent, hedgeNodeXor, rootsMembers, flowMembers,
    List.foldl_cons, List.foldl_nil, Bool.false_xor]
  change updatedBits unit bits outcomeNode = Bool.xor (Bool.xor (originalBits unit firstRoot) (originalBits unit outcomeNode)) _
  rw [new_Y, new_B, new_E, new_R, old_R, old_Y]
  have regroup (r b y nr ne nb ny : Bool) :
      Bool.xor (Bool.xor y (Bool.xor (Bool.xor b (Bool.xor (Bool.xor (Bool.xor r true) nr) ne)) nb)) ny =
        Bool.xor (Bool.xor (Bool.xor r true) (Bool.xor y b))
          (Bool.xor (Bool.xor (Bool.xor nr ne) nb) ny) := by
    cases r <;> cases b <;> cases y <;> cases nr <;> cases ne <;> cases nb <;> cases ny <;> rfl
  exact regroup _ _ _ _ _ _ _

/-- The nested outcome carries the weighted original defect and the very
same fresh parity.  The general conservation theorem includes the internal
kept child, rather than substituting observed coordinates independently. -/
theorem small_outcome_carries_defect (unit : (witness.smallCarrierDefectParityModel rich).latent.Assignment)
    (bits : Fin signature.count -> Bool) :
    hedgeIsSecond rich outcomeNode (right.evalUnder (hedgeDoSecond rich query.action)
      ((witness.smallCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits plan unit) outcomeNode) =
        Bool.xor (hedgeDefectBitOf graph unit) (hedgeNodeXor witness.smallOutcomeFlowNodes bits) := by
  have sinksMembers : NodeSet.members (keptSinks witness.rootReadoutNodes witness.rootReadoutSuccessor) = [outcomeNode] :=
    by decide +kernel
  simpa only [hedgeNodeXor, sinksMembers, List.foldl_cons, List.foldl_nil, Bool.false_xor] using
    witness.smallCarrierDefectParityModel_carrierFlowReadoutPlan_sinkParity_doSecond rich (fun _node => noise)
      allowed bits unit

end HedgeCompensatedReentry
end Examples
end Causality
end Thesis
