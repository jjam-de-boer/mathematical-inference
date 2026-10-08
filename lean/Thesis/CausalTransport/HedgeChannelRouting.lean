import Thesis.CausalTransport.HedgeChannelFullTerms
import Thesis.Probability.FiniteBooleanCharacter

namespace Thesis
namespace Causality
namespace HedgeChannelInstallation

open Probability

/-!
# Linear parent signals for the original hedge outcome flow

The installed channel pair permits arbitrary typed parent signals, but the
original-outcome separation argument needs a particular homogeneous linear
choice.  Each row reads precisely the incoming parents of a supplied
no-splitting successor map.  An edge guard keeps the definition genuinely
typed even before well-formedness is supplied.  Well-formedness then identifies
that local signal with the already proved abstract incoming-flow XOR.

For a hedge we use its existing composed small-forest/outcome flow, not a new
route or a readiness hypothesis.  Readout routes may leave and re-enter the
large or small forest.  The composed flow is action-avoiding, contains the
small forest, and has all its sinks in the original outcome set.

The distinguished outside-small background mask completes exactly that
flow.  Conservation identifies its combined small/background character with
sink parity.  On the original all-false outcome cylinder this character is
therefore positive everywhere.  The other background phases remain
homogeneous XOR-linear, so their complete false-cylinder character sums
are nonnegative by the separate finite probability theorem.

These are phase and support facts, not yet a replacement for actual
interventional term coefficients or a `PublishedCompleteness` inhabitant.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S} {q : JointKernelQuery S}

/-! ## Actual directed-parent signals and their abstract flow phase -/

/-- Incoming routed-parent XOR using only declared directed-parent values.
Invalid successor entries contribute zero; no unavailable parent is read. -/
def routingParentSignal (successor : ForestChild S) : ParentSignal S :=
  fun child parents => (List.finRange S.count).foldl (fun total parent =>
    Bool.xor total (if edge : S.directed parent child = true then
      if successor parent = some child then parents parent edge else false
    else false)) false

/-- On a well-formed successor map, the edge guard removes nothing that
the incoming-flow fold would retain.  The sample itself is not evaluated
through a substitute model: these are its actual typed parent values. -/
theorem routingParentSignal_eq_incoming (nodes : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool nodes successor = true)
    (sample : S.binary.Assignment) (child : Fin S.count) :
    routingParentSignal successor child (fun parent _edge => sample parent) =
      hedgeRoutingIncomingBits successor sample child := by
  unfold routingParentSignal hedgeRoutingIncomingBits hedgeRoutingParentEntry
  apply foldl_congr
  intro total parent
  by_cases selected : successor parent = some child
  · have edge := (childWellFormed_edge nodes successor wellFormed selected).2.2
    simp only [edge, selected, dite_true, if_true]
  · by_cases edge : S.directed parent child = true
    · simp only [edge, selected, dite_true, if_false]
    · rw [dif_neg edge]
      simp only [selected, if_false]

/-- A phase over any selected rows is the parity of their recovered local
flow sources.  The well-formed flow domain need not equal those selected rows. -/
theorem routingPhase_eq_localSource (domain nodes : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool domain successor = true) (sample : S.binary.Assignment) :
    signalPhase nodes (routingParentSignal successor) sample =
      hedgeNodeXor nodes (hedgeRoutingLocalSource successor sample) := by
  unfold signalPhase hedgeNodeXor hedgeRoutingLocalSource
  apply foldl_congr
  intro total child
  change Bool.xor total (Bool.xor (sample child)
    (routingParentSignal successor child (fun parent _edge => sample parent))) = _
  rw [routingParentSignal_eq_incoming domain successor wellFormed sample child]

private theorem incoming_zero (successor : ForestChild S) (child : Fin S.count) :
    hedgeRoutingIncomingBits successor (fun _ => false) child = false := by
  unfold hedgeRoutingIncomingBits hedgeRoutingParentEntry
  apply foldl_unchanged
  intro total parent
  simp only [ite_self, Bool.xor_false]

private theorem incoming_xor (successor : ForestChild S) (left right : S.binary.Assignment)
    (child : Fin S.count) :
    hedgeRoutingIncomingBits successor (FiniteProduct.xorAssignment S.count left right) child =
      Bool.xor (hedgeRoutingIncomingBits successor left child)
        (hedgeRoutingIncomingBits successor right child) := by
  unfold hedgeRoutingIncomingBits
  have entry : forall parent,
      hedgeRoutingParentEntry successor (FiniteProduct.xorAssignment S.count left right) child parent =
        Bool.xor (hedgeRoutingParentEntry successor left child parent)
          (hedgeRoutingParentEntry successor right child parent) := by
    intro parent
    by_cases selected : successor parent = some child <;>
      simp only [hedgeRoutingParentEntry, selected, if_true, if_false, FiniteProduct.xorAssignment,
        Bool.xor_self]
  exact (foldl_congr _ _ false (List.finRange S.count)
    (fun total parent => congrArg (Bool.xor total) (entry parent))).trans
    (foldl_xor_pointwise _ _ (List.finRange S.count))

/-- Homogeneity of the actual routed phase.  In particular there is no
constant odd offset hidden in the local parent signals. -/
theorem routingPhase_zero (domain nodes : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool domain successor = true) :
    signalPhase nodes (routingParentSignal successor) (fun _ => false) = false := by
  rw [routingPhase_eq_localSource domain nodes successor wellFormed]
  unfold hedgeNodeXor hedgeRoutingLocalSource
  apply foldl_unchanged
  intro total child
  change Bool.xor total (Bool.xor false
    (@hedgeRoutingIncomingBits S successor (fun _ => false) child)) = total
  rw [@incoming_zero S successor child, Bool.xor_self, Bool.xor_false]

/-- Additivity of the whole observed/parent phase, irrespective of the
chosen node set.  Only the successor map's well-formed domain is fixed. -/
theorem routingPhase_xor (domain nodes : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool domain successor = true)
    (left right : S.binary.Assignment) :
    signalPhase nodes (routingParentSignal successor) (FiniteProduct.xorAssignment S.count left right) =
      Bool.xor (signalPhase nodes (routingParentSignal successor) left)
        (signalPhase nodes (routingParentSignal successor) right) := by
  have localSum : forall child,
      Bool.xor ((FiniteProduct.xorAssignment S.count left right) child)
        (routingParentSignal successor child (fun parent _edge =>
          (FiniteProduct.xorAssignment S.count left right) parent)) =
      Bool.xor (Bool.xor (left child) (routingParentSignal successor child (fun parent _edge => left parent)))
        (Bool.xor (right child) (routingParentSignal successor child (fun parent _edge => right parent))) := by
    intro child
    rw [routingParentSignal_eq_incoming domain successor wellFormed,
      routingParentSignal_eq_incoming domain successor wellFormed,
      routingParentSignal_eq_incoming domain successor wellFormed, incoming_xor]
    simp only [FiniteProduct.xorAssignment]
    generalize left child = leftBit
    generalize right child = rightBit
    generalize hedgeRoutingIncomingBits successor left child = leftIncoming
    generalize hedgeRoutingIncomingBits successor right child = rightIncoming
    cases leftBit <;> cases rightBit <;> cases leftIncoming <;> cases rightIncoming <;> rfl
  exact (foldl_congr _ _ false (NodeSet.members nodes)
    (fun total child => congrArg (Bool.xor total) (localSum child))).trans
    (foldl_xor_pointwise _ _ (NodeSet.members nodes))

/-- The actual Boolean signature enumeration, filtered at a false-valued
coordinate cylinder, has a nonnegative complete routed-character sum.
This transfers the finite probability theorem through the signature's own
deduplicated enumeration instead of assuming that it is a raw product list. -/
theorem routingPhase_characterSum_nonneg (domain nodes : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool domain successor = true) (fixed : NodeSet S) :
    0 <= ((S.binary.assignmentEnumeration.filter (FiniteProduct.falseCylinder S.count fixed)).map
      (fun sample => FiniteProbRecord.characterSign (signalPhase nodes (routingParentSignal successor) sample))).sum := by
  letI : DecidableEq (Fin S.count -> Bool) :=
    FiniteProduct.assignmentDecidableEq S.count (fun _ => Bool) (fun _ => inferInstance)
  have fullPermutation :
      (FiniteProduct.enumeration S.count (fun _ => Bool) (fun _ => [false, true])).Perm
        S.binary.assignmentEnumeration := by
    apply ConstructivePermutation.perm_of_nodup_mem_iff _ _
      (FiniteProduct.enumeration_nodup S.count (fun _ => Bool) (fun _ => [false, true])
        (fun _ => inferInstance) (fun _ => by change ([false, true] : List Bool).Nodup; decide))
      S.binary.assignmentEnumeration_nodup
    intro sample
    exact ⟨fun _listed => S.binary.assignmentEnumeration_complete sample,
      fun _listed => FiniteProduct.enumeration_complete S.count (fun _ => Bool) (fun _ => [false, true])
        (fun _ bit => by cases bit <;> simp) sample⟩
  have same := FiniteSupportedSum.sum_eq_of_perm
    ((fullPermutation.filter (FiniteProduct.falseCylinder S.count fixed)).map
      (fun sample => FiniteProbRecord.characterSign (signalPhase nodes (routingParentSignal successor) sample)))
  rw [← same]
  exact FiniteProduct.filtered_falseCylinder_characterSum_nonneg S.count fixed
    (signalPhase nodes (routingParentSignal successor)) (routingPhase_zero domain nodes successor wellFormed)
    (routingPhase_xor domain nodes successor wellFormed)

/-- Every permitted outside-small background has a nonnegative complete
combined small/background character sum on the original action/outcome
false cylinder.  The two row sets are disjoint, so their XOR phase is the
single routed phase of their actual union.  No distinguished-mask hypothesis
is used for these other terms. -/
theorem smallBackground_characterSum_nonneg (w : HedgeWitness G q) (mask : NodeSet S)
    (subset : NodeSet.Subset mask (outside w.small)) :
    0 <= ((S.binary.assignmentEnumeration.filter
      (FiniteProduct.falseCylinder S.count (NodeSet.union q.action q.outcome))).map
      (fun sample => FiniteProbRecord.characterSign
        (Bool.xor (signalPhase w.small (routingParentSignal w.smallOutcomeFlowSuccessor) sample)
          (signalPhase mask (routingParentSignal w.smallOutcomeFlowSuccessor) sample)))).sum := by
  have disjoint : NodeSet.Disjoint w.small mask := by
    intro child inside
    cases selected : mask child with
    | false => rfl
    | true =>
        have outsideSmall : Bool.not (w.small child) = true := by
          simpa only [outside, NodeSet.diff, NodeSet.full, Bool.true_and] using subset child selected
        rw [inside] at outsideSmall
        cases outsideSmall
  have phases := List.map_congr_left
    (l := S.binary.assignmentEnumeration.filter
      (FiniteProduct.falseCylinder S.count (NodeSet.union q.action q.outcome)))
    (fun sample _listed => congrArg FiniteProbRecord.characterSign
      (signalPhase_union_of_disjoint w.small mask disjoint
        (routingParentSignal w.smallOutcomeFlowSuccessor) sample).symm)
  have nonnegative := routingPhase_characterSum_nonneg w.smallOutcomeFlowNodes (NodeSet.union w.small mask)
    w.smallOutcomeFlowSuccessor w.smallOutcomeFlowSuccessor_wellFormed (NodeSet.union q.action q.outcome)
  exact (congrArg List.sum phases).symm ▸ nonnegative

/-! ## The distinguished mask of the existing original-outcome flow -/

/-- Background rows completing the small forest to its existing composed
outcome flow.  None of these rows is in the small forest or original action. -/
def outcomeFlowBackground (w : HedgeWitness G q) : NodeSet S :=
  NodeSet.diff w.smallOutcomeFlowNodes w.small

/-- Every small-forest row is retained in the composed outcome flow,
even when a readout successor takes priority over its old forest successor. -/
theorem outcomeFlow_small_subset (w : HedgeWitness G q) :
    NodeSet.Subset w.small w.smallOutcomeFlowNodes := by
  intro child selected
  simp only [HedgeWitness.smallOutcomeFlowNodes, NodeSet.union, selected, Bool.or_true]

/-- Both constituents of the composed flow avoid the full original action,
not merely the stored action seed.  Their union inherits that avoidance. -/
theorem outcomeFlow_avoids_action (w : HedgeWitness G q) (child : Fin S.count)
    (selected : w.smallOutcomeFlowNodes child = true) : q.action child = false := by
  cases inReadout : w.rootReadoutNodes child with
  | true => exact w.rootReadoutNodes_avoids_action child inReadout
  | false =>
      have inSmall : w.small child = true := by
        simpa only [HedgeWitness.smallOutcomeFlowNodes, NodeSet.union, inReadout, Bool.false_or] using selected
      exact w.small_avoids_intervention child inSmall

/-- The distinguished background is a legal outside-small mask in the
installed model's complete canonical enumeration. -/
theorem outcomeFlowBackground_subset_outside (w : HedgeWitness G q) :
    NodeSet.Subset (outcomeFlowBackground w) (outside w.small) := by
  intro child selected
  exact Bool.and_eq_true_iff.mpr ⟨rfl, (Bool.and_eq_true_iff.mp selected).2⟩

/-- No distinguished background row is removed by the original action cut.
This is separate from its outside-small support condition. -/
theorem outcomeFlowBackground_avoids_action (w : HedgeWitness G q) (child : Fin S.count)
    (selected : outcomeFlowBackground w child = true) : q.action child = false :=
  outcomeFlow_avoids_action w child ((Bool.and_eq_true_iff.mp selected).1)

/-- Small rows and the distinguished backgrounds complete exactly the
existing outcome flow; no extra queried or routed coordinate is introduced. -/
theorem outcomeFlowBackground_reconstructs (w : HedgeWitness G q) :
    NodeSet.union w.small (outcomeFlowBackground w) = w.smallOutcomeFlowNodes :=
  NodeSet.union_diff_eq (outcomeFlow_small_subset w)

/-- Conservation turns the distinguished full-small/background phase into
the parity of the composed flow's actual original-outcome sinks. -/
theorem outcomeFlow_phase_eq_sinkParity (w : HedgeWitness G q) (sample : S.binary.Assignment) :
    Bool.xor (signalPhase w.small (routingParentSignal w.smallOutcomeFlowSuccessor) sample)
      (signalPhase (outcomeFlowBackground w) (routingParentSignal w.smallOutcomeFlowSuccessor) sample) =
      hedgeNodeXor (keptSinks w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor) sample := by
  rw [← signalPhase_union_of_disjoint w.small (outcomeFlowBackground w)
    (NodeSet.disjoint_diff w.smallOutcomeFlowNodes w.small), outcomeFlowBackground_reconstructs,
    routingPhase_eq_localSource w.smallOutcomeFlowNodes w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor
      w.smallOutcomeFlowSuccessor_wellFormed]
  exact (hedgeRoutingFlow_conservation_localSource w.smallOutcomeFlowNodes
    w.smallOutcomeFlowSuccessor w.smallOutcomeFlowSuccessor_wellFormed sample).symm

/-- The original all-false outcome event makes the distinguished phase
even.  No action seed, unqueried vertex or enlarged outcome is added to that
event; action consistency is a separate actual likelihood coefficient. -/
theorem outcomeFlow_phase_false_of_outcome (w : HedgeWitness G q) (sample : S.binary.Assignment)
    (selected : FiniteProduct.falseCylinder S.count q.outcome sample = true) :
    Bool.xor (signalPhase w.small (routingParentSignal w.smallOutcomeFlowSuccessor) sample)
      (signalPhase (outcomeFlowBackground w) (routingParentSignal w.smallOutcomeFlowSuccessor) sample) = false := by
  rw [outcomeFlow_phase_eq_sinkParity]
  unfold hedgeNodeXor
  have equal :
      (NodeSet.members (keptSinks w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor)).foldl
        (fun total child => Bool.xor total (sample child)) false =
      (NodeSet.members (keptSinks w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor)).foldl
        (fun total _child => total) false := by
    apply foldl_congr_of_mem
    intro total child member
    have sink := (NodeSet.mem_members_iff _ child).mp member
    have outcome := w.smallOutcomeFlowSinks_subset_outcome child sink
    rw [(FiniteProduct.falseCylinder_eq_true_iff S.count q.outcome sample).mp selected child outcome,
      Bool.xor_false]
  exact equal.trans (foldl_unchanged _ false _ (fun _ _ => rfl))

end HedgeChannelInstallation
end Causality
end Thesis
