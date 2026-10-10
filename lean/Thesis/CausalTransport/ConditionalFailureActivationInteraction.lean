import Thesis.CausalTransport.ConditionalFailureActivationSelection
import Thesis.CausalTransport.ConditionalFailurePathDirection
import Thesis.CausalTransport.HedgeChannelPathBoundary
import Thesis.CausalTransport.HedgeChannelEnvironmentFusion

namespace Thesis
namespace Causality

open PathSpecification Probability FiniteBooleanInteraction HedgeChannelEnvironmentInstallation

/-!
# Install the actual normalized path and merged collider activation traces

The path-head signal and the restricted common-policy activation forest are
real executable graph data.  Their union uses one installed mechanism per
observed row, with original pair-root reads only at path heads.  Incoming
parent masks are fused by XOR; overlapping collider rows keep their own bit
once.  Branches may merge under the already proved common successor policy.

The actual trace/path intersection is exactly the actual collider mask.
Whole-cube conservation therefore cancels that mask against the fusion's
own-bit correction, leaving the endpoint bits XOR the real activation sinks.
Those sinks are conditioned, so the complete original conditioning cylinder
leaves precisely the selected outcome character.  Already-conditioned
zero-edge activations are included: their sink bit is retained on the full
cube and vanishes only on that real evidence cylinder.

The proved path direction is zero at every trace vertex.  Fused path-row
parities are consequently preserved and activation-only rows are even.
This constructs the combined conserved interaction, not a mandatory Small
forest or a universal conditional countermodel.  All-Small routing and any
Small-to-pivot oddness transfer remain separate obligations.
-/

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
  {source : Fin S.count}

namespace ConditionalBackdoorPathNormalForm

/-- Select precisely the actual incoming heads of this normalized cut path.
Observed forks and outgoing endpoints are not added just for being on it. -/
def pathHeads {node : Fin S.count} (normal : ConditionalBackdoorPathNormalForm graph query node) : NodeSet S :=
  ActivePathInput.headRows graph (GraphMutilation.barUnderline query.action (NodeSet.singleton node)) normal.cutPath.nodes

variable (pivot : LatestConditionalPivot graph query source)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (forest : ConditionalColliderActivationForest query pivot.node)

/-- The real union of path heads and complete retained activation traces.
A shared collider or merged trace vertex has one Boolean membership entry. -/
def activationInteractionRows : NodeSet S := NodeSet.union normal.pathHeads (normal.activationTraceNodes pivot forest)

/-- Install one common local signal on that union.  Fusion adds actual
activation-parent reads, retains original path-root reads only at actual
heads, and never duplicates a mechanism's own observed bit. -/
def activationInteractionSignal : LinearSignal graph :=
  (LinearSignal.ofActivePath normal.cutPath).absorbSuccessor normal.pathHeads (normal.activationTraceSuccessor pivot forest)

/-- An actual internal collider is a path head: its first kept incoming
arrow and displayed consecutive window already select its row. -/
theorem colliderSeeds_subset_pathHeads : NodeSet.Subset normal.colliderSeeds normal.pathHeads := by
  intro child selected
  rcases (normal.colliderSeeds_eq_true_iff child).mp selected with ⟨before, after, previous, next, window, actual⟩
  apply ActivePathInput.incomingEdge_head
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, actual.1⟩
  exact (ActivePathInput.stepOnPath_internal_window normal.cutPath.simple before after previous (.observed child) next previous window).mpr
    (Or.inl rfl)

/-- The intersection is exactly the common executable collider classifier,
not a proposed overlap partition or all auxiliary activation ancestors. -/
theorem pathHeads_activationTrace_inter :
    NodeSet.inter normal.pathHeads (normal.activationTraceNodes pivot forest) = normal.colliderSeeds := by
  funext child
  apply Bool.eq_iff_iff.mpr
  rw [NodeSet.inter, Bool.and_eq_true_iff]
  constructor
  · intro both
    have onPath := ActivePathInput.headRows_member both.1
    exact (normal.activationTraceNodes_intersection_iff_collider pivot forest child onPath).mp both.2
  · intro collider
    exact ⟨normal.colliderSeeds_subset_pathHeads pivot child collider,
      normal.colliderSeeds_subset_activationTraceNodes pivot forest child collider⟩

/-- Every installed interaction row avoids the original action set.  Path
heads inherit the incoming cut, and real traces inherit policy action freedom. -/
theorem activationInteractionRows_action_free (child : Fin S.count)
    (selected : normal.activationInteractionRows pivot forest child = true) : query.action child = false := by
  rcases Bool.or_eq_true_iff.mp selected with pathHead | trace
  · exact ActivePathInput.headRows_not_cut pathHead
  · exact normal.activationTraceNodes_action_free pivot forest child trace

/-- Every real activation trace vertex is zero in the constructed path
direction.  A true direction bit would be a path noncollider, contradicting
the proved actual trace/path intersection.  Off-path coordinates are already
zero by construction, so omitted nonzero forks cannot be activation contacts. -/
theorem activationTrace_direction_zero (child : Fin S.count)
    (selected : normal.activationTraceNodes pivot forest child = true) : cubeSample graph normal.pathDirection child = false := by
  rw [pathDirection, LinearSignal.activePathDirection_sample]
  apply Bool.eq_false_iff.mpr
  intro positive
  have entries := (ActivePathInput.nonColliderBits_eq_true_iff graph _ normal.cutPath.nodes pivot.node child).mp positive
  have collider := (normal.activationTraceNodes_intersection_iff_collider pivot forest child entries.1).mp selected
  exact Bool.false_ne_true (entries.2.2.symm.trans collider)

/-- Actual retained activation sinks are conditioned in the original
query.  This includes an already-conditioned collider's zero-edge trace. -/
theorem activationTrace_sinks_conditioned :
    NodeSet.Subset (keptSinks (normal.activationTraceNodes pivot forest) (normal.activationTraceSuccessor pivot forest)) query.condition := by
  intro child sink
  have entries := (keptSinks_iff _ _ child).mp sink
  exact (normal.activationTraceSuccessor_sink_iff_condition pivot forest child entries.1).mp entries.2

private theorem pathPhase_endpoint_collider (point : Cube graph) :
    ((LinearSignal.ofActivePath normal.cutPath).forestPhase normal.pathHeads).value point =
      Bool.xor (cubeSample graph point pivot.node)
        (Bool.xor (cubeSample graph point normal.outcome) (hedgeNodeXor normal.colliderSeeds (cubeSample graph point))) := by
  have distinct : pivot.node ≠ normal.outcome := by
    intro equal
    have free := query.outcome_condition_disjoint normal.outcome normal.outcome_selected
    exact Bool.false_ne_true (free.symm.trans (equal ▸ pivot.selected))
  rw [pathHeads, LinearSignal.ofActivePath_forestPhase_endpointCollider normal.cutPath distinct, cubeMaskPhase_value]
  change hedgeNodeXor
    (fun child => Bool.xor (NodeSet.singleton pivot.node child)
      (Bool.xor (NodeSet.singleton normal.outcome child) (normal.colliderSeeds child))) (cubeSample graph point) = _
  rw [nodeXor_xor_masks, nodeXor_xor_masks, nodeXor_singleton, nodeXor_singleton]

/-- Full-cube conservation of the actual fused union, including all
original reserved coordinates and deduplicated merged activation rows.
Only real evidence-sink terms remain in addition to the two endpoint bits. -/
theorem activationInteraction_forestPhase (point : Cube graph) :
    ((normal.activationInteractionSignal pivot forest).forestPhase (normal.activationInteractionRows pivot forest)).value point =
      Bool.xor (cubeSample graph point pivot.node)
        (Bool.xor (cubeSample graph point normal.outcome)
          (hedgeNodeXor (keptSinks (normal.activationTraceNodes pivot forest) (normal.activationTraceSuccessor pivot forest))
            (cubeSample graph point))) := by
  rw [activationInteractionSignal, activationInteractionRows,
    LinearSignal.absorbSuccessor_forestPhase_with_overlap _ _ _ _ (normal.activationTraceSuccessor_wellFormed pivot forest),
    LinearSignal.ofSuccessor_forestPhase _ _ (normal.activationTraceSuccessor_wellFormed pivot forest),
    normal.pathHeads_activationTrace_inter pivot forest, normal.pathPhase_endpoint_collider pivot]
  have cancel (left right collider sinks : Bool) :
      Bool.xor (Bool.xor left (Bool.xor right collider)) (Bool.xor sinks collider) =
        Bool.xor left (Bool.xor right sinks) := by
    cases left <;> cases right <;> cases collider <;> cases sinks <;> rfl
  exact cancel _ _ _ _

/-- On the complete original conditioning cylinder the conserved union
is exactly the selected outcome character.  The pivot and actual sink
bits vanish by real evidence membership, not by selecting one environment
assignment or assuming matched conditional denominators. -/
theorem activationInteraction_conditionalPhase (point : Cube graph)
    (listed : point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count)
      (cubeMask graph (NodeSet.union query.action query.condition))) :
    ((normal.activationInteractionSignal pivot forest).forestPhase (normal.activationInteractionRows pivot forest)).value point =
      (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value point := by
  rw [normal.activationInteraction_forestPhase pivot forest, cubeMaskPhase_value, nodeXor_singleton]
  have pivotZero := cubeSample_false_of_mem graph (NodeSet.union query.action query.condition) point listed pivot.node
    (NodeSet.subset_union_right _ _ pivot.node pivot.selected)
  have sinkZero : hedgeNodeXor (keptSinks (normal.activationTraceNodes pivot forest) (normal.activationTraceSuccessor pivot forest))
      (cubeSample graph point) = false := by
    apply nodeXor_of_zero
    intro child sink
    exact cubeSample_false_of_mem graph (NodeSet.union query.action query.condition) point listed child
      (NodeSet.subset_union_right _ _ child (normal.activationTrace_sinks_conditioned pivot forest child sink))
  rw [pivotZero, sinkZero, Bool.xor_false, Bool.false_xor]

/-- The conserved singleton character is among the unchanged query's
actual outcome submasks.  Other outcomes are neither removed from the
query nor silently conditioned; the later covariance expansion retains them. -/
theorem activationInteraction_outcome_mask_member :
    cubeMask graph (NodeSet.singleton normal.outcome) ∈
      outcomeMasks (pairRootCount graph.binary + S.count) (cubeMask graph query.outcome) := by
  apply cubeMask_member_outcomeMasks
  intro child selected
  have same := (NodeSet.singleton_eq_true_iff normal.outcome child).mp selected
  exact same ▸ normal.outcome_selected

/-- The real outcome character is odd on the already proved supported
direction.  This follows from its actual endpoint bit, not from choosing
one favorable environment assignment or a supplied oddness certificate. -/
theorem activationInteraction_outcome_odd :
    (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value normal.pathDirection = true := by
  rw [cubeMaskPhase_value, nodeXor_singleton]
  exact normal.pathDirection_outcome_bit pivot.selected

/-- The entire deduplicated path/activation union is odd on the original
conditioning support.  This is a theorem of its complete conserved phase;
it is not oddness of a possibly different mandatory Small forest. -/
theorem activationInteraction_forest_odd :
    ((normal.activationInteractionSignal pivot forest).forestPhase (normal.activationInteractionRows pivot forest)).value
      normal.pathDirection = true := by
  rw [normal.activationInteraction_conditionalPhase pivot forest normal.pathDirection normal.pathDirection_member]
  exact normal.activationInteraction_outcome_odd pivot

/-- Fusion preserves each actual path-head parity in the supported
direction.  All activation-domain coordinates are proved zero above;
no stopped-at-path or extra row-evenness premise is supplied. -/
theorem activationInteraction_path_row (child : Fin S.count) (selected : normal.pathHeads child = true) :
    ((normal.activationInteractionSignal pivot forest).rowPhase child).value normal.pathDirection =
      ((LinearSignal.ofActivePath normal.cutPath).rowPhase child).value normal.pathDirection :=
  LinearSignal.absorbSuccessor_rowPhase_inside_of_domain_zero _ _ _ _ (normal.activationTraceSuccessor_wellFormed pivot forest)
    normal.pathDirection (normal.activationTrace_direction_zero pivot forest) child selected

/-- The actual combined signal's pivot row remains selected and odd.
This may still be outside the mandatory Small forest, so it is not itself
a Small-phase oddness theorem. -/
theorem activationInteraction_source_odd : normal.activationInteractionRows pivot forest pivot.node = true ∧
    ((normal.activationInteractionSignal pivot forest).rowPhase pivot.node).value normal.pathDirection = true := by
  have pathOdd := normal.pathDirection_source_odd pivot.selected
  refine ⟨NodeSet.subset_union_left _ _ pivot.node pathOdd.1, ?_⟩
  rw [normal.activationInteraction_path_row pivot forest pivot.node pathOdd.1]
  exact pathOdd.2

/-- Every other actually selected union row is even, including activation
merges and overlap colliders.  Omitted path forks remain outside the union;
their nonzero own bits are not incorrectly required to be even. -/
theorem activationInteraction_selected_even (child : Fin S.count)
    (selected : normal.activationInteractionRows pivot forest child = true) (different : child ≠ pivot.node) :
    ((normal.activationInteractionSignal pivot forest).rowPhase child).value normal.pathDirection = false := by
  cases pathHead : normal.pathHeads child with
  | true =>
      rw [normal.activationInteraction_path_row pivot forest child pathHead]
      exact normal.pathDirection_selected_even pivot.selected child pathHead different
  | false =>
      have trace : normal.activationTraceNodes pivot forest child = true := by
        simpa only [activationInteractionRows, NodeSet.union, pathHead, Bool.false_or] using selected
      exact LinearSignal.absorbSuccessor_rowPhase_new_of_domain_zero _ _ _ _ (normal.activationTraceSuccessor_wellFormed pivot forest)
        normal.pathDirection (normal.activationTrace_direction_zero pivot forest) child pathHead trace

end ConditionalBackdoorPathNormalForm

end Causality
end Thesis
