import Thesis.CausalTransport.ConditionalFailureSmallInteraction
import Thesis.Examples.ConditionalCutActivationForest

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalCutActivationRoute

open PathSpecification Probability FiniteBooleanInteraction HedgeChannelEnvironmentInstallation

/-!
# Actual trace pruning and parity at a genuinely nonlatest pivot

The original pivot `P` reaches a later conditioner in the larger graph, and
the old universal bar forest is impossible there.  Nonetheless its actual
cut policy supplies complete collider traces to the same general selection
and installation theorems.  No latest certificate, replacement query or
independent parity flag is passed.

The generous domain includes the fork `U`, but the actual collider trace
union contains only `C,Z`.  The installed interaction therefore omits `U`.
Its direction bit and own row phase are genuinely nonzero, so a later proof
must handle that contact if `U` belongs to mandatory Small.  Pruning is not
permission to assume every omitted coordinate is zero.

Full original-input cube conservation and the entire original evidence
cylinder retain the actual outcome character.  These are graph/signal
regressions for an identifiable query, not conditional countermodels.  The
independent zero-edge fixture additionally retains its conditioned sink on
the full cube, before that bit vanishes on the actual evidence cylinder.
-/

/-- Only membership in the unchanged original condition set is supplied.
`pivot_not_latest` proves no original-graph latest certificate exists here. -/
def retainedPivot : RetainedConditionalPivot query where
  node := pivotNode
  selected := by decide +kernel

/-- Select actual collider traces, not the entire auxiliary domain. -/
def traces : NodeSet signature := normal.activationTraceNodes retainedPivot cutForest

/-- Restrict the one shared map to the successor-closed actual trace union. -/
def traceSuccessor : ForestChild signature := normal.activationTraceSuccessor retainedPivot cutForest

/-- One occurrence of every actual path head or activation row. -/
def interactionRows : NodeSet signature := normal.activationInteractionRows retainedPivot cutForest

/-- The general fused installation retains original reserved-root inputs. -/
def interactionSignal : LinearSignal graph := normal.activationInteractionSignal retainedPivot cutForest

theorem actual_trace_mask : traces = NodeSet.union (NodeSet.singleton collider) (NodeSet.singleton evidence) := by
  funext node
  decide +kernel +revert

/-- The irrelevant domain ancestor really is pruned, while both vertices
of the complete actual collider trace remain selected. -/
theorem irrelevant_fork_pruned : cutForest.nodes parent = true ∧ traces parent = false ∧ interactionRows parent = false := by
  decide +kernel

/-- The actual fork coordinate is true in the supported path direction.
It is not an activation contact, and is not silently fixed to false. -/
theorem omitted_fork_direction_nonzero : cubeSample graph normal.pathDirection parent = true := by
  rw [ConditionalBackdoorPathNormalForm.pathDirection, LinearSignal.activePathDirection_sample, normal_window]
  rfl

/-- An omitted row keeps its real own bit, which is odd here.  This is a
regression against treating uncovered Small forks as zero-tail routing. -/
theorem omitted_fork_row_odd : (interactionSignal.rowPhase parent).value normal.pathDirection = true := by
  rw [interactionSignal, normal.activationInteraction_rowPhase_outside retainedPivot cutForest parent irrelevant_fork_pruned.2.2]
  exact omitted_fork_direction_nonzero

/-- Whole original conditioning-cylinder matching follows from the same
general conservation proof at this nonlatest pivot.  No evidence assignment
is picked and no likelihood table is exhaustively enumerated. -/
theorem original_conditional_character (point : Cube graph)
    (listed : point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + signature.count)
      (cubeMask graph (NodeSet.union query.action query.condition))) :
    (interactionSignal.forestPhase interactionRows).value point = (maskPhase _ (cubeMask graph query.outcome)).value point := by
  rw [interactionSignal, interactionRows, normal.activationInteraction_conditionalPhase retainedPivot cutForest point listed]
  have same := (NodeSet.singleton_eq_true_iff outcome normal.outcome).mp normal.outcome_selected
  rw [same]
  rfl

/-- The retained pivot is the unique odd selected row, although an omitted
fork row can also be odd outside the selected interaction. -/
theorem actual_selected_parities : interactionRows pivotNode = true ∧
    (interactionSignal.rowPhase pivotNode).value normal.pathDirection = true ∧
    (forall child, interactionRows child = true -> child ≠ pivotNode ->
      (interactionSignal.rowPhase child).value normal.pathDirection = false) :=
  ⟨(normal.activationInteraction_source_odd retainedPivot cutForest).1,
    (normal.activationInteraction_source_odd retainedPivot cutForest).2,
    normal.activationInteraction_selected_even retainedPivot cutForest⟩

theorem actual_union_odd : (interactionSignal.forestPhase interactionRows).value normal.pathDirection = true :=
  normal.activationInteraction_forest_odd retainedPivot cutForest

end CurrentConditionalCutActivationRoute

namespace CurrentConditionalCutActivationRouteZero

open PathSpecification Probability FiniteBooleanInteraction HedgeChannelEnvironmentInstallation
open CurrentConditionalFailureActivationAvoidanceZero

abbrev retainedPivot : RetainedConditionalPivot query := pivot.toRetained
def traces : NodeSet signature := normal.activationTraceNodes retainedPivot cutForest
def traceSuccessor : ForestChild signature := normal.activationTraceSuccessor retainedPivot cutForest
def interactionRows : NodeSet signature := normal.activationInteractionRows retainedPivot cutForest
def interactionSignal : LinearSignal graph := normal.activationInteractionSignal retainedPivot cutForest

/-- A conditioned source contributes its singleton trace with no invented
outgoing continuation.  Its own bit remains in full-cube conservation. -/
theorem actual_zero_edge_trace : traces = NodeSet.singleton collider ∧ traceSuccessor = (fun _ => none) := by
  have seedMask : normal.colliderSeeds = NodeSet.singleton collider := by
    unfold ConditionalBackdoorPathNormalForm.colliderSeeds
    rw [normal_window]
    funext node
    decide +kernel +revert
  have selectedMask : traces = NodeSet.singleton collider := by
    funext node
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro selected
      have inside := normal.activationTraceNodes_subset_forest retainedPivot cutForest node selected
      have onPath : .observed node ∈ normal.cutPath.nodes := by
        rw [normal_window]
        exact (by decide +kernel : forall child, cutForest.nodes child = true ->
          (SeparationNode.observed child : SeparationNode signature) ∈
            [.observed pivotNode, .observed parent, .observed collider, .observed outcome]) node inside
      have seed := (normal.activationTraceNodes_intersection_iff_collider retainedPivot cutForest node onPath).mp selected
      rw [seedMask] at seed
      exact seed
    · intro selected
      apply normal.colliderSeeds_subset_activationTraceNodes retainedPivot cutForest node
      rw [seedMask]
      exact selected
  refine ⟨selectedMask, ?_⟩
  change restrictChild traces cutForest.successor = (fun _ => none)
  rw [selectedMask]
  funext node
  decide +kernel +revert

/-- The full-cube phase retains the real conditioned-collider sink bit.
It vanishes only after restricting to the unchanged query's evidence. -/
theorem original_full_cube_character (point : Cube graph) :
    (interactionSignal.forestPhase interactionRows).value point =
      Bool.xor (cubeSample graph point pivotNode)
        (Bool.xor (cubeSample graph point normal.outcome) (cubeSample graph point collider)) := by
  have sinks : keptSinks traces traceSuccessor = NodeSet.singleton collider := by
    rw [actual_zero_edge_trace.1, actual_zero_edge_trace.2]
    funext node
    unfold keptSinks
    cases NodeSet.singleton collider node <;> rfl
  rw [interactionSignal, interactionRows, normal.activationInteraction_forestPhase retainedPivot cutForest]
  change Bool.xor _ (Bool.xor _ (hedgeNodeXor (keptSinks traces traceSuccessor) (cubeSample graph point))) = _
  rw [sinks, nodeXor_singleton]
  rfl

end CurrentConditionalCutActivationRouteZero
end Examples
end Causality
end Thesis
