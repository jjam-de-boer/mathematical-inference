import Thesis.CausalTransport.ConditionalFailureActivationInteraction
import Thesis.Examples.ConditionalFailureActivationSelection
import Thesis.Examples.ConditionalFailureActivationAvoidanceZero

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureActivationInteraction

open Probability PathSpecification FiniteBooleanInteraction HedgeChannelEnvironmentInstallation

/-!+# Actual normalized path/activation installations on original query support

The genuine five-vertex numerator hedge supplies the opaque result of the
general normal-form constructor.  The tests below apply the new interaction
theorems to that result structurally: they do not replace it with the displayed
hand-written path or evaluate its exhaustive search.  Its complete original
conditioning cylinder gives the unchanged queried outcome character, and its
actual direction retains only the pivot's odd selected row.  The trace union
still lies inside Small, so it must not be installed a second time as background.

The independent four-vertex fixture has an already-conditioned collider.
Its actual trace selection is the singleton collider with no outgoing edge.
Full-cube conservation retains this sink bit; only the real evidence cylinder
removes it.  The shared collider row keeps one own bit, even though the two
separate phase sums would each include that bit.

These tests do not construct a universal terminal countermodel.  The first
fixture has a genuine joint hedge; the action-free second one is identifiable
and checks the graph/signal bridge only.  Mandatory-Small coverage and any
Small-to-pivot oddness transfer are not inferred from these interaction tests.
-/

namespace SmallOverlap

open CurrentConditionalFailureActivationSelection

/-- Actual union from the opaque certified normal form, not the displayed path. -/
def rows : NodeSet signature := normal.activationInteractionRows pivot forest
/-- The one fused signal installed on every selected union row. -/
def installed : LinearSignal graph := normal.activationInteractionSignal pivot forest

/-- The actual constructed normal form, with all original input coordinates,
has the original singleton outcome character on the complete query support. -/
theorem original_conditional_character (point : Cube graph)
    (listed : point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + signature.count)
      (cubeMask graph (NodeSet.union query.action query.condition))) :
    (installed.forestPhase rows).value point = (maskPhase _ (cubeMask graph query.outcome)).value point := by
  rw [installed, rows, normal.activationInteraction_conditionalPhase pivot forest point listed]
  have same := (NodeSet.singleton_eq_true_iff outcome normal.outcome).mp normal.outcome_selected
  rw [same]
  rfl

/-- Only the genuine latest pivot is odd among the deduplicated installed
rows.  Neither a row partition nor its parity is supplied as a premise. -/
theorem actual_selected_parities : rows pivot.node = true ∧
    (installed.rowPhase pivot.node).value normal.pathDirection = true ∧
    (forall child, rows child = true -> child ≠ pivot.node ->
      (installed.rowPhase child).value normal.pathDirection = false) :=
  ⟨(normal.activationInteraction_source_odd pivot forest).1,
    (normal.activationInteraction_source_odd pivot forest).2,
    normal.activationInteraction_selected_even pivot forest⟩

/-- Complete supported union oddness follows from the general conserved
phase, not enumeration of this graph's likelihood or private environment. -/
theorem actual_union_odd : (installed.forestPhase rows).value normal.pathDirection = true :=
  normal.activationInteraction_forest_odd pivot forest

/-- The real trace overlap remains mandatory Small.  Fusion installs it
once in the union, rather than assuming Small and activation are disjoint. -/
theorem inside_small_traces_retained : NodeSet.Subset traces witness.small ∧ NodeSet.Subset traces rows :=
  ⟨normal_trace_union_inside_small, NodeSet.subset_union_right _ _⟩

end SmallOverlap

namespace AlreadyConditioned

open CurrentConditionalFailureActivationAvoidanceZero

/-- Complete actual traces, retaining even an already-conditioned source. -/
def traces : NodeSet signature := normal.activationTraceNodes pivot forest
/-- The same common policy restricted to the actual selected trace union. -/
def successor : ForestChild signature := normal.activationTraceSuccessor pivot forest
/-- Actual deduplicated path heads and zero-edge activation rows. -/
def rows : NodeSet signature := normal.activationInteractionRows pivot forest
/-- The general fused signal, not a manually proposed row-phase table. -/
def installed : LinearSignal graph := normal.activationInteractionSignal pivot forest

/-- The actual finite selection keeps exactly the already-conditioned
source; its restricted successor has no invented activation edge. -/
theorem actual_zero_edge_trace : traces = NodeSet.singleton collider ∧ successor = (fun _ => none) := by
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
      have inForest := normal.activationTraceNodes_subset_forest pivot forest node selected
      have onPath : .observed node ∈ normal.cutPath.nodes := by
        rw [normal_window]
        exact (by decide +kernel : forall child, forest.nodes child = true ->
          (SeparationNode.observed child : SeparationNode signature) ∈
            [.observed pivotNode, .observed parent, .observed collider, .observed outcome]) node inForest
      have seed := (normal.activationTraceNodes_intersection_iff_collider pivot forest node onPath).mp selected
      rw [seedMask] at seed
      exact seed
    · intro selected
      apply normal.colliderSeeds_subset_activationTraceNodes pivot forest node
      rw [seedMask]
      exact selected
  refine ⟨selectedMask, ?_⟩
  change restrictChild traces forest.successor = (fun _ => none)
  rw [selectedMask]
  funext node
  decide +kernel +revert

/-- The collider belongs to both real selections and remains a real sink.
This is the permitted overlap, not an empty-intersection assumption. -/
theorem actual_collider_overlap : normal.pathHeads collider = true ∧ traces collider = true ∧
    keptSinks traces successor collider = true := by
  refine ⟨?_, ?_, ?_⟩
  · unfold ConditionalBackdoorPathNormalForm.pathHeads
    rw [normal_window]
    decide +kernel
  · rw [actual_zero_edge_trace.1]
    decide +kernel
  · rw [actual_zero_edge_trace.1, actual_zero_edge_trace.2]
    decide +kernel

/-- Full-cube fusion still contains the actual conditioned sink term.
This guards against cancelling an already-conditioned activation too early. -/
theorem full_cube_sink_retained (point : Cube graph) :
    (installed.forestPhase rows).value point = Bool.xor (cubeSample graph point pivot.node)
      (Bool.xor (cubeSample graph point normal.outcome) (cubeSample graph point collider)) := by
  rw [installed, rows, normal.activationInteraction_forestPhase pivot forest]
  have sinks : keptSinks traces successor = NodeSet.singleton collider := by
    rw [actual_zero_edge_trace.1, actual_zero_edge_trace.2]
    funext node
    decide +kernel +revert
  change Bool.xor _ (Bool.xor _ (hedgeNodeXor (keptSinks traces successor) _)) = _
  rw [sinks, nodeXor_singleton]

/-- Only actual original evidence membership removes the pivot and sink
terms.  No alteration of the query's outcome or conditioning set is made. -/
theorem original_conditional_character (point : Cube graph)
    (listed : point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + signature.count)
      (cubeMask graph (NodeSet.union query.action query.condition))) :
    (installed.forestPhase rows).value point = (maskPhase _ (cubeMask graph query.outcome)).value point := by
  rw [installed, rows, normal.activationInteraction_conditionalPhase pivot forest point listed]
  have same := (NodeSet.singleton_eq_true_iff outcome normal.outcome).mp normal.outcome_selected
  rw [same]
  rfl

private theorem own_basis (data : LinearSignal graph) :
    (data.rowPhase collider).value (joinCube graph (fun _ => false) (basisAssignment signature.count collider)) = true := by
  rw [joinCube, ← basisAssignment_eq_join_right, LinearSignal.rowPhase_observed_basis]
  have noSelf : signature.directed collider collider = false := by decide +kernel
  rw [LinearSignal.observedRowCoefficient, noSelf, Bool.false_and, Bool.xor_false]
  exact decide_eq_true rfl

/-- Fusion keeps one collider own bit.  Naively XORing two complete rows
would cancel it, even for this genuine zero-edge activation overlap. -/
theorem collider_own_bit_retained :
    (installed.rowPhase collider).value (joinCube graph (fun _ => false) (basisAssignment signature.count collider)) = true ∧
    Bool.xor (((LinearSignal.ofActivePath normal.cutPath).rowPhase collider).value
      (joinCube graph (fun _ => false) (basisAssignment signature.count collider)))
      (((LinearSignal.ofSuccessor (G := graph) successor).rowPhase collider).value
        (joinCube graph (fun _ => false) (basisAssignment signature.count collider))) = false := by
  rw [own_basis installed, own_basis (LinearSignal.ofActivePath normal.cutPath),
    own_basis (LinearSignal.ofSuccessor (G := graph) successor)]
  exact ⟨rfl, rfl⟩

/-- The installed zero-edge case uses the general supported direction
and whole-union oddness theorem, just like a nonzero activation trace. -/
theorem actual_union_odd : (installed.forestPhase rows).value normal.pathDirection = true :=
  normal.activationInteraction_forest_odd pivot forest

end AlreadyConditioned

end CurrentConditionalFailureActivationInteraction
end Examples
end Causality
end Thesis
