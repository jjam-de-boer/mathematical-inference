import Thesis.CausalTransport.ConditionalFailureForkAbsorption
import Thesis.Examples.ConditionalCutActivationInteraction

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentActivePathForkRouting

open PathSpecification Probability FiniteBooleanInteraction
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation
open CurrentConditionalCutActivationRoute

/-!+# Cancel a real fork read and retain its odd mandatory row

The existing normalized path is `P <- U -> C <- Y`, with activation `C -> Z`.
Its fused signal omits the nonzero fork row `U`, while both path heads read
that original observed input.  The executable fork scan chooses `U -> P`.
Installing `U` and XORing that input at `P` cancels exactly the original read
there; `C` still reads `U`, and the complete collider trace remains installed.

At the unchanged supported normalized-path direction, `U` is now the unique
odd selected row.  `P`, `C` and `Z` are even, and the outcome character is
still odd.  No prefix bit is assumed zero and no receiving own bit is doubled.
Whole-cube conservation is checked independently of that one direction.

The original action-free query is identifiable.  This is a real graph/signal
regression for the generic fork-exit construction, not a hedge or a claim of
universal conditional completeness.  The all-Small terminal construction must
still account for other incoming approaches and actual head contacts.
-/

private theorem distinct : pivotNode ≠ normal.outcome := by
  have same := (NodeSet.singleton_eq_true_iff outcome normal.outcome).mp normal.outcome_selected
  rw [same]
  decide +kernel

/-- Select the actual omitted fork, not the outgoing outcome endpoint. -/
def selected : NodeSet signature := NodeSet.singleton parent

/-- The general finite path-head scan supplies this policy's only exit. -/
def successor : ForestChild signature := normal.cutPath.forkRoutingSuccessor distinct selected

/-- Use the actual fused path/activation installation as the starting signal. -/
def installed : LinearSignal graph := interactionSignal.absorbSuccessor interactionRows successor

/-- Keep the whole actual core and the selected fork once each. -/
def rows : NodeSet signature := NodeSet.union interactionRows (normal.cutPath.forkRoutingNodes selected)

theorem actual_fork : normal.cutPath.forkNodes parent = true := by
  unfold PathSpecification.ActivePath.forkNodes
  rw [normal_window]
  decide +kernel

theorem actual_selected_forks : normal.cutPath.forkRoutingNodes selected = NodeSet.singleton parent := by
  unfold PathSpecification.ActivePath.forkRoutingNodes PathSpecification.ActivePath.forkNodes
  rw [normal_window]
  funext child
  decide +kernel +revert

/-- Enumeration picks the real first receiving head `P`; it does not keep
an arbitrary original hedge successor or add a third off-path destination. -/
theorem actual_successor : successor = (fun child => if child = parent then some pivotNode else none) := by
  funext child
  unfold successor PathSpecification.ActivePath.forkRoutingSuccessor
  rw [actual_selected_forks]
  by_cases same : child = parent
  · subst child
    rw [restrictChild_of_true (by decide +kernel : NodeSet.singleton parent parent = true), if_pos rfl]
    apply normal.cutPath.forkSuccessor_of_find distinct actual_fork
    rw [normal_window]
    decide +kernel
  · have absent : NodeSet.singleton parent child = false := by
      simp only [NodeSet.singleton, same, decide_false]
    rw [restrictChild_of_false absent, if_neg same]

/-- The actual omitted fork is outside the retained collider trace union,
even though it belongs to the larger auxiliary activation domain. -/
theorem original_trace_avoids_fork : normal.activationTraceNodes retainedPivot cutForest parent = false :=
  normal.forkNodes_activationTrace_free retainedPivot cutForest parent actual_fork

/-- The original fused receiving row genuinely reads this fork.  This is
the general intersection theorem, not a supplied zero-tail certificate. -/
theorem original_chosen_input_present : interactionSignal.parentMask pivotNode parent = true := by
  apply normal.forkInput_in_activationInteraction retainedPivot cutForest actual_fork
  rw [normal_window]
  decide +kernel

/-- The chosen receiver no longer reads `U` after the duplicate is canceled. -/
theorem chosen_input_canceled : installed.parentMask pivotNode parent = false := by
  have edge : successor parent = some pivotNode := by rw [actual_successor]; decide +kernel
  simp only [installed, LinearSignal.absorbSuccessor, actual_selected_parities.1, if_true,
    original_chosen_input_present, edge, decide_true, Bool.xor_self]

/-- The other path head retains its real `U` input.  Canceling one read
does not erase the fork from every mechanism that originally used it. -/
theorem other_input_retained : installed.parentMask collider parent = true := by
  have input : ActivePathInput.incomingEdge graph
      (GraphMutilation.barUnderline query.action (NodeSet.singleton pivotNode)) normal.cutPath.nodes (.observed parent) collider = true := by
    rw [normal_window]
    decide +kernel
  have original : interactionSignal.parentMask collider parent = true := by
    exact normal.forkInput_in_activationInteraction retainedPivot cutForest actual_fork input
  have head : interactionRows collider = true := NodeSet.subset_union_left normal.pathHeads
    (normal.activationTraceNodes retainedPivot cutForest) collider (ActivePathInput.incomingEdge_head input)
  have absent : successor parent ≠ some collider := by rw [actual_successor]; decide +kernel
  simp only [installed, LinearSignal.absorbSuccessor, head, if_true, original, absent,
    decide_false, Bool.xor_false]

theorem actual_rows : rows = NodeSet.union (NodeSet.singleton parent)
    (NodeSet.union (NodeSet.singleton pivotNode) (NodeSet.union (NodeSet.singleton collider) (NodeSet.singleton evidence))) := by
  have traceMask : normal.activationTraceNodes retainedPivot cutForest =
      NodeSet.union (NodeSet.singleton collider) (NodeSet.singleton evidence) := actual_trace_mask
  unfold rows interactionRows ConditionalBackdoorPathNormalForm.activationInteractionRows
    ConditionalBackdoorPathNormalForm.pathHeads
  rw [actual_selected_forks, normal_window, traceMask]
  funext child
  decide +kernel +revert

private theorem actual_core : interactionRows = NodeSet.union (NodeSet.singleton pivotNode)
    (NodeSet.union (NodeSet.singleton collider) (NodeSet.singleton evidence)) := by
  have traceMask : normal.activationTraceNodes retainedPivot cutForest =
      NodeSet.union (NodeSet.singleton collider) (NodeSet.singleton evidence) := actual_trace_mask
  unfold interactionRows ConditionalBackdoorPathNormalForm.activationInteractionRows
    ConditionalBackdoorPathNormalForm.pathHeads
  rw [normal_window, traceMask]
  funext child
  decide +kernel +revert

/-- All exits are real declared arrows inside the actual completed union. -/
theorem well_formed : childWellFormedBool rows successor = true := by
  rw [actual_rows, actual_successor]
  decide +kernel

private theorem stops_core : forall child, interactionRows child = true -> successor child = none := by
  rw [actual_core, actual_successor]
  decide +kernel

private theorem sinks_in_core : NodeSet.Subset (keptSinks rows successor) interactionRows := by
  rw [actual_rows, actual_successor, actual_core]
  unfold NodeSet.Subset
  decide +kernel

/-- The full original-input phase is preserved, before imposing any
conditioning or inspecting the supported odd direction. -/
theorem whole_cube_conservation (point : Cube graph) :
    (installed.forestPhase rows).value point = (interactionSignal.forestPhase interactionRows).value point := by
  have enlarged : NodeSet.union interactionRows rows = rows := by
    funext child
    change (interactionRows child || (interactionRows child || normal.cutPath.forkRoutingNodes selected child)) =
      (interactionRows child || normal.cutPath.forkRoutingNodes selected child)
    cases interactionRows child <;> cases normal.cutPath.forkRoutingNodes selected child <;> rfl
  rw [installed, ← enlarged]
  exact LinearSignal.absorbSuccessor_forestPhase _ _ _ _ well_formed stops_core sinks_in_core point

/-- All original evidence assignments, not just the balance direction,
retain the outcome character of the original normalized interaction. -/
theorem original_conditional_character (point : Cube graph)
    (listed : point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + signature.count)
      (cubeMask graph (NodeSet.union query.action query.condition))) :
    (installed.forestPhase rows).value point = (maskPhase _ (cubeMask graph query.outcome)).value point := by
  rw [whole_cube_conservation]
  exact CurrentConditionalCutActivationRoute.original_conditional_character point listed

/-- No correction changes the original supported direction or its inputs. -/
theorem direction_supported : normal.pathDirection ∈
    FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + signature.count)
      (cubeMask graph (NodeSet.union query.action query.condition)) := normal.pathDirection_member

theorem outcome_odd : (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value normal.pathDirection = true :=
  normal.activationInteraction_outcome_odd retainedPivot

/-- At the unchanged direction, the new selected fork is the unique odd
row.  Finite calculations reduce only the legal masks and the proved actual
path window, not the exhaustive normalization search or any model table. -/
theorem fork_unique_odd : (installed.rowPhase parent).value normal.pathDirection = true ∧
    (forall child, rows child = true -> child ≠ parent -> (installed.rowPhase child).value normal.pathDirection = false) := by
  have traceMask : normal.activationTraceNodes retainedPivot cutForest =
      NodeSet.union (NodeSet.singleton collider) (NodeSet.singleton evidence) := actual_trace_mask
  rw [actual_rows]
  unfold installed interactionSignal ConditionalBackdoorPathNormalForm.activationInteractionSignal
    ConditionalBackdoorPathNormalForm.pathHeads ConditionalBackdoorPathNormalForm.activationTraceSuccessor LinearSignal.ofActivePath
  rw [normal_window, traceMask, actual_core, actual_successor]
  unfold ConditionalBackdoorPathNormalForm.pathDirection LinearSignal.activePathDirection
  rw [normal_window]
  decide +kernel

end CurrentActivePathForkRouting
end Examples
end Causality
end Thesis
