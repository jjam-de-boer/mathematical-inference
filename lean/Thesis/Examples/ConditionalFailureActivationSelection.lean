import Thesis.Examples.ConditionalFailureActivationSelectionGraph

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureActivationSelection

open Probability PathSpecification HedgeChannelInstallation

/-!
# A genuine hedge whose activation trace lies inside Small

The ordered vertices are `X(0),Y(1),C(2),Z(3),P(4)`.  Directed arrows are
`X -> P` and `Y -> C -> Z`; bidirected edges are `X <-> P`, `P <-> C`,
and `C <-> Z`.  For `P(Y | do(X), P,Z)`, the displayed numerator hedge has
Large `X,C,Z,P`, Small `C,Z,P`, and roots `Z,P`.  Both forests and the
unchanged original numerator query are certified by the actual finite tests.

The latest pivot reachable from the stored Small source `P` is `P` itself.
An actual active path is `P <- L(C,P) -> C <- Y`, with the genuine collider
`C` activated by `C -> Z`.  That complete activation trace lies *entirely*
inside Small.  For the general normal form, a structural argument proves its
whole trace union lies inside Small: `X` is excluded by action avoidance, and
the queried endpoint `Y` has no incoming expanded edge and hence cannot be a
collider source.  The outside-Small selection is therefore empty without
evaluating the exhaustive normal-form search.  A construction demanding
disjointness from Small, or installing inside traces again as background,
would mishandle this case.

The separate `ConditionalFailureActivationSelectionCounterexample` companion
retains all three Small rows with one legal signal and builds a positive
original-alphabet countermodel.  This graph module checks the actual overlap
and pruning facts independently of that heavier semantic assembly.  Together
they cover a real nontrivial Small-overlap case, not universal path coverage.
-/

def traces : NodeSet signature := normal.activationTraceNodes pivot.toRetained forest.toCutForest
def outsideRows : NodeSet signature := normal.activationTraceOutside pivot.toRetained forest.toCutForest witness.small

def activation : ConditionalColliderActivationRoute query pivot.node collider where
  before := [collider]
  endpoint := evidence
  endpoint_condition := by decide +kernel
  endpoint_ne_pivot := by decide +kernel
  starts := rfl
  simple := by decide +kernel
  consecutive := by decide +kernel
  action_free := by decide +kernel
  before_given_free := by decide +kernel

def trace := forest.path collider (forest.contains_activation collider activation)

theorem trace_codes : trace.nodes.map Fin.val = [2, 3] := by decide +kernel

/-- Both the collider and its final other conditioner are mandatory Small
rows.  The trace must not be installed a second time as background. -/
theorem activation_is_inside_small : forall node, node ∈ trace.nodes -> witness.small node = true := by
  intro node visited
  have codes : node.val ∈ [2, 3] := by
    rw [← trace_codes]
    exact List.mem_map.mpr ⟨node, visited, rfl⟩
  change decide (2 ≤ node.val) = true
  apply decide_eq_true
  rcases List.mem_cons.mp codes with equal | later
  · omega
  · have equal := List.mem_singleton.mp later
    omega

private theorem outcome_not_collider_seed : normal.colliderSeeds outcome = false := by
  cases selected : normal.colliderSeeds outcome with
  | false => rfl
  | true =>
      rcases (normal.colliderSeeds_eq_true_iff outcome).mp selected with ⟨before, after, previous, next, _window, actual⟩
      have noIncoming : graph.expandedMutilatedEdge
          (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) previous (.observed outcome) = false := by
        cases previous with
        | observed parent =>
            exact (by decide +kernel : forall parent : Fin signature.count,
              graph.expandedMutilatedEdge (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node))
                (.observed parent) (.observed outcome) = false) parent
        | latentPair left right =>
            exact (by decide +kernel : forall left right : Fin signature.count,
              graph.expandedMutilatedEdge (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node))
                (.latentPair left right) (.observed outcome) = false) left right
      have incoming := actual.1
      rw [noIncoming] at incoming
      cases incoming

private theorem outcome_on_normal_path : .observed outcome ∈ normal.cutPath.nodes := by
  have same := (NodeSet.singleton_eq_true_iff outcome normal.outcome).mp normal.outcome_selected
  rw [← same]
  exact List.mem_of_getLast? normal.cutPath.finishes

/-- The actual auxiliary domain also contains queried `Y`, which is not
a collider source and must not become an activation interaction row. -/
theorem irrelevant_ancestor_pruned : forest.nodes outcome = true ∧ traces outcome = false := by
  refine ⟨by decide +kernel, ?_⟩
  cases selected : traces outcome with
  | false => rfl
  | true =>
      have source := (normal.activationTraceNodes_intersection_iff_collider pivot.toRetained forest.toCutForest outcome outcome_on_normal_path).mp selected
      exact False.elim (Bool.false_ne_true (outcome_not_collider_seed.symm.trans source))

/-- Every trace row of the computed normal form is mandatory Small.
This uses graph/action/endpoint certificates, not evaluation of the
exhaustive normal-form search or a guessed exact path list. -/
theorem normal_trace_union_inside_small : NodeSet.Subset traces witness.small := by
  intro node selected
  by_cases isAction : node = actionNode
  · subst node
    have free := normal.activationTraceNodes_action_free pivot.toRetained forest.toCutForest actionNode selected
    have acted : query.action actionNode = true := by decide +kernel
    rw [acted] at free
    cases free
  · by_cases isOutcome : node = outcome
    · subst node
      rw [irrelevant_ancestor_pruned.2] at selected
      cases selected
    · change decide (2 ≤ node.val) = true
      apply decide_eq_true
      have nonzero : node.val ≠ 0 := fun same => isAction (Fin.ext same)
      have notOne : node.val ≠ 1 := fun same => isOutcome (Fin.ext same)
      omega

theorem outside_rows_empty : outsideRows = NodeSet.empty := by
  funext node
  cases selected : outsideRows node with
  | false => rfl
  | true =>
      have onTrace : traces node = true := (Bool.and_eq_true_iff.mp selected).1
      have outside := normal.activationTraceOutside_not_mandatory pivot.toRetained forest.toCutForest witness.small node selected
      have inside := normal_trace_union_inside_small node onTrace
      rw [outside] at inside
      cases inside

theorem small_rows_retained : NodeSet.union witness.small outsideRows = witness.small := by
  rw [outside_rows_empty]
  funext node
  exact Bool.or_false _

end CurrentConditionalFailureActivationSelection
end Examples
end Causality
end Thesis
