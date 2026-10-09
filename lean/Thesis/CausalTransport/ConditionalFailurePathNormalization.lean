import Thesis.CausalTransport.ActivePathNormalization
import Thesis.CausalTransport.ConditionalFailurePaths

namespace Thesis
namespace Causality

universe u

variable {S : ObservedSignature.{u}}

open PathSpecification

/-!
# Collider-normal back-door data at conditional failures

The original failure-path constructor deliberately returns the first path
found by the finite witness search.  It is sufficient for extracting actual
collider activations, but its search order does not justify any minimality
argument at activation/path intersections.

Here the same negative singleton exchange test supplies a nonempty path type
in the singleton outgoing-cut graph.  The finite collider-normal search then
selects a path with fewest colliders and, at equal count, greatest collider
rank sum.  Its certificates are proved by the search, not supplied as extra
readiness assumptions.  Restoring the singleton outgoing edges retains the
exact selected list and derives its first incoming edge by the shared adapter.

The normal form compares paths with the same selected outcome and the exact
exchange-test conditioning set.  It does not claim optimality over arbitrary
outcome choices or over paths with a different first-edge constraint.  In
particular its comparison graph is the outgoing-cut graph, not an unrelated
stronger separation semantics.

This establishes actual normalized graph data.  Rerouting intersections must
still be proved to improve these objectives, and small-forest intersections
and the combined parity-conservation argument remain separate obligations.
The first-success API stays unchanged for callers which do not need optimality.
-/

/-- A certified normal form in the exact singleton exchange graph.  The two
optimality fields are theorem certificates of the executable constructor below.
They are not additional assumptions of an irreducible conditional failure. -/
structure ConditionalBackdoorPathNormalForm (graph : ObservedGraph S)
    (query : ConditionalKernelQuery S) (node : Fin S.count) : Type where
  outcome : Fin S.count
  outcome_selected : query.outcome outcome = true
  cutPath : ActivePath graph
    (GraphMutilation.barUnderline query.action (NodeSet.singleton node))
    (NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton node)))
    (.observed node) (.observed outcome)
  count_minimal : forall competitor : ActivePath graph
    (GraphMutilation.barUnderline query.action (NodeSet.singleton node))
    (NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton node)))
    (.observed node) (.observed outcome),
    colliderCount graph (GraphMutilation.barUnderline query.action (NodeSet.singleton node)) cutPath.nodes ≤
      colliderCount graph (GraphMutilation.barUnderline query.action (NodeSet.singleton node)) competitor.nodes
  rank_maximal : forall competitor : ActivePath graph
    (GraphMutilation.barUnderline query.action (NodeSet.singleton node))
    (NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton node)))
    (.observed node) (.observed outcome),
    colliderCount graph (GraphMutilation.barUnderline query.action (NodeSet.singleton node)) competitor.nodes =
      colliderCount graph (GraphMutilation.barUnderline query.action (NodeSet.singleton node)) cutPath.nodes ->
    colliderRankSum graph (GraphMutilation.barUnderline query.action (NodeSet.singleton node)) competitor.nodes ≤
      colliderRankSum graph (GraphMutilation.barUnderline query.action (NodeSet.singleton node)) cutPath.nodes

namespace ConditionalBackdoorPathNormalForm

/-- A negative exchange test constructs the normal form without assuming
a chosen path, minimum, maximum, or disjoint activation network.  The initial
endpoint selection uses the ordinary search; normalization keeps those endpoints. -/
def ofExchangeTestFalse (graph : ObservedGraph S) (query : ConditionalKernelQuery S)
    (node : Fin S.count) (failed : conditionalExchangeTest graph query node = false) :
    ConditionalBackdoorPathNormalForm graph query node := by
  let m := GraphMutilation.barUnderline query.action (NodeSet.singleton node)
  let conditioned := NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton node))
  let connection := activeConnectionOfDSeparatedFalse graph m query.outcome
    (NodeSet.singleton node) conditioned failed
  have target_eq : connection.target = node :=
    (NodeSet.singleton_eq_true_iff node connection.target).mp connection.target_selected
  have existsPath : Nonempty (ActivePath graph m conditioned (.observed node) (.observed connection.source)) := by
    refine ⟨?_⟩
    simpa only [target_eq] using connection.path.reverse
  exact {
    outcome := connection.source
    outcome_selected := connection.source_selected
    cutPath := colliderNormalActivePathOfNonempty graph m conditioned
      (.observed node) (.observed connection.source) existsPath
    count_minimal := colliderNormalActivePathOfNonempty_count_minimal graph m conditioned
      (.observed node) (.observed connection.source) existsPath
    rank_maximal := colliderNormalActivePathOfNonempty_rank_maximal graph m conditioned
      (.observed node) (.observed connection.source) existsPath
  }

/-- Every retained conditioner of an exhausted exchange search admits actual
normal-form data.  No extra collider-normality flag is supplied by the caller. -/
def ofNoExchange (graph : ObservedGraph S) (query : ConditionalKernelQuery S)
    (exhausted : conditionalExchangeStep? graph query = none)
    (node : Fin S.count) (selected : query.condition node = true) :
    ConditionalBackdoorPathNormalForm graph query node :=
  ofExchangeTestFalse graph query node
    (conditionalExchangeStep?_none_excludes_all graph query exhausted node selected)

/-- Restore the exact normal-form list to the action-cut graph.  The adapter
proves first-edge orientation and excludes singleton paths from the actual
query's disjoint outcome/condition sets; no independent edge flag is needed. -/
def backdoor {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {node : Fin S.count}
    (normal : ConditionalBackdoorPathNormalForm graph query node)
    (selected : query.condition node = true) : ConditionalBackdoorPath graph query node :=
  .ofCutPath graph query node normal.outcome selected normal.outcome_selected normal.cutPath

/-- Edge restoration preserves the selected vertex list exactly.  Subsequent
activation arguments therefore refer to the normalized path's actual data. -/
theorem backdoor_nodes {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {node : Fin S.count}
    (normal : ConditionalBackdoorPathNormalForm graph query node)
    (selected : query.condition node = true) : (normal.backdoor selected).path.nodes = normal.cutPath.nodes := rfl

end ConditionalBackdoorPathNormalForm

/-- The arbitrary-depth failure provenance exposes a collider-normal path
at its own irreducible terminal.  This does not replace or strengthen the
terminal's still-open semantic counterexample obligation. -/
def ConditionalKernelFailure.normalBackdoorPath
    {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {fail : IdentificationFail S}
    (failure : ConditionalKernelFailure graph query fail)
    (node : Fin S.count) (selected : failure.terminal.condition node = true) :
    ConditionalBackdoorPathNormalForm graph failure.terminal node :=
  .ofNoExchange graph failure.terminal failure.no_exchange node selected

end Causality
end Thesis
