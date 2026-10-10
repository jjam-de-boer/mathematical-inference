import Thesis.CausalTransport.ConditionalFailureActivationAvoidance

namespace Thesis
namespace Causality

open PathSpecification HedgeChannelInstallation

/-!
# A common collider-activation policy in the exact outgoing cut

The larger bar-graph forest cannot be built at every retained pivot: its
universal coverage may demand a route through the pivot that its domain must
exclude.  This interface covers actual cut routes instead.  All branches use
one successor map, so a shared vertex has one continuation and one local row.

The existing verified forest search is reused on the outgoing-masked search
signature from `ConditionalCutActivationRoute`.  In that search graph the
pivot has no outgoing arrow.  It is therefore trivially latest among its own
reachable conditioners, irrespective of its rank in the original graph.
This is a theorem about auxiliary search data, not a maximality assumption
about the original pivot.  The constructor takes only its actual membership
in the original condition set.

The public domain, successors and paths use the original node indices.  Their
well-formedness and every real cut arrow are proved in the original graph;
the temporary signature is never used for model installation or root inputs.
Conditioned vertices remain sinks, including zero-edge activations.  Complete
common-policy paths inherit normalized-path avoidance without a latest-pivot
premise.  `ConditionalFailureActivationSelection` and its interaction module
separately select and install those actual traces at any retained pivot.
Routing missing Small rows and transferring Small oddness are still distinct
obligations, not conclusions of the policy interface here.
-/

variable {S : ObservedSignature.{0}}

namespace ConditionalCutActivationRouting

/-- The unchanged query labels on the auxiliary graph-search signature.
No observed coordinate, alphabet value or conditioning label is dropped. -/
def searchQuery (query : ConditionalKernelQuery S) (pivot : Fin S.count) :
    ConditionalKernelQuery (searchSignature pivot) where
  outcome := query.outcome
  action := query.action
  condition := query.condition
  action_outcome_disjoint := query.action_outcome_disjoint
  action_condition_disjoint := query.action_condition_disjoint
  outcome_condition_disjoint := query.outcome_condition_disjoint

-- The old latest-pivot certificate has a graph parameter, though its finite
-- observed reachability and the forest search do not read bidirected edges.
-- Retain those edges too rather than fabricate a different latent alphabet.
private def searchGraph (graph : ObservedGraph S) (pivot : Fin S.count) :
    ObservedGraph (searchSignature pivot) where
  bidirected := graph.bidirected
  bidirected_symmetric := graph.bidirected_symmetric
  bidirected_irreflexive := graph.bidirected_irreflexive

private theorem reachable_from_pivot_eq (query : ConditionalKernelQuery S) (pivot target : Fin S.count)
    (reachable : FiniteReachability.Reachable (observedEdge query pivot) pivot target) : target = pivot := by
  rcases reachable with ⟨length, ⟨walk⟩⟩
  cases walk with
  | refl => rfl
  | @step length pivot child target edge rest =>
      have self := (NodeSet.singleton_eq_true_iff pivot pivot).mpr rfl
      change (if query.action child = true then false else (S.directed pivot child && !(NodeSet.singleton pivot pivot))) = true at edge
      rw [self] at edge
      simp only [Bool.not_true, Bool.and_false, ite_self] at edge
      cases edge

/-- The cut pivot is latest only in the auxiliary search graph, because
it reaches no different vertex there.  Original-graph maximality is neither
asserted nor needed.  All returned data are the supplied finite pivot itself. -/
private def searchPivot (graph : ObservedGraph S) (query : ConditionalKernelQuery S) (pivot : Fin S.count)
    (selected : query.condition pivot = true) :
    LatestConditionalPivot (searchGraph graph pivot) (searchQuery query pivot) pivot := by
  let edge := observedEdge query pivot
  have bounded := FiniteReachability.boundedWalk_of_reachable finBeq (NodeSet.enumerated S)
    edge finBeq_eq_true_iff (NodeSet.mem_enumerated S) (FiniteReachability.Reachable.refl edge pivot)
  rw [NodeSet.length_enumerated] at bounded
  refine {
    node := pivot
    selected := selected
    reachable := (FiniteReachability.within_eq_true_iff_boundedWalk finBeq (NodeSet.enumerated S)
      edge finBeq_eq_true_iff (NodeSet.mem_enumerated S) _ _ _).mpr bounded
    latest := ?_
  }
  intro other _condition reaches
  have reachable := FiniteReachability.Reachable.of_bounded
    ((FiniteReachability.within_eq_true_iff_boundedWalk finBeq (NodeSet.enumerated S)
      edge finBeq_eq_true_iff (NodeSet.mem_enumerated S) _ _ _).mp reaches)
  have same := reachable_from_pivot_eq query pivot other reachable
  rw [same]
  exact Nat.le_refl _

end ConditionalCutActivationRouting

/-- A shared cut-policy search, not a family of independently chosen
branches.  Its auxiliary certificate is wrapped so downstream code receives
original-signature graph proofs through the interface below. -/
structure ConditionalCutColliderActivationForest (query : ConditionalKernelQuery S) (pivot : Fin S.count) where
  policy : ConditionalColliderActivationForest (ConditionalCutActivationRouting.searchQuery query pivot) pivot

namespace ConditionalCutColliderActivationForest

variable {query : ConditionalKernelQuery S} {pivot : Fin S.count}

/-- Construct one common policy at any actual retained conditioner.
The internal finite search certifies all its own coverage and stopping facts;
the caller supplies no maximality, route avoidance or disjointness flags. -/
def ofRetainedPivot (graph : ObservedGraph S) (query : ConditionalKernelQuery S) (pivot : Fin S.count)
    (selected : query.condition pivot = true) : ConditionalCutColliderActivationForest query pivot where
  policy := .ofLatestPivot (ConditionalCutActivationRouting.searchPivot graph query pivot selected)

/-- Actual selected observed rows, on the original index type. -/
def nodes (forest : ConditionalCutColliderActivationForest query pivot) : NodeSet S := forest.policy.nodes

/-- One common successor for all branches, on the original index type. -/
def successor (forest : ConditionalCutColliderActivationForest query pivot) : ForestChild S := forest.policy.successor

/-- The auxiliary cut arrows are genuine original arrows.  Transfer the
finite well-formedness test without replacing the original signature. -/
theorem wellFormed (forest : ConditionalCutColliderActivationForest query pivot) :
    childWellFormedBool forest.nodes forest.successor = true := by
  apply List.all_eq_true.mpr
  intro parent _member
  cases selected : forest.nodes parent with
  | false =>
      have stopped := childWellFormed_off forest.policy.nodes forest.policy.successor forest.policy.wellFormed selected
      change forest.successor parent = none at stopped
      rw [stopped]
  | true =>
      cases next : forest.successor parent with
      | none => rfl
      | some child =>
          have actual := childWellFormed_edge forest.policy.nodes forest.policy.successor forest.policy.wellFormed next
          have original : S.directed parent child = true := (Bool.and_eq_true_iff.mp actual.2.2).1
          change (forest.nodes child && S.directed parent child) = true
          exact Bool.and_eq_true_iff.mpr ⟨actual.2.1, original⟩

/-- Incoming action cuts keep the entire original action set out. -/
theorem action_free (forest : ConditionalCutColliderActivationForest query pivot) (node : Fin S.count)
    (selected : forest.nodes node = true) : query.action node = false := forest.policy.action_free node selected

/-- Outgoing-cut reachability, not original-graph maximality, excludes the pivot. -/
theorem pivot_free (forest : ConditionalCutColliderActivationForest query pivot) : forest.nodes pivot = false :=
  forest.policy.pivot_free

/-- Selected conditioners are exactly the actual policy sinks. -/
theorem sink_iff_condition (forest : ConditionalCutColliderActivationForest query pivot) (node : Fin S.count)
    (selected : forest.nodes node = true) : forest.successor node = none ↔ query.condition node = true :=
  forest.policy.sink_iff_condition node selected

/-- Every selected successor is an actual arrow of the original exact
exchange cut, not merely a well-formed arrow of the larger bar graph. -/
theorem successor_cut_edge (forest : ConditionalCutColliderActivationForest query pivot) (graph : ObservedGraph S)
    (parent child : Fin S.count) (edge : forest.successor parent = some child) :
    graph.expandedMutilatedEdge (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot))
      (.observed parent) (.observed child) = true := by
  have actual := childWellFormed_edge forest.policy.nodes forest.policy.successor forest.policy.wellFormed edge
  have free := forest.action_free child actual.2.1
  have kept : ConditionalCutActivationRouting.observedEdge query pivot parent child = true := by
    change (if query.action child = true then false else (S.directed parent child && !(NodeSet.singleton pivot parent))) = true
    rw [free]
    exact actual.2.2
  rw [ConditionalCutActivationRouting.observedEdge_eq_expanded graph] at kept
  exact kept

/-- Coverage is for real routes in the exact cut, not every route in the
larger bar graph.  The proved arrow equality translates the supplied route
into the unchanged executable forest search. -/
theorem contains_activation (forest : ConditionalCutColliderActivationForest query pivot)
    {graph : ObservedGraph S} (collider : Fin S.count)
    (route : ConditionalCutColliderActivationRoute graph query pivot collider) : forest.nodes collider = true := by
  apply forest.policy.contains_activation collider
  refine {
    before := route.before
    endpoint := route.endpoint
    endpoint_condition := route.endpoint_condition
    endpoint_ne_pivot := route.endpoint_ne_pivot
    starts := route.starts
    simple := route.simple
    consecutive := ?_
    action_free := route.action_free
    before_given_free := route.before_given_free
  }
  apply Consecutive.mono (fun parent child edge => ?_) _ route.cut_consecutive
  change ConditionalCutActivationRouting.observedEdge query pivot parent child = true
  rw [ConditionalCutActivationRouting.observedEdge_eq_expanded graph]
  exact edge

/-- Repackage the exact computed common-policy path on the original
signature.  Lists, endpoint and successor map are unchanged, not searched again. -/
def path (forest : ConditionalCutColliderActivationForest query pivot) (collider : Fin S.count)
    (selected : forest.nodes collider = true) : SuccessorPath forest.nodes forest.successor collider :=
  let traced := forest.policy.path collider selected
  { nodes := traced.nodes, endpoint := traced.endpoint, starts := traced.starts, finishes := traced.finishes,
    simple := traced.simple, consecutive := traced.consecutive, stopped := traced.stopped, inside := traced.inside }

/-- Each complete policy path ends at a real original conditioner other
than the pivot.  This includes an already-conditioned source's singleton path. -/
theorem path_endpoint_condition (forest : ConditionalCutColliderActivationForest query pivot)
    (collider : Fin S.count) (selected : forest.nodes collider = true) :
    query.condition (forest.path collider selected).endpoint = true ∧ (forest.path collider selected).endpoint ≠ pivot :=
  forest.policy.path_endpoint_condition collider selected

/-- No proper path vertex is originally conditioned.  The same stopping
theorem is retained on the unchanged list, without a second route search. -/
theorem path_before_condition_free (forest : ConditionalCutColliderActivationForest query pivot)
    (collider : Fin S.count) (selected : forest.nodes collider = true) (node : Fin S.count)
    (member : node ∈ (forest.path collider selected).nodes) (notEndpoint : node ≠ (forest.path collider selected).endpoint) :
    query.condition node = false := forest.policy.path_before_condition_free collider selected node member notEndpoint

/-- The policy's complete trace is an actual cut route.  Reuse its proved
first-conditioner stopping contract; transfer only the real arrow relation. -/
def activationRoute (forest : ConditionalCutColliderActivationForest query pivot) (graph : ObservedGraph S)
    (collider : Fin S.count) (selected : forest.nodes collider = true) :
    ConditionalCutColliderActivationRoute graph query pivot collider := by
  let route := forest.policy.activationRoute collider selected
  refine {
    before := route.before
    endpoint := route.endpoint
    endpoint_condition := route.endpoint_condition
    endpoint_ne_pivot := route.endpoint_ne_pivot
    starts := route.starts
    simple := route.simple
    consecutive := Consecutive.mono (ConditionalCutActivationRouting.observedEdge_implies_action_edge query pivot) _ route.consecutive
    action_free := route.action_free
    before_given_free := route.before_given_free
    cut_consecutive := ?_
  }
  exact Consecutive.mono (fun parent child edge =>
    (ConditionalCutActivationRouting.observedEdge_eq_expanded graph query pivot parent child).symm ▸ edge) _ route.consecutive

/-- The route adapter retains the entire computed list, including all
merged suffix vertices and the real conditioned endpoint. -/
theorem activationRoute_nodes (forest : ConditionalCutColliderActivationForest query pivot) (graph : ObservedGraph S)
    (collider : Fin S.count) (selected : forest.nodes collider = true) :
    (forest.activationRoute graph collider selected).before ++ [(forest.activationRoute graph collider selected).endpoint] =
      (forest.path collider selected).nodes := forest.policy.activationRoute_nodes collider selected

/-- Shared branches have the same actual endpoint because they follow
the same map.  No uniqueness of incoming graph parents is assumed. -/
theorem path_endpoints_eq_of_shared (forest : ConditionalCutColliderActivationForest query pivot)
    (left right : Fin S.count) (leftSelected : forest.nodes left = true) (rightSelected : forest.nodes right = true)
    (shared : Fin S.count) (leftMember : shared ∈ (forest.path left leftSelected).nodes)
    (rightMember : shared ∈ (forest.path right rightSelected).nodes) :
    (forest.path left leftSelected).endpoint = (forest.path right rightSelected).endpoint :=
  (forest.path left leftSelected).endpoint_eq_of_shared (forest.path right rightSelected) shared leftMember rightMember

end ConditionalCutColliderActivationForest

namespace ConditionalColliderActivationForest

/-- Reinterpret an existing stronger bar-policy forest as a cut-policy
forest, without changing its domain or successor map.  Its proved pivot-free
domain makes every selected parent different from the pivot, so all its
arrows survive the singleton outgoing cut.  Cut-route coverage follows from
its stronger bar-route coverage.  This explicit adapter lets older clients
reuse the same general trace/parity proofs as arbitrary retained pivots. -/
def toCutForest {query : ConditionalKernelQuery S} {pivot : Fin S.count}
    (forest : ConditionalColliderActivationForest query pivot) : ConditionalCutColliderActivationForest query pivot := by
  refine { policy := {
    nodes := forest.nodes
    successor := forest.successor
    wellFormed := ?_
    action_free := forest.action_free
    pivot_free := forest.pivot_free
    sink_iff_condition := forest.sink_iff_condition
    contains_activation := ?_
  } }
  · apply List.all_eq_true.mpr
    intro parent _member
    cases selected : forest.nodes parent with
    | false =>
        have stopped := childWellFormed_off forest.nodes forest.successor forest.wellFormed selected
        rw [stopped]
    | true =>
        cases next : forest.successor parent with
        | none => rfl
        | some child =>
            have actual := childWellFormed_edge forest.nodes forest.successor forest.wellFormed next
            have different : parent ≠ pivot := by
              intro same
              rw [same, forest.pivot_free] at selected
              cases selected
            have absent : NodeSet.singleton pivot parent = false := by
              apply Bool.eq_false_iff.mpr
              intro present
              exact different ((NodeSet.singleton_eq_true_iff pivot parent).mp present)
            change (forest.nodes child && (S.directed parent child && !(NodeSet.singleton pivot parent))) = true
            rw [actual.2.1, actual.2.2, absent]
            rfl
  · intro collider route
    apply forest.contains_activation collider
    refine {
      before := route.before
      endpoint := route.endpoint
      endpoint_condition := route.endpoint_condition
      endpoint_ne_pivot := route.endpoint_ne_pivot
      starts := route.starts
      simple := route.simple
      consecutive := ?_
      action_free := route.action_free
      before_given_free := route.before_given_free
    }
    exact Consecutive.mono (ConditionalCutActivationRouting.observedEdge_implies_action_edge query pivot) _ route.consecutive

/-- The compatibility adapter does not alter the selected original rows. -/
theorem toCutForest_nodes {query : ConditionalKernelQuery S} {pivot : Fin S.count}
    (forest : ConditionalColliderActivationForest query pivot) : forest.toCutForest.nodes = forest.nodes := rfl

/-- The compatibility adapter preserves the shared successor exactly,
including actual conditioned stops and all branch merges. -/
theorem toCutForest_successor {query : ConditionalKernelQuery S} {pivot : Fin S.count}
    (forest : ConditionalColliderActivationForest query pivot) : forest.toCutForest.successor = forest.successor := rfl

/-- Domain/map compatibility preserves every complete computed trace,
not merely its reachability proposition or a selected endpoint. -/
theorem toCutForest_path_nodes {query : ConditionalKernelQuery S} {pivot : Fin S.count}
    (forest : ConditionalColliderActivationForest query pivot) (collider : Fin S.count)
    (selected : forest.nodes collider = true) :
    (forest.toCutForest.path collider selected).nodes = (forest.path collider selected).nodes :=
  (forest.toCutForest.path collider selected).nodes_eq_of_same_source (forest.path collider selected)

/-- The conditioned endpoint itself is unchanged by the explicit adapter. -/
theorem toCutForest_path_endpoint {query : ConditionalKernelQuery S} {pivot : Fin S.count}
    (forest : ConditionalColliderActivationForest query pivot) (collider : Fin S.count)
    (selected : forest.nodes collider = true) :
    (forest.toCutForest.path collider selected).endpoint = (forest.path collider selected).endpoint :=
  (forest.toCutForest.path collider selected).endpoint_eq_of_shared (forest.path collider selected) collider
    (List.mem_of_head? (forest.toCutForest.path collider selected).starts)
    (List.mem_of_head? (forest.path collider selected).starts)

end ConditionalColliderActivationForest

namespace ConditionalBackdoorPathNormalForm

/-- Actual cut-path collider activity supplies its complete common-policy
path at any retained pivot.  No independent selected-collider flag or
latest-pivot certificate is supplied by the caller. -/
def cutActivationForestPath {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {pivot : Fin S.count}
    (normal : ConditionalBackdoorPathNormalForm graph query pivot)
    (forest : ConditionalCutColliderActivationForest query pivot) (selected : query.condition pivot = true)
    (before after : List (SeparationNode S)) (previous next : SeparationNode S) (collider : Fin S.count)
    (window : normal.cutPath.nodes = before ++ previous :: .observed collider :: next :: after)
    (isCollider : IsCollider graph (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot))
      previous (.observed collider) next) : SuccessorPath forest.nodes forest.successor collider :=
  forest.path collider (forest.contains_activation collider
    (normal.cutColliderActivationRoute selected before after previous next collider window isCollider))

/-- The complete shared-policy trace meets the actual normalized path
only at its collider source, without original-graph pivot maximality.  This
does not assert avoidance by irrelevant ancestors in the whole domain. -/
theorem cut_activation_forest_path_intersection_eq_collider
    {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {pivot : Fin S.count}
    (normal : ConditionalBackdoorPathNormalForm graph query pivot)
    (forest : ConditionalCutColliderActivationForest query pivot) (selected : query.condition pivot = true)
    (before after : List (SeparationNode S)) (previous next : SeparationNode S) (collider : Fin S.count)
    (window : normal.cutPath.nodes = before ++ previous :: .observed collider :: next :: after)
    (isCollider : IsCollider graph (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot))
      previous (.observed collider) next)
    (node : Fin S.count)
    (onRoute : node ∈ (normal.cutActivationForestPath forest selected before after previous next collider window isCollider).nodes)
    (onPath : .observed node ∈ normal.cutPath.nodes) : node = collider := by
  let covered := forest.contains_activation collider
    (normal.cutColliderActivationRoute selected before after previous next collider window isCollider)
  apply normal.cut_activation_path_intersection_eq_collider before after previous next collider window isCollider
    (forest.activationRoute graph collider covered) node
  · rw [forest.activationRoute_nodes]
    exact onRoute
  · exact onPath

end ConditionalBackdoorPathNormalForm

end Causality
end Thesis
