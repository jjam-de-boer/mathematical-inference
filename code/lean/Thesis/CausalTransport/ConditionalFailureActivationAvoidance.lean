import Thesis.CausalTransport.ConditionalFailurePivot
import Thesis.CausalTransport.ConditionalFailurePathNormalization
import Thesis.CausalTransport.ActivePathColliderRerouting
import Thesis.CausalTransport.ConditionalFailureActivationForest
import Thesis.CausalTransport.ConditionalCutActivationRoute

namespace Thesis
namespace Causality

open PathSpecification

variable {S : ObservedSignature.{0}}

/-!
# Activation routes meet a normalized path only at their own collider

The generic directed-detour theorem supplies a contradiction to path
optimality once its local certificates are available.  This module derives
those certificates from the actual conditional graph data.  It does not ask
for a disjoint activation/path flag, a selected return vertex, or a second
independent activation certificate.

Take the first return after the collider along any certified activation
route.  The preceding detour vertices are disjoint from the whole active
path by finite first-intersection search.  They precede the route's final
conditioner, so the original route certificates make them open and action
free.  The remaining directed suffix activates the return vertex.

The general theorem uses routes certified in the singleton outgoing cut
used by the normal form.  `ConditionalCutActivationRoute` constructs these
from actual cut-graph collider activity at any retained pivot.  A latest
reachable pivot is not required by this detour argument.  The older API is
preserved: maximality proves that its larger action-cut route survives the
singleton cut, and the general theorem then applies.  In both cases the
detour is a competitor in the *same* graph and conditioning set as the
selected path.  Its return has later observed rank; whether it occurs before
or after the old collider, the corresponding detour exclusion applies.

The result concerns every certified cut-surviving activation route, not
just one policy's selected child trace.  It does not assert disjointness between activation
branches, disjointness from the small hedge forest, or combined parity
conservation.  Those are different parts of the remaining countermodel proof.
-/

/-! ## Replay the actual route in the exact singleton outgoing-cut graph -/

private theorem cut_edge_of_observed_action_edge (graph : ObservedGraph S)
    (query : ConditionalKernelQuery S) (pivot parent child : Fin S.count)
    (notPivot : parent ≠ pivot) (edge : mutilatedDirected S query.action parent child = true) :
    graph.expandedMutilatedEdge (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot))
      (.observed parent) (.observed child) = true := by
  have childFree := action_false_of_mutilatedDirected query.action edge
  have actual : S.directed parent child = true := by
    simpa only [mutilatedDirected, childFree, Bool.false_eq_true, if_false] using edge
  have pivotFalse : NodeSet.singleton pivot parent = false := decide_eq_false notPivot
  simp only [ObservedGraph.expandedMutilatedEdge, GraphMutilation.barUnderline, actual,
    childFree, pivotFalse, Bool.not_false, Bool.and_true]

private theorem map_cut_directed (graph : ObservedGraph S) (query : ConditionalKernelQuery S)
    (pivot : Fin S.count) : forall nodes : List (Fin S.count),
    Consecutive (fun parent child => mutilatedDirected S query.action parent child = true) nodes ->
    (forall node, node ∈ nodes -> node ≠ pivot) ->
    Consecutive (fun parent child => graph.expandedMutilatedEdge
      (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot)) parent child = true)
      (nodes.map SeparationNode.observed)
  | [], _directed, _avoids => True.intro
  | [_], _directed, _avoids => True.intro
  | parent :: child :: rest, directed, avoids =>
      ⟨cut_edge_of_observed_action_edge graph query pivot parent child
          (avoids parent (List.mem_cons.mpr (Or.inl rfl))) directed.1,
        map_cut_directed graph query pivot (child :: rest) directed.2
          (fun node member => avoids node (List.mem_cons.mpr (Or.inr member)))⟩

private theorem route_cut_directed {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    {source collider : Fin S.count} (pivot : LatestConditionalPivot graph query source)
    (route : ConditionalColliderActivationRoute query pivot.node collider) :
    Consecutive (fun parent child => graph.expandedMutilatedEdge
      (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) parent child = true)
      ((route.before ++ [route.endpoint]).map SeparationNode.observed) :=
  map_cut_directed graph query pivot.node _ route.consecutive (fun node member same =>
    pivot.activation_pivot_not_mem route (same ▸ member))

/-- Proper route vertices are open in the exact exchange given-set.  The
final conditioner is deliberately excluded, since it may be a conditioned
collider at a path return and must not be incorrectly treated as open. -/
private theorem route_open_of_not_endpoint {query : ConditionalKernelQuery S} {pivot collider : Fin S.count}
    (route : ConditionalColliderActivationRoute query pivot collider) (node : SeparationNode S)
    (member : node ∈ (route.before ++ [route.endpoint]).map SeparationNode.observed)
    (notEndpoint : node ≠ .observed route.endpoint) :
    ObservedGraph.blockedBy (NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton pivot))) node = false := by
  rcases List.mem_map.mp member with ⟨observed, observedMember, same⟩
  subst node
  rcases List.mem_append.mp observedMember with before | endpoint
  · change (query.action observed || NodeSet.diff query.condition (NodeSet.singleton pivot) observed) = false
    rw [route.action_free observed (List.mem_append.mpr (Or.inl before)), route.before_given_free observed before]
    rfl
  · exact False.elim (notEndpoint (congrArg SeparationNode.observed (List.mem_singleton.mp endpoint)))

private theorem consecutive_suffix {α : Type _} {relation : α -> α -> Prop}
    (before : List α) (node : α) (after : List α)
    (directed : Consecutive relation (before ++ node :: after)) : Consecutive relation (node :: after) := by
  have suffix := Consecutive.drop before.length (before ++ node :: after) directed
  simpa only [List.drop_append_length] using suffix

/-- The actual directed suffix to the other conditioner supplies activation
in the cut graph.  Only a propositional bounded-walk proof is extracted;
there is no route selected into data from existential reachability. -/
private theorem activated_of_suffix (graph : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (start : SeparationNode S) (endpoint : Fin S.count)
    (nodes : List (SeparationNode S)) (starts : nodes.head? = some start)
    (finishes : nodes.getLast? = some (.observed endpoint))
    (directed : Consecutive (fun parent child => graph.expandedMutilatedEdge m parent child = true) nodes)
    (selected : conditioned endpoint = true) : ColliderActivated graph m conditioned start := by
  have reachable := FiniteReachability.Reachable.of_consecutive _ _ starts finishes directed
  have bounded := FiniteReachability.boundedWalk_of_reachable SeparationNode.beq graph.separationNodes
    (graph.expandedMutilatedEdge m) SeparationNode.beq_eq_true_iff SeparationNode.mem_all reachable
  exact (graph.ancestorOf_eq_true_iff m conditioned start).mpr ⟨endpoint, selected, bounded⟩

private theorem colliderJoinBool_reverse_sides (graph : ObservedGraph S) (m : GraphMutilation S)
    (left right : List (SeparationNode S)) (middle : SeparationNode S) :
    colliderJoinBool graph m right.reverse middle left.reverse = colliderJoinBool graph m left middle right := by
  unfold colliderJoinBool
  rw [List.getLast?_reverse, head?_reverse_eq_getLast?]
  cases leftLast : left.getLast? <;> cases rightHead : right.head? <;>
    simp only [isColliderBool, Bool.and_comm]

/-- Restoring the singleton's outgoing arrows retains each cut-graph edge.
This is used only to read a cut-path collider as the same bar-graph collider
when requesting the existing activation-forest constructor. -/
private theorem bar_edge_of_cut_edge (graph : ObservedGraph S) (query : ConditionalKernelQuery S)
    (pivot : Fin S.count) (parent child : SeparationNode S)
    (edge : graph.expandedMutilatedEdge
      (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot)) parent child = true) :
    graph.expandedMutilatedEdge (GraphMutilation.bar query.action) parent child = true := by
  cases parent with
  | observed parent =>
      cases child with
      | observed child =>
          simp only [ObservedGraph.expandedMutilatedEdge, GraphMutilation.barUnderline, GraphMutilation.bar,
            NodeSet.empty, Bool.not_false, Bool.and_true, Bool.and_eq_true] at edge ⊢
          exact ⟨edge.1.1, edge.2⟩
      | latentPair _ _ => cases edge
  | latentPair _ _ => exact edge

/-! ## First-intersection certificates and contradiction to proved optimality -/

/-- Every cut-surviving activation/path intersection is its own collider,
for any retained pivot and its actual collider-normal path.  The route's
cut arrows, rather than latest-pivot maximality, supply the detour in the
exact comparison graph.  The cut-route constructor derives this premise
from actual cut-graph collider activity, without an avoidance flag.

Existential membership splits below stay in the final equality proposition
or contradiction.  The competing list is explicit; no path is chosen into
output data from propositional existence. -/
theorem ConditionalBackdoorPathNormalForm.activation_path_intersection_eq_collider_of_cut_route
    {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {pivot : Fin S.count}
    (normal : ConditionalBackdoorPathNormalForm graph query pivot)
    (before after : List (SeparationNode S)) (previous next : SeparationNode S) (collider : Fin S.count)
    (window : normal.cutPath.nodes = before ++ previous :: .observed collider :: next :: after)
    (isCollider : IsCollider graph (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot))
      previous (.observed collider) next)
    (route : ConditionalColliderActivationRoute query pivot collider)
    (cutDirected : Consecutive (fun parent child => graph.expandedMutilatedEdge
      (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot)) parent child = true)
      ((route.before ++ [route.endpoint]).map SeparationNode.observed))
    (node : Fin S.count) (onRoute : node ∈ route.before ++ [route.endpoint])
    (onPath : .observed node ∈ normal.cutPath.nodes) : node = collider := by
  by_cases same : node = collider
  · exact same
  · apply False.elim
    let m := GraphMutilation.barUnderline query.action (NodeSet.singleton pivot)
    let conditioned := NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton pivot))
    rcases List.head?_eq_some_iff.mp route.starts with ⟨tail, routeNodes⟩
    have inTail : node ∈ tail := by
      rw [routeNodes] at onRoute
      rcases List.mem_cons.mp onRoute with equal | later
      · exact False.elim (same equal)
      · exact later
    have inMappedTail : .observed node ∈ tail.map SeparationNode.observed := List.mem_map.mpr ⟨node, inTail, rfl⟩
    -- Search only after the source collider.  Its own permitted intersection
    -- must not be mistaken for a return; firstness excludes every detour
    -- vertex from the entire original path, not just from one side of it.
    cases intersection : firstSharedSeparation? (tail.map SeparationNode.observed) normal.cutPath.nodes with
    | none => exact firstSharedSeparation?_eq_none_disjoint intersection _ inMappedTail onPath
    | some returnedNode =>
        rcases firstSharedSeparation?_eq_some_split intersection with ⟨via, routeAfter, tailSplit, viaAvoids, returnedOnPath⟩
        have returnedInTail : returnedNode ∈ tail.map SeparationNode.observed := by
          rw [tailSplit]
          exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
        rcases List.mem_map.mp returnedInTail with ⟨returned, returnedInObservedTail, returnedIsObserved⟩
        subst returnedNode
        have fullSplit : (route.before ++ [route.endpoint]).map SeparationNode.observed =
            (.observed collider :: via) ++ .observed returned :: routeAfter := by
          rw [routeNodes, List.map_cons, tailSplit]
          rfl
        -- The route's real arrows are already certified in the exact outgoing
        -- cut used by the normal form's optimality proof.  A competitor in
        -- merely the restored bar graph would not suffice.
        have allSimple := nodup_map_observed route.simple
        have allFinishes : ((route.before ++ [route.endpoint]).map SeparationNode.observed).getLast? =
            some (.observed route.endpoint) := by
          simp only [List.getLast?_map, List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.map_some]
        have suffixFinishes := ObservedGraph.getLast?_suffix_append (fullSplit ▸ allFinishes)
        have suffixDirected := consecutive_suffix (.observed collider :: via) (.observed returned) routeAfter
          (fullSplit ▸ cutDirected)
        have bridgeDirected : Consecutive (fun parent child => graph.expandedMutilatedEdge m parent child = true)
            (.observed collider :: (via ++ [.observed returned])) := by
          simpa only [List.cons_append] using Consecutive.prefix_append (.observed collider :: via)
            (.observed returned) routeAfter (fullSplit ▸ cutDirected)
        have bridgeSimple : (.observed collider :: (via ++ [.observed returned])).Nodup := by
          simpa only [List.cons_append] using ObservedGraph.nodup_prefix_append (fullSplit ▸ allSimple)
        -- Only the proper prefix must be open.  The return may be the final
        -- conditioner and remain a collider; its directed suffix supplies
        -- activation instead of an unjustified return-openness premise.
        have openPrefix : forall vertex, vertex ∈ .observed collider :: via ->
            ObservedGraph.blockedBy conditioned vertex = false := by
          intro vertex member
          apply route_open_of_not_endpoint route vertex
          · rw [fullSplit]
            exact List.mem_append.mpr (Or.inl member)
          · intro equal
            have endpointInSuffix := List.mem_of_getLast? suffixFinishes
            exact (List.nodup_append.mp (fullSplit ▸ allSimple)).2.2 vertex member
              (.observed route.endpoint) endpointInSuffix equal
        have sourceOpen := openPrefix (.observed collider) (List.mem_cons.mpr (Or.inl rfl))
        have openVia : forall vertex, vertex ∈ via -> ObservedGraph.blockedBy conditioned vertex = false :=
          fun vertex member => openPrefix vertex (List.mem_cons.mpr (Or.inr member))
        have endpointSelected : conditioned route.endpoint = true := by
          have pivotFalse : NodeSet.singleton pivot route.endpoint = false := decide_eq_false route.endpoint_ne_pivot
          change (query.action route.endpoint || (query.condition route.endpoint && !(NodeSet.singleton pivot route.endpoint))) = true
          rw [route.endpoint_condition, pivotFalse]
          simp only [Bool.not_false, Bool.and_self, Bool.or_true]
        have activated := activated_of_suffix graph m conditioned (.observed returned) route.endpoint
          (.observed returned :: routeAfter) rfl suffixFinishes suffixDirected endpointSelected
        have later : observedColliderRank (.observed collider) < observedColliderRank (.observed returned) := by
          have ordered := Consecutive.mono (fun _ _ edge => mutilatedDirected_earlier S query.action edge)
            _ route.consecutive
          rw [routeNodes] at ordered
          exact ordered.fin_lt_of_mem_tail returned returnedInObservedTail
        let left := before ++ [previous]
        let right := next :: after
        have pathSplit : normal.cutPath.nodes = left ++ .observed collider :: right := by
          simpa only [left, right, List.append_assoc, List.singleton_append] using window
        have oldJoin : colliderJoinBool graph m left (.observed collider) right = true := by
          simpa only [colliderJoinBool, left, right, List.getLast?_append, List.getLast?_singleton,
            Option.some_or, List.head?_cons] using (IsCollider_iff_isColliderBool graph m previous (.observed collider) next).mp isCollider
        have returnedPart : .observed returned ∈ left ∨ .observed returned ∈ .observed collider :: right := by
          rw [pathSplit] at returnedOnPath
          exact List.mem_append.mp returnedOnPath
        -- The activation route always increases observed rank, but its
        -- return can lie on either side of the source along the active path.
        -- Reversal transfers proved optimality; it does not select a new path.
        rcases returnedPart with beforeCollider | afterCollider
        · rcases List.mem_iff_append.mp beforeCollider with ⟨leftBefore, between, leftSplit⟩
          have reverseSplit : normal.cutPath.reverse.nodes = right.reverse ++ .observed collider ::
              (between.reverse ++ .observed returned :: leftBefore.reverse) := by
            change normal.cutPath.nodes.reverse = _
            rw [pathSplit, leftSplit]
            simp only [List.reverse_append, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
          have reverseJoin : colliderJoinBool graph m right.reverse (.observed collider)
              (between.reverse ++ .observed returned :: leftBefore.reverse) = true := by
            have reversed := colliderJoinBool_reverse_sides graph m left right (.observed collider)
            rw [leftSplit] at reversed
            rw [leftSplit] at oldJoin
            simpa only [List.reverse_append, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using reversed.trans oldJoin
          exact normal.cutPath.noBackwardColliderDetour normal.score_minimal right.reverse between.reverse via leftBefore.reverse
            (.observed collider) (.observed returned) reverseSplit reverseJoin bridgeDirected bridgeSimple
            sourceOpen openVia activated
            (fun vertex member inReverse => viaAvoids vertex member (List.mem_reverse.mp inReverse)) later
        · rcases List.mem_cons.mp afterCollider with equal | inRight
          · have same : returned = collider := SeparationNode.observed.inj equal
            rw [same] at later
            exact Nat.lt_irrefl _ later
          · rcases List.mem_iff_append.mp inRight with ⟨between, rightAfter, rightSplit⟩
            have forwardSplit : normal.cutPath.nodes = left ++ .observed collider ::
                (between ++ .observed returned :: rightAfter) := by rw [pathSplit, rightSplit]
            have forwardJoin : colliderJoinBool graph m left (.observed collider)
                (between ++ .observed returned :: rightAfter) = true := by rw [← rightSplit]; exact oldJoin
            exact normal.cutPath.noForwardColliderDetour normal.score_minimal left between via rightAfter
              (.observed collider) (.observed returned) forwardSplit forwardJoin bridgeDirected bridgeSimple
              sourceOpen openVia activated (fun vertex member inPath => viaAvoids vertex member inPath) later

/-- The actual cut-route interface gives normalized-path avoidance
without any latest-pivot argument.  Its arrows and pivot freedom come from
the cut-graph activity constructor, not a supplied forest-disjointness flag. -/
theorem ConditionalBackdoorPathNormalForm.cut_activation_path_intersection_eq_collider
    {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {pivot : Fin S.count}
    (normal : ConditionalBackdoorPathNormalForm graph query pivot)
    (before after : List (SeparationNode S)) (previous next : SeparationNode S) (collider : Fin S.count)
    (window : normal.cutPath.nodes = before ++ previous :: .observed collider :: next :: after)
    (isCollider : IsCollider graph (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot))
      previous (.observed collider) next)
    (route : ConditionalCutColliderActivationRoute graph query pivot collider)
    (node : Fin S.count) (onRoute : node ∈ route.before ++ [route.endpoint])
    (onPath : .observed node ∈ normal.cutPath.nodes) : node = collider :=
  normal.activation_path_intersection_eq_collider_of_cut_route before after previous next collider window isCollider
    route.toConditionalColliderActivationRoute route.mapped_cut_consecutive node onRoute onPath

/-- Preserve the original latest-pivot API.  Maximality proves that its
bar-graph route survives the cut, after which the more general avoidance
theorem applies.  Existing common-forest clients keep the same interface. -/
theorem ConditionalBackdoorPathNormalForm.activation_path_intersection_eq_collider
    {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {hedgeSource : Fin S.count}
    (pivot : LatestConditionalPivot graph query hedgeSource)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (before after : List (SeparationNode S)) (previous next : SeparationNode S) (collider : Fin S.count)
    (window : normal.cutPath.nodes = before ++ previous :: .observed collider :: next :: after)
    (isCollider : IsCollider graph (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node))
      previous (.observed collider) next)
    (route : ConditionalColliderActivationRoute query pivot.node collider)
    (node : Fin S.count) (onRoute : node ∈ route.before ++ [route.endpoint])
    (onPath : .observed node ∈ normal.cutPath.nodes) : node = collider :=
  normal.activation_path_intersection_eq_collider_of_cut_route before after previous next collider window isCollider
    route (route_cut_directed pivot route) node onRoute onPath

/-! ## The common activation policy supplies routes without new readiness flags -/

namespace ConditionalColliderActivationForest

open HedgeChannelInstallation

private theorem path_nodes_eq_dropLast {query : ConditionalKernelQuery S} {pivot : Fin S.count}
    (forest : ConditionalColliderActivationForest query pivot) (collider : Fin S.count)
    (selected : forest.nodes collider = true) :
    (forest.path collider selected).nodes = (forest.path collider selected).nodes.dropLast ++
      [(forest.path collider selected).endpoint] := by
  let path := forest.path collider selected
  have nonempty : path.nodes ≠ [] := by
    intro empty
    have starts := path.starts
    rw [empty] at starts
    cases starts
  have lastEq : path.nodes.getLast nonempty = path.endpoint :=
    Option.some.inj ((List.getLast?_eq_some_getLast nonempty).symm.trans path.finishes)
  have full := (List.dropLast_concat_getLast nonempty).symm
  rw [lastEq] at full
  exact full

/-- Reinterpret the actual common-policy trace as a certified activation
route.  Its preceding list is the computed `dropLast`, not a list chosen from
the proposition that an activation route exists.  Its conditioned endpoint,
pivot avoidance, action freedom, and preceding condition freedom are all
theorems of the forest policy and its complete path. -/
def activationRoute {query : ConditionalKernelQuery S} {pivot : Fin S.count}
    (forest : ConditionalColliderActivationForest query pivot) (collider : Fin S.count)
    (selected : forest.nodes collider = true) : ConditionalColliderActivationRoute query pivot collider := by
  let path := forest.path collider selected
  have shape := path_nodes_eq_dropLast forest collider selected
  have endpointFacts := forest.path_endpoint_condition collider selected
  refine {
    before := path.nodes.dropLast
    endpoint := path.endpoint
    endpoint_condition := endpointFacts.1
    endpoint_ne_pivot := endpointFacts.2
    starts := ?_
    simple := ?_
    consecutive := ?_
    action_free := ?_
    before_given_free := ?_
  }
  · rw [← shape]
    exact path.starts
  · rw [← shape]
    exact path.simple
  · rw [← shape]
    apply Consecutive.mono (fun parent child edge => ?_) path.nodes path.consecutive
    change forest.successor parent = some child at edge
    have actual := childWellFormed_edge forest.nodes forest.successor forest.wellFormed edge
    have free := forest.action_free child actual.2.1
    simpa only [mutilatedDirected, free, Bool.false_eq_true, if_false] using actual.2.2
  · intro node member
    rw [← shape] at member
    exact forest.action_free node (path.inside node member)
  · intro node member
    have nodeInPath : node ∈ path.nodes := by
      rw [shape]
      exact List.mem_append.mpr (Or.inl member)
    have notEndpoint : node ≠ path.endpoint := by
      intro same
      exact (List.nodup_append.mp (shape ▸ path.simple)).2.2 node member path.endpoint
        (List.mem_singleton.mpr rfl) same
    have free := forest.path_before_condition_free collider selected node nodeInPath notEndpoint
    change (query.condition node && !(NodeSet.singleton pivot node)) = false
    rw [free]
    rfl

/-- The activation-route adapter retains the complete policy path exactly.
This lets the universal route-avoidance theorem apply directly to common
forest paths, without another path search or a separate route witness. -/
theorem activationRoute_nodes {query : ConditionalKernelQuery S} {pivot : Fin S.count}
    (forest : ConditionalColliderActivationForest query pivot) (collider : Fin S.count)
    (selected : forest.nodes collider = true) :
    (forest.activationRoute collider selected).before ++ [(forest.activationRoute collider selected).endpoint] =
      (forest.path collider selected).nodes := by
  change (forest.path collider selected).nodes.dropLast ++ [(forest.path collider selected).endpoint] = _
  exact (path_nodes_eq_dropLast forest collider selected).symm

end ConditionalColliderActivationForest

namespace ConditionalBackdoorPathNormalForm

open HedgeChannelInstallation

/-- An actual collider window of the normal form supplies its complete
common-policy activation path.  Its cut-graph parents survive restoration,
so the existing bar-graph activation constructor supplies forest coverage.
No selected-collider or independently activated-source flag is requested. -/
def activationForestPath {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {source : Fin S.count}
    (pivot : LatestConditionalPivot graph query source)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (forest : ConditionalColliderActivationForest query pivot.node)
    (before after : List (SeparationNode S)) (previous next : SeparationNode S) (collider : Fin S.count)
    (window : normal.cutPath.nodes = before ++ previous :: .observed collider :: next :: after)
    (isCollider : IsCollider graph (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node))
      previous (.observed collider) next) : SuccessorPath forest.nodes forest.successor collider :=
  forest.pathOfBackdoorCollider (normal.backdoor pivot.selected) before after previous next collider
    ((normal.backdoor_nodes pivot.selected).trans window)
    ⟨bar_edge_of_cut_edge graph query pivot.node _ _ isCollider.1,
      bar_edge_of_cut_edge graph query pivot.node _ _ isCollider.2⟩

/-- Every selected collider's actual common-policy activation path meets
the normalized path only at that collider.  This is a theorem of the latest
pivot, path normal form, and common forest, not an interaction-selection flag.
The larger auxiliary forest domain may still contain irrelevant ancestors;
no disjointness of that entire domain is asserted. -/
theorem activation_forest_path_intersection_eq_collider
    {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {source : Fin S.count}
    (pivot : LatestConditionalPivot graph query source)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (forest : ConditionalColliderActivationForest query pivot.node)
    (before after : List (SeparationNode S)) (previous next : SeparationNode S) (collider : Fin S.count)
    (window : normal.cutPath.nodes = before ++ previous :: .observed collider :: next :: after)
    (isCollider : IsCollider graph (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node))
      previous (.observed collider) next)
    (node : Fin S.count)
    (onRoute : node ∈ (normal.activationForestPath pivot forest before after previous next collider window isCollider).nodes)
    (onPath : .observed node ∈ normal.cutPath.nodes) : node = collider := by
  let backdoor := normal.backdoor pivot.selected
  have restoredWindow := (normal.backdoor_nodes pivot.selected).trans window
  have restoredCollider : IsCollider graph (GraphMutilation.bar query.action) previous (.observed collider) next :=
    ⟨bar_edge_of_cut_edge graph query pivot.node _ _ isCollider.1,
      bar_edge_of_cut_edge graph query pivot.node _ _ isCollider.2⟩
  let selected := forest.contains_activation collider
    (backdoor.colliderActivationRoute before after previous next collider restoredWindow restoredCollider)
  apply normal.activation_path_intersection_eq_collider pivot before after previous next collider window isCollider
    (forest.activationRoute collider selected) node
  · rw [forest.activationRoute_nodes]
    exact onRoute
  · exact onPath

end ConditionalBackdoorPathNormalForm

end Causality
end Thesis
