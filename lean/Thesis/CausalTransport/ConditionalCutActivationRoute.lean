import Thesis.CausalTransport.ConditionalFailureActivation
import Thesis.CausalTransport.ConditionalFailurePathNormalization

namespace Thesis
namespace Causality

open PathSpecification

/-!
# Actual collider activations in the exact singleton outgoing-cut graph

The older activation search works in the larger incoming action cut and
can pass through the omitted pivot.  Latest-pivot maximality then proves
that those routes survive the singleton outgoing cut.  Here the route is
searched in that exact cut from the start, using the actual collider's
cut-graph activity certificate.  No latest-pivot assumption is required.

The finite observed search reuses the existing verified route constructor
on a mechanically outgoing-masked signature.  Its alphabet and node indices
are literally unchanged, and the temporary signature is used only to compute
graph routes.  Model installation still uses the original graph and inputs.
Every returned arrow is proved equal to a real original expanded cut arrow.
Truncation retains the first actual other conditioner, including a zero-edge
activation at an already-conditioned collider.

The resulting route avoids the pivot because that vertex has no outgoing
cut arrow and is not the endpoint.  Its entire proper prefix is therefore
unconditioned in the original query.  These are proved route properties,
not additional avoidance flags.  General normalized-path avoidance can now
use these routes without selecting a latest reachable conditioning vertex.
`ConditionalCutActivationForest` separately constructs one common merged
cut policy using the same search signature.  Independent routes must not
be installed as duplicate rows; trace selection and parity installation
are different tasks from the individual route constructor here.
-/

variable {S : ObservedSignature.{0}}

namespace ConditionalCutActivationRouting

/-- The same observed alphabet and order, with only the singleton pivot's
outgoing arrows removed.  This temporary signature computes graph routes;
it is not a replacement for the original model's signature or root inputs. -/
def searchSignature (pivot : Fin S.count) : ObservedSignature where
  count := S.count
  Value := S.Value
  valueEnumeration := S.valueEnumeration
  value_complete := S.value_complete
  value_nodup := S.value_nodup
  defaultValue := S.defaultValue
  valueDecidableEq := S.valueDecidableEq
  directed := fun parent child => S.directed parent child && !(NodeSet.singleton pivot parent)
  directed_earlier := by
    intro parent child edge
    exact S.directed_earlier (Bool.and_eq_true_iff.mp edge).1

/-- The finite observed search edge in the exact exchange cut.  Incoming
action cuts and the pivot outgoing cut are both retained. -/
def observedEdge (query : ConditionalKernelQuery S) (pivot : Fin S.count) : Fin S.count -> Fin S.count -> Bool :=
  mutilatedDirected (searchSignature pivot) query.action

/-- The search's arrow is the actual original expanded cut arrow between
these observed endpoints, not an unrelated masked graph relation. -/
theorem observedEdge_eq_expanded (graph : ObservedGraph S) (query : ConditionalKernelQuery S)
    (pivot parent child : Fin S.count) : observedEdge query pivot parent child =
      graph.expandedMutilatedEdge (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot))
        (.observed parent) (.observed child) := by
  change (if query.action child = true then false else (S.directed parent child && !(NodeSet.singleton pivot parent))) =
    (S.directed parent child && !(NodeSet.singleton pivot parent) && !(query.action child))
  cases query.action child <;> cases NodeSet.singleton pivot parent <;> cases S.directed parent child <;> rfl

/-- Every actual cut-search arrow remains a genuine arrow of the original
incoming action cut.  This preserves the older activation-route interface. -/
theorem observedEdge_implies_action_edge (query : ConditionalKernelQuery S) (pivot parent child : Fin S.count)
    (edge : observedEdge query pivot parent child = true) : mutilatedDirected S query.action parent child = true := by
  change (if query.action child = true then false else (S.directed parent child && !(NodeSet.singleton pivot parent))) = true at edge
  change (if query.action child = true then false else S.directed parent child) = true
  cases acted : query.action child with
  | true => rw [acted] at edge; change false = true at edge; cases edge
  | false =>
      rw [acted] at edge
      change (S.directed parent child && !(NodeSet.singleton pivot parent)) = true at edge
      change S.directed parent child = true
      exact (Bool.and_eq_true_iff.mp edge).1

private theorem observedReachable_of_expandedWalk (graph : ObservedGraph S) (query : ConditionalKernelQuery S)
    (pivot : Fin S.count) {length : Nat} {start finish : SeparationNode S}
    (walk : FiniteReachability.ExactWalk
      (graph.expandedMutilatedEdge (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot))) length start finish)
    (source target : Fin S.count) (starts : start = .observed source) (finishes : finish = .observed target) :
    FiniteReachability.Reachable (observedEdge query pivot) source target := by
  induction walk generalizing source with
  | refl node =>
      have same : source = target := SeparationNode.observed.inj (starts.symm.trans finishes)
      subst target
      exact FiniteReachability.Reachable.refl _ source
  | @step length start middle finish first rest inductionHypothesis =>
      subst start
      cases middle with
      | latentPair left right => cases first
      | observed child =>
          have edge : observedEdge query pivot source child = true := by
            rw [observedEdge_eq_expanded graph]
            exact first
          exact FiniteReachability.Reachable.prepend edge (inductionHypothesis child rfl finishes)

private theorem within_of_expandedReachable (graph : ObservedGraph S) (query : ConditionalKernelQuery S)
    (pivot source target : Fin S.count)
    (reachable : graph.expandedReachable (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot))
      (.observed source) (.observed target) = true) :
    FiniteReachability.within finBeq (NodeSet.enumerated S) (observedEdge query pivot) S.count source target = true := by
  rcases (graph.expandedReachable_eq_true_iff _ _ _).mp reachable with ⟨length, _bound, ⟨walk⟩⟩
  have observed := observedReachable_of_expandedWalk graph query pivot walk source target rfl rfl
  have bounded := FiniteReachability.boundedWalk_of_reachable finBeq (NodeSet.enumerated S)
    (observedEdge query pivot) finBeq_eq_true_iff (NodeSet.mem_enumerated S) observed
  rw [NodeSet.length_enumerated] at bounded
  exact (FiniteReachability.within_eq_true_iff_boundedWalk finBeq (NodeSet.enumerated S)
    (observedEdge query pivot) finBeq_eq_true_iff (NodeSet.mem_enumerated S) _ _ _).mpr bounded

end ConditionalCutActivationRouting

/-- A real activation route whose arrows all survive the exact outgoing
cut.  The original-route fields retain the unchanged query and alphabet;
cut survival is constructed from cut-graph activity below, not from maximality. -/
structure ConditionalCutColliderActivationRoute (graph : ObservedGraph S) (query : ConditionalKernelQuery S)
    (pivot collider : Fin S.count) extends ConditionalColliderActivationRoute query pivot collider where
  cut_consecutive : Consecutive (fun parent child => graph.expandedMutilatedEdge
    (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot)) (.observed parent) (.observed child) = true)
      (before ++ [endpoint])

namespace ConditionalCutColliderActivationRoute

open ConditionalCutActivationRouting

/-- Construct actual cut arrows from the collider's cut-graph ancestry
answer.  Observed finite search and first-target truncation supply all route
data; no representative is selected from propositional reachability. -/
def ofAncestor (graph : ObservedGraph S) (query : ConditionalKernelQuery S) (pivot collider : Fin S.count)
    (collider_action_free : query.action collider = false)
    (activated : graph.ancestorOf (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot))
      (NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton pivot))) (.observed collider) = true) :
    ConditionalCutColliderActivationRoute graph query pivot collider := by
  let targets := NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton pivot))
  let candidates := NodeSet.enumerated S
  let accepts := fun target => targets target && FiniteReachability.within finBeq candidates (observedEdge query pivot) S.count collider target
  have found : candidates.any accepts = true := by
    rcases (graph.ancestorOf_eq_true_iff _ targets (.observed collider)).mp activated with ⟨endpoint, selected, bounded⟩
    have expanded := (graph.expandedReachable_eq_true_iff _ _ _).mpr bounded
    have observed := within_of_expandedReachable graph query pivot collider endpoint expanded
    exact List.any_eq_true.mpr ⟨endpoint, NodeSet.mem_enumerated S endpoint, Bool.and_eq_true_iff.mpr ⟨selected, observed⟩⟩
  let target := listFirstAny candidates accepts found
  have targetParts := Bool.and_eq_true_iff.mp (listFirstAny_pred candidates accepts found)
  let original := mutilatedDirectedRoute (S := searchSignature pivot) query.action target S.count collider targetParts.2
  have originalSpec := mutilatedDirectedRoute_spec (S := searchSignature pivot) query.action target S.count collider targetParts.2
  let first := ConditionalActivationRouting.firstTargetPrefix targets target targetParts.1 original originalSpec.2.1
  have prefixStarts : (first.before ++ [first.target]).head? = some collider := by
    have starts := originalSpec.1
    change original.head? = some collider at starts
    rw [first.split] at starts
    cases beforeEq : first.before with
    | nil => simpa only [beforeEq, List.nil_append, List.head?_cons] using starts
    | cons head tail => simpa only [beforeEq, List.cons_append, List.head?_cons] using starts
  have prefixCut : Consecutive (fun parent child => observedEdge query pivot parent child = true) (first.before ++ [first.target]) :=
    Consecutive.prefix_append first.before first.target first.after (first.split ▸ originalSpec.2.2)
  have prefixConsecutive : Consecutive (fun parent child => mutilatedDirected S query.action parent child = true)
      (first.before ++ [first.target]) := Consecutive.mono (observedEdge_implies_action_edge query pivot) _ prefixCut
  have prefixFree : forall node, node ∈ first.before ++ [first.target] -> query.action node = false :=
    consecutive_mutilatedDirected_avoids_action query.action _ collider prefixStarts collider_action_free prefixConsecutive
  have endpointFree := prefixFree first.target (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
  have endpointGiven : query.condition first.target = true ∧ NodeSet.singleton pivot first.target = false := by
    have selected := first.selected
    change (query.action first.target || (query.condition first.target && !(NodeSet.singleton pivot first.target))) = true at selected
    simpa only [endpointFree, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] using selected
  refine {
    before := first.before
    endpoint := first.target
    endpoint_condition := endpointGiven.1
    endpoint_ne_pivot := ?_
    starts := prefixStarts
    simple := by
      apply Consecutive.nodup_of_fin_lt
      exact Consecutive.mono (fun _ _ edge => mutilatedDirected_earlier S query.action edge) _ prefixConsecutive
    consecutive := prefixConsecutive
    action_free := prefixFree
    before_given_free := ?_
    cut_consecutive := Consecutive.mono (fun parent child edge =>
      (observedEdge_eq_expanded graph query pivot parent child).symm ▸ edge) _ prefixCut
  }
  · intro same
    have singletonTrue := (NodeSet.singleton_eq_true_iff pivot pivot).mpr rfl
    rw [same] at endpointGiven
    exact Bool.false_ne_true (endpointGiven.2.symm.trans singletonTrue)
  · intro node member
    have unselected := first.before_free node member
    change (query.action node || NodeSet.diff query.condition (NodeSet.singleton pivot) node) = false at unselected
    exact (Bool.or_eq_false_iff.mp unselected).2

/-- Map the route's actual observed arrows into the original expanded
cut graph.  This is precisely the directed-detour relation needed by the
normal-form avoidance theorem; the list itself is unchanged. -/
theorem mapped_cut_consecutive {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {pivot collider : Fin S.count}
    (route : ConditionalCutColliderActivationRoute graph query pivot collider) :
    Consecutive (fun parent child => graph.expandedMutilatedEdge
      (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot)) parent child = true)
      ((route.before ++ [route.endpoint]).map SeparationNode.observed) :=
  Consecutive.map SeparationNode.observed (fun _ _ edge => edge) _ route.cut_consecutive

/-- The pivot cannot occur anywhere on the returned cut route.  An
internal occurrence would need a forbidden outgoing arrow, while the
endpoint is already a proved different original conditioner. -/
theorem pivot_not_mem {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {pivot collider : Fin S.count}
    (route : ConditionalCutColliderActivationRoute graph query pivot collider) : pivot ∉ route.before ++ [route.endpoint] := by
  intro member
  have finishes : (route.before ++ [route.endpoint]).getLast? = some route.endpoint := by
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
  have notLast : (route.before ++ [route.endpoint]).getLast? ≠ some pivot := by
    intro same
    exact route.endpoint_ne_pivot (Option.some.inj (finishes.symm.trans same))
  have found := routeSuccessor_isSome_of_mem_of_not_last _ pivot route.simple member notLast
  cases next : routeSuccessor (route.before ++ [route.endpoint]) pivot with
  | none => rw [next] at found; cases found
  | some child =>
      have edge := routeSuccessor_rel_of_eq_some (fun parent child => graph.expandedMutilatedEdge
        (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot)) (.observed parent) (.observed child) = true)
        _ pivot child route.cut_consecutive next
      have self := (NodeSet.singleton_eq_true_iff pivot pivot).mpr rfl
      simp only [ObservedGraph.expandedMutilatedEdge, GraphMutilation.barUnderline, self,
        Bool.not_true, Bool.and_false, Bool.false_and] at edge
      cases edge

/-- Every proper route vertex is unconditioned in the unchanged original
query.  The exchange mask alone omitted the pivot, but the proved cut-route
avoidance now rules out that exception as well. -/
theorem before_condition_free {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {pivot collider : Fin S.count}
    (route : ConditionalCutColliderActivationRoute graph query pivot collider) (node : Fin S.count)
    (member : node ∈ route.before) : query.condition node = false := by
  have different : node ≠ pivot := by
    intro same
    have inRoute : node ∈ route.before ++ [route.endpoint] := List.mem_append.mpr (Or.inl member)
    have transported : pivot ∈ route.before ++ [route.endpoint] :=
      Eq.mp (congrArg (fun child => child ∈ route.before ++ [route.endpoint]) same) inRoute
    exact route.pivot_not_mem transported
  have absent : NodeSet.singleton pivot node = false := decide_eq_false different
  have free := route.before_given_free node member
  change (query.condition node && !(NodeSet.singleton pivot node)) = false at free
  simpa only [absent, Bool.not_false, Bool.and_true] using free

end ConditionalCutColliderActivationRoute

/-- An actual collider window of any retained-pivot normal form supplies
its real cut-graph activation route.  Activity and path action freedom are
derived here; no latest-pivot or independent activation flag is supplied. -/
def ConditionalBackdoorPathNormalForm.cutColliderActivationRoute
    {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {pivot : Fin S.count}
    (normal : ConditionalBackdoorPathNormalForm graph query pivot) (selected : query.condition pivot = true)
    (before after : List (SeparationNode S)) (previous next : SeparationNode S) (collider : Fin S.count)
    (window : normal.cutPath.nodes = before ++ previous :: .observed collider :: next :: after)
    (isCollider : IsCollider graph (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot))
      previous (.observed collider) next) : ConditionalCutColliderActivationRoute graph query pivot collider := by
  have active := InternalTriplesActive.triple_of_append before after previous (.observed collider) next
    (window ▸ normal.cutPath.internal_active)
  have activated : graph.ancestorOf (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot))
      (NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton pivot))) (.observed collider) = true := by
    rcases active with actual | nonCollider
    · exact actual.2
    · exact False.elim (nonCollider.1 isCollider)
  have member : .observed collider ∈ (normal.backdoor selected).path.nodes := by
    rw [normal.backdoor_nodes selected, window]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
  exact .ofAncestor graph query pivot collider ((normal.backdoor selected).action_false_of_mem collider member) activated

end Causality
end Thesis
