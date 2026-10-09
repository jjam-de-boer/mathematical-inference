import Thesis.CausalTransport.ConditionalFailurePaths

namespace Thesis
namespace Causality

/-!
# Actual activation routes for irreducible conditional back-door colliders

An active collider carries a Boolean ancestor certificate.  The conditional
countermodel argument needs more: the actual observed arrows carrying that
activation to a remaining conditioner.  This module obtains those arrows by
the existing finite route search, rather than by choosing a representative
from the propositional ancestry theorem.

The incoming action cut is retained throughout.  Starting at an observed
collider, a directed walk cannot enter a latent root or an action vertex.
Consequently its activating endpoint belongs to the *other* conditioners,
not the action set or the conditioner at which the back-door path starts.
We stop at the first such endpoint.  Every preceding vertex is outside the
exchange test's given-set, and the signature's topological order makes the
returned route simple.  That given-set omits the back-door pivot itself:
passing through that pivot is not silently ruled out by this construction.

These facts are graph ingredients, not yet a conditional countermodel.  In
particular, activation routes may meet each other, the active path, or the
hedge's small forest.  No disjointness or parity conservation at those
intersections is assumed here; those remain obligations of the general
graph-to-parity construction.
-/

open PathSpecification

variable {S : ObservedSignature.{0}}

/-! ## The expanded ancestry test retains an observed directed route -/

/-- Project an expanded directed walk with observed endpoints to observed
reachability.  All eliminations in this lemma remain in `Prop`: the executable
search below, not this existence proof, will supply the route data.  An
observed vertex cannot have a latent vertex as its next directed successor. -/
private theorem observedReachable_of_expandedWalk (graph : ObservedGraph S)
    (action : NodeSet S) {length : Nat} {start finish : SeparationNode S}
    (walk : FiniteReachability.ExactWalk
      (graph.expandedMutilatedEdge (GraphMutilation.bar action)) length start finish)
    (source target : Fin S.count) (starts : start = .observed source)
    (finishes : finish = .observed target) :
    FiniteReachability.Reachable (mutilatedDirected S action) source target := by
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
          have parts : S.directed source child = true ∧ action child = false := by
            simpa only [ObservedGraph.expandedMutilatedEdge, GraphMutilation.bar,
              NodeSet.empty, Bool.not_false, Bool.and_true, Bool.and_eq_true,
              Bool.not_eq_true'] using first
          have observedEdge : mutilatedDirected S action source child = true := by
            simp only [mutilatedDirected, parts.2, Bool.false_eq_true, if_false]
            exact parts.1
          exact FiniteReachability.Reachable.prepend observedEdge
            (inductionHypothesis child rfl finishes)

/-- An expanded observed-to-observed reachability answer also drives the
existing observed route search.  The finite bounded-walk theorem changes the
alphabet and fuel bound constructively; it does not select an existential
walk into `Type`. -/
private theorem observedWithin_of_expandedReachable (graph : ObservedGraph S)
    (action : NodeSet S) (source target : Fin S.count)
    (reachable : graph.expandedReachable (GraphMutilation.bar action)
      (.observed source) (.observed target) = true) :
    FiniteReachability.within finBeq (NodeSet.enumerated S)
      (mutilatedDirected S action) S.count source target = true := by
  rcases (graph.expandedReachable_eq_true_iff _ _ _).mp reachable with
    ⟨length, _bound, ⟨walk⟩⟩
  have observed := observedReachable_of_expandedWalk graph action walk source target rfl rfl
  have bounded := FiniteReachability.boundedWalk_of_reachable finBeq
    (NodeSet.enumerated S) (mutilatedDirected S action) finBeq_eq_true_iff
    (NodeSet.mem_enumerated S) observed
  rw [NodeSet.length_enumerated] at bounded
  exact (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
    (NodeSet.enumerated S) (mutilatedDirected S action) finBeq_eq_true_iff
    (NodeSet.mem_enumerated S) S.count source target).mpr bounded

/-! ## Stop at the first selected vertex, without choosing from existence -/

/-- A data-level split at the first selected vertex.  The preceding list is
allowed to be empty, which is essential when a collider is itself conditioned.
The suffix is retained only to certify that this is a prefix of the actual
searched route, not an independently supplied path. -/
private structure FirstTargetPrefix (targets : NodeSet S) (original : List (Fin S.count)) where
  before : List (Fin S.count)
  target : Fin S.count
  after : List (Fin S.count)
  split : original = before ++ target :: after
  selected : targets target = true
  before_free : forall node, node ∈ before -> targets node = false

/-- Scan a route ending at a selected vertex and return its first selected
vertex.  The recursion inspects only the displayed list and Boolean mask;
the endpoint proof rules out an empty unsuccessful suffix. -/
private def firstTargetPrefix (targets : NodeSet S) (endpoint : Fin S.count)
    (selected : targets endpoint = true) :
    (nodes : List (Fin S.count)) -> nodes.getLast? = some endpoint ->
      FirstTargetPrefix targets nodes
  | [], finishes => by cases finishes
  | head :: tail, finishes => by
      cases atHead : targets head with
      | true => exact ⟨[], head, tail, rfl, atHead, fun _ member => by cases member⟩
      | false =>
          cases tail with
          | nil =>
              have same : head = endpoint := Option.some.inj finishes
              subst endpoint
              exact False.elim (Bool.false_ne_true (atHead.symm.trans selected))
          | cons next rest =>
              let found := firstTargetPrefix targets endpoint selected (next :: rest) finishes
              refine ⟨head :: found.before, found.target, found.after, ?_, found.selected, ?_⟩
              · simpa only [List.cons_append] using congrArg (List.cons head) found.split
              · intro node member
                rcases List.mem_cons.mp member with same | later
                · subst node
                  exact atHead
                · exact found.before_free node later

/-! ## Conditional activation data with the exact exchange-test given-set -/

/-- A simple directed collider-activation branch in the action-cut graph.
Its vertices are `before ++ [endpoint]`: only the final vertex belongs to the
other conditioners.  The zero-edge branch has `before = []` and starts at a
conditioned collider.  The omitted pivot may occur earlier; no avoidance of
that pivot, the small forest, or other activation branches is assumed. -/
structure ConditionalColliderActivationRoute (query : ConditionalKernelQuery S)
    (pivot collider : Fin S.count) where
  before : List (Fin S.count)
  endpoint : Fin S.count
  endpoint_condition : query.condition endpoint = true
  endpoint_ne_pivot : endpoint ≠ pivot
  starts : (before ++ [endpoint]).head? = some collider
  simple : (before ++ [endpoint]).Nodup
  consecutive : Consecutive (fun parent child =>
    mutilatedDirected S query.action parent child = true) (before ++ [endpoint])
  action_free : forall node, node ∈ before ++ [endpoint] -> query.action node = false
  before_given_free : forall node, node ∈ before ->
    NodeSet.diff query.condition (NodeSet.singleton pivot) node = false

/-- Return actual arrows from a collider's exact exchange-test ancestry
certificate.  The source is action-free; the incoming cut then excludes all
action destinations, including the searched target.  Truncation at the first
selected vertex removes any earlier *other* conditioner without adding a
readiness assumption.  The omitted pivot is deliberately not treated as
conditioned by this exchange test. -/
def ConditionalColliderActivationRoute.ofAncestor (graph : ObservedGraph S)
    (query : ConditionalKernelQuery S) (pivot collider : Fin S.count)
    (collider_action_free : query.action collider = false)
    (activated : graph.ancestorOf (GraphMutilation.bar query.action)
      (NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton pivot)))
      (.observed collider) = true) :
    ConditionalColliderActivationRoute query pivot collider := by
  let targets := NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton pivot))
  let candidates := NodeSet.enumerated S
  -- Once the source is observed, directed successors remain observed.  Search
  -- this smaller alphabet instead of repeatedly expanding all latent-pair
  -- vertices during executable target selection.  The ancestry proof is used
  -- only to certify that the observed search succeeds.
  let accepts := fun target => targets target && FiniteReachability.within finBeq candidates
    (mutilatedDirected S query.action) S.count collider target
  have found : candidates.any accepts = true := by
    rcases (graph.ancestorOf_eq_true_iff _ targets (.observed collider)).mp activated with
      ⟨endpoint, selected, bounded⟩
    have expanded := (graph.expandedReachable_eq_true_iff _ _ _).mpr bounded
    have observed := observedWithin_of_expandedReachable graph query.action collider endpoint expanded
    exact List.any_eq_true.mpr ⟨endpoint, NodeSet.mem_enumerated S endpoint,
      Bool.and_eq_true_iff.mpr ⟨selected, observed⟩⟩
  let target := listFirstAny candidates accepts found
  have targetParts := Bool.and_eq_true_iff.mp (listFirstAny_pred candidates accepts found)
  have reaches := targetParts.2
  let original := mutilatedDirectedRoute query.action target S.count collider reaches
  have originalSpec := mutilatedDirectedRoute_spec query.action target S.count collider reaches
  let first := firstTargetPrefix targets target targetParts.1 original originalSpec.2.1
  have prefixStarts : (first.before ++ [first.target]).head? = some collider := by
    have starts := originalSpec.1
    change original.head? = some collider at starts
    rw [first.split] at starts
    cases beforeEq : first.before with
    | nil => simpa only [beforeEq, List.nil_append, List.head?_cons] using starts
    | cons head tail => simpa only [beforeEq, List.cons_append, List.head?_cons] using starts
  have prefixConsecutive : Consecutive (fun parent child =>
      mutilatedDirected S query.action parent child = true) (first.before ++ [first.target]) :=
    Consecutive.prefix_append first.before first.target first.after (first.split ▸ originalSpec.2.2)
  have prefixFree : forall node, node ∈ first.before ++ [first.target] -> query.action node = false := by
    apply consecutive_mutilatedDirected_avoids_action query.action _ collider prefixStarts
      collider_action_free prefixConsecutive
  have endpointFree := prefixFree first.target (List.mem_append.mpr (Or.inr (by simp only [List.mem_singleton])))
  have endpointGiven : query.condition first.target = true ∧
      NodeSet.singleton pivot first.target = false := by
    have selected := first.selected
    change (query.action first.target ||
      (query.condition first.target && !(NodeSet.singleton pivot first.target))) = true at selected
    simpa only [endpointFree, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] using selected
  have earlierFree : forall node, node ∈ first.before ->
      NodeSet.diff query.condition (NodeSet.singleton pivot) node = false := by
    intro node member
    have unselected := first.before_free node member
    change (query.action node || NodeSet.diff query.condition (NodeSet.singleton pivot) node) = false at unselected
    exact (Bool.or_eq_false_iff.mp unselected).2
  refine {
    before := first.before
    endpoint := first.target
    endpoint_condition := endpointGiven.1
    endpoint_ne_pivot := ?_
    starts := prefixStarts
    simple := ?_
    consecutive := prefixConsecutive
    action_free := prefixFree
    before_given_free := earlierFree
  }
  · intro same
    have singletonTrue := (NodeSet.singleton_eq_true_iff pivot pivot).mpr rfl
    rw [same] at endpointGiven
    exact Bool.false_ne_true (endpointGiven.2.symm.trans singletonTrue)
  · apply Consecutive.nodup_of_fin_lt
    exact Consecutive.mono (fun _ _ edge => mutilatedDirected_earlier S query.action edge) _ prefixConsecutive

/-- Obtain activation data from an actual collider window of the extracted
back-door path.  The activity proof supplies the ancestry test automatically,
and path membership supplies action avoidance.  Thus no extra activation or
action-freedom flags are required from a conditional failure caller.

The displayed window is intentional: later network constructions need the
same predecessor and successor when deciding which local parent or latent
inputs to use at this collider.  This constructor retains that connection to
the actual path instead of searching for an unrelated activated vertex. -/
def ConditionalBackdoorPath.colliderActivationRoute
    {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {pivot : Fin S.count}
    (backdoor : ConditionalBackdoorPath graph query pivot)
    (before after : List (SeparationNode S)) (previous next : SeparationNode S)
    (collider : Fin S.count)
    (window : backdoor.path.nodes = before ++ previous :: .observed collider :: next :: after)
    (isCollider : IsCollider graph (GraphMutilation.bar query.action)
      previous (.observed collider) next) :
    ConditionalColliderActivationRoute query pivot collider := by
  have active := InternalTriplesActive.triple_of_append before after previous (.observed collider) next
    (window ▸ backdoor.path.internal_active)
  have activated : graph.ancestorOf (GraphMutilation.bar query.action)
      (NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton pivot)))
      (.observed collider) = true := by
    rcases active with colliderAndActivated | nonColliderAndOpen
    · exact colliderAndActivated.2
    · exact False.elim (nonColliderAndOpen.1 isCollider)
  have member : .observed collider ∈ backdoor.path.nodes := by
    rw [window]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
  exact ConditionalColliderActivationRoute.ofAncestor graph query pivot collider
    (backdoor.action_false_of_mem collider member) activated

end Causality
end Thesis
