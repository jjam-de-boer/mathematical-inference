import Thesis.CausalTransport.ConditionalFailureActivation
import Thesis.CausalTransport.HedgeChannelRouting

namespace Thesis
namespace Causality

/-!
# A latest reachable conditioner removes activation's omitted-pivot overlap

The exchange test for a conditioner omits that conditioner from its given-set.
Accordingly, `ConditionalFailureActivation` correctly permits an activation
branch to pass through the omitted pivot.  Assuming that overlap away would
be incorrect for an arbitrary pivot, as its regression example demonstrates.

Here the pivot is selected more carefully.  Among all conditioners reachable
from a supplied hedge source in the incoming-cut action graph, take the latest
one in the signature's finite topological order.  This is an actual `getLast`
of an ordered finite filter, not a maximizer selected from a proposition.

If an activation branch passed through this pivot, its different conditioned
endpoint would be both reachable from the same source and strictly later than
the pivot.  Maximality forbids that.  Thus the previously proved exact
exchange-given-set avoidance upgrades to avoidance of the *full* condition
set at every preceding activation vertex, without an extra readiness flag.

In the hard conditional case where every composed hedge-flow sink is
conditioned, following that actual flow from the stored action root supplies
the initial reachable conditioner automatically.  The latest-pivot selection
therefore does not assume an independently chosen reachable conditioning node.
Neither this normalization nor its back-door path proves the remaining parity
network conservation at intersections with the path or the small forest.
-/

open PathSpecification

variable {S : ObservedSignature.{0}}

/-! ## Finite ordered selection and directed-route endpoint facts -/

/-- Every member of an increasing observed list is at most its last vertex.
Inspecting the list avoids any classical maximum or empty-filter lemma. -/
private theorem ordered_le_last (nodes : List (Fin S.count))
    (ordered : nodes.Pairwise (fun left right => left.val < right.val))
    (endpoint : Fin S.count) (finishes : nodes.getLast? = some endpoint) :
    forall node, node ∈ nodes -> node.val ≤ endpoint.val := by
  induction nodes with
  | nil => intro _ member; cases member
  | cons head tail inductionHypothesis =>
      cases tail with
      | nil =>
          have same : head = endpoint := Option.some.inj finishes
          intro node member
          have equal := List.mem_singleton.mp member
          subst node
          rw [same]
          exact Nat.le_refl _
      | cons next rest =>
          have parts := List.pairwise_cons.mp ordered
          have tailFinishes : (next :: rest).getLast? = some endpoint := finishes
          intro node member
          rcases List.mem_cons.mp member with same | later
          · subst node
            exact Nat.le_of_lt (parts.1 endpoint (List.mem_of_getLast? tailFinishes))
          · exact inductionHypothesis parts.2 tailFinishes node later

/-- Every member of a directed list reaches its displayed endpoint.  Only
propositional reachability is needed for maximality; no suffix is chosen into
data from a membership existence theorem. -/
private theorem reachable_to_last_of_mem (edge : Fin S.count -> Fin S.count -> Bool)
    (nodes : List (Fin S.count)) (endpoint : Fin S.count)
    (finishes : nodes.getLast? = some endpoint)
    (consecutive : Consecutive (fun left right => edge left right = true) nodes) :
    forall node, node ∈ nodes -> FiniteReachability.Reachable edge node endpoint := by
  induction nodes with
  | nil => intro _ member; cases member
  | cons head tail inductionHypothesis =>
      cases tail with
      | nil =>
          have same : head = endpoint := Option.some.inj finishes
          intro node member
          have equal := List.mem_singleton.mp member
          subst node
          rw [same]
          exact FiniteReachability.Reachable.refl edge endpoint
      | cons next rest =>
          have tailFinishes : (next :: rest).getLast? = some endpoint := finishes
          have tailReach := inductionHypothesis tailFinishes consecutive.2
          intro node member
          rcases List.mem_cons.mp member with same | later
          · subst node
            exact FiniteReachability.Reachable.prepend consecutive.1
              (tailReach next (List.mem_cons.mpr (Or.inl rfl)))
          · exact tailReach node later

/-- Strictly increasing consecutive vertices are pairwise increasing.
The existing finite-order lemma already compares the head to its whole tail. -/
private theorem ordered_of_consecutive (nodes : List (Fin S.count))
    (consecutive : Consecutive (fun left right => left.val < right.val) nodes) :
    nodes.Pairwise (fun left right => left.val < right.val) := by
  induction nodes with
  | nil => exact .nil
  | cons head tail inductionHypothesis =>
      refine .cons (fun node member => consecutive.fin_lt_of_mem_tail node member) ?_
      cases tail with
      | nil => exact .nil
      | cons next rest => exact inductionHypothesis consecutive.2

/-- Concatenated finite reachability can be rebounded by the actual observed
alphabet.  This uses the proved walk-shortening theorem, not a larger search
fuel in the eventual executable pivot selection. -/
private theorem within_of_reachable (action : NodeSet S) (source endpoint : Fin S.count)
    (reachable : FiniteReachability.Reachable (mutilatedDirected S action) source endpoint) :
    FiniteReachability.within finBeq (NodeSet.enumerated S)
      (mutilatedDirected S action) S.count source endpoint = true := by
  have bounded := FiniteReachability.boundedWalk_of_reachable finBeq
    (NodeSet.enumerated S) (mutilatedDirected S action) finBeq_eq_true_iff
    (NodeSet.mem_enumerated S) reachable
  rw [NodeSet.length_enumerated] at bounded
  exact (FiniteReachability.within_eq_true_iff_boundedWalk finBeq (NodeSet.enumerated S)
    (mutilatedDirected S action) finBeq_eq_true_iff (NodeSet.mem_enumerated S) _ _ _).mpr bounded

/-! ## Select the latest reachable conditioner constructively -/

/-- A conditioner reachable from the supplied source, latest among *all*
such conditioners.  Maximality refers to the original condition set and full
incoming action cut, not merely to a canonical route's selected endpoint. -/
structure LatestConditionalPivot (graph : ObservedGraph S)
    (query : ConditionalKernelQuery S) (source : Fin S.count) where
  node : Fin S.count
  selected : query.condition node = true
  reachable : FiniteReachability.within finBeq (NodeSet.enumerated S)
    (mutilatedDirected S query.action) S.count source node = true
  latest : forall other, query.condition other = true ->
    FiniteReachability.within finBeq (NodeSet.enumerated S)
      (mutilatedDirected S query.action) S.count source other = true -> other.val ≤ node.val

namespace LatestConditionalPivot

variable {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {source : Fin S.count}

/-- The ordered finite member list supplies its greatest reachable conditioner.
The initial conditioner proves this list nonempty but does not determine the
returned data; the executable filter and final list member do that. -/
def ofReachableConditioner (graph : ObservedGraph S) (query : ConditionalKernelQuery S)
    (source initial : Fin S.count) (selected : query.condition initial = true)
    (reachable : FiniteReachability.within finBeq (NodeSet.enumerated S)
      (mutilatedDirected S query.action) S.count source initial = true) :
    LatestConditionalPivot graph query source := by
  let eligible : NodeSet S := fun node => query.condition node &&
    FiniteReachability.within finBeq (NodeSet.enumerated S)
      (mutilatedDirected S query.action) S.count source node
  let candidates := NodeSet.members eligible
  have initialMember : initial ∈ candidates :=
    (NodeSet.mem_members_iff eligible initial).mpr (Bool.and_eq_true_iff.mpr ⟨selected, reachable⟩)
  have nonempty : candidates ≠ [] := by
    intro empty
    rw [empty] at initialMember
    cases initialMember
  let pivot := candidates.getLast nonempty
  have parts := Bool.and_eq_true_iff.mp ((NodeSet.mem_members_iff eligible pivot).mp (List.getLast_mem nonempty))
  refine ⟨pivot, parts.1, parts.2, ?_⟩
  intro other otherSelected otherReachable
  have member : other ∈ candidates :=
    (NodeSet.mem_members_iff eligible other).mpr (Bool.and_eq_true_iff.mpr ⟨otherSelected, otherReachable⟩)
  exact ordered_le_last candidates (NodeSet.members_pairwise_val_lt eligible) pivot
    (List.getLast?_eq_some_getLast nonempty) other member

/-- Exhausted exchange search supplies the actual back-door path at this
normalized pivot, with no new semantic or path-existence premise. -/
def backdoor (pivot : LatestConditionalPivot graph query source)
    (exhausted : conditionalExchangeStep? graph query = none) :
    ConditionalBackdoorPath graph query pivot.node :=
  ConditionalBackdoorPath.ofNoExchange graph query exhausted pivot.node pivot.selected

/-- No collider-activation branch for this pivot can pass through the pivot.
Its endpoint is a different conditioner.  A suffix from the pivot would make
that endpoint reachable from the same source and later in topological order,
contradicting the finite maximality certificate.  Branch intersections with
the rest of the path or the small forest are deliberately not ruled out. -/
theorem activation_pivot_not_mem (pivot : LatestConditionalPivot graph query source)
    {collider : Fin S.count} (route : ConditionalColliderActivationRoute query pivot.node collider) :
    pivot.node ∉ route.before ++ [route.endpoint] := by
  intro member
  have finishes : (route.before ++ [route.endpoint]).getLast? = some route.endpoint := by
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
  have suffix := reachable_to_last_of_mem (mutilatedDirected S query.action) _ route.endpoint
    finishes route.consecutive pivot.node member
  have sourceBounded := (FiniteReachability.within_eq_true_iff_boundedWalk finBeq (NodeSet.enumerated S)
    (mutilatedDirected S query.action) finBeq_eq_true_iff (NodeSet.mem_enumerated S) _ _ _).mp pivot.reachable
  have suffixBounded := FiniteReachability.boundedWalk_of_reachable finBeq
    (NodeSet.enumerated S) (mutilatedDirected S query.action) finBeq_eq_true_iff
    (NodeSet.mem_enumerated S) suffix
  have sourceReachesEnd := within_of_reachable query.action source route.endpoint
    (FiniteReachability.Reachable.of_bounded (sourceBounded.trans suffixBounded))
  have endpointEarlier := pivot.latest route.endpoint route.endpoint_condition sourceReachesEnd
  have ordered := ordered_of_consecutive _ (Consecutive.mono
    (fun _ _ edge => mutilatedDirected_earlier S query.action edge) _ route.consecutive)
  have pivotEarlier := ordered_le_last _ ordered route.endpoint finishes pivot.node member
  have same : route.endpoint = pivot.node := Fin.ext (Nat.le_antisymm endpointEarlier pivotEarlier)
  exact route.endpoint_ne_pivot same

/-- For the latest reachable pivot, every preceding activation vertex avoids
the *full* original condition set, not only the exchange test's other
conditioners.  The omitted-pivot case is discharged by maximality above,
rather than being added as a separate Boolean readiness assumption. -/
theorem activation_before_condition_free (pivot : LatestConditionalPivot graph query source)
    {collider : Fin S.count} (route : ConditionalColliderActivationRoute query pivot.node collider)
    (node : Fin S.count) (member : node ∈ route.before) : query.condition node = false := by
  have notPivot : node ≠ pivot.node := by
    intro same
    apply pivot.activation_pivot_not_mem route
    exact Eq.mp (congrArg (fun selected => selected ∈ route.before ++ [route.endpoint]) same)
      (List.mem_append.mpr (Or.inl member))
  have singletonFalse : NodeSet.singleton pivot.node node = false := by
    cases selected : NodeSet.singleton pivot.node node with
    | false => rfl
    | true => exact False.elim (notPivot ((NodeSet.singleton_eq_true_iff pivot.node node).mp selected))
  have free := route.before_given_free node member
  simpa only [NodeSet.diff, singletonFalse, Bool.not_false, Bool.and_true] using free

end LatestConditionalPivot

/-! ## The fully inspected hedge-flow boundary supplies the initial pivot -/

/-- Following a well-formed, action-free successor map is a bounded walk in
the actual incoming-cut action graph.  All selected successors remain in the
domain, so destination freedom is derived from that domain's avoidance. -/
private theorem forestFollow_bounded (nodes : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool nodes successor = true) (action : NodeSet S)
    (avoidsAction : forall node, nodes node = true -> action node = false)
    (fuel : Nat) (start : Fin S.count) (selected : nodes start = true) :
    FiniteReachability.BoundedWalk (mutilatedDirected S action) fuel start
      (forestFollow successor start fuel) := by
  induction fuel generalizing start with
  | zero => exact FiniteReachability.BoundedWalk.refl _ _ start
  | succ fuel inductionHypothesis =>
      cases next : successor start with
      | none =>
          simpa only [forestFollow, next] using FiniteReachability.BoundedWalk.refl
            (mutilatedDirected S action) (fuel + 1) start
      | some child =>
          have parts := childWellFormed_edge nodes successor wellFormed next
          have free := avoidsAction child parts.2.1
          have edge : mutilatedDirected S action start child = true := by
            simp only [mutilatedDirected, free, Bool.false_eq_true, if_false]
            exact parts.2.2
          simpa only [forestFollow, next] using FiniteReachability.BoundedWalk.prepend edge
            (inductionHypothesis child parts.2.1)

/-- In the hard conditional branch, following the original composed flow
from the stored hedge source reaches a conditioned sink.  That actual sink
proves the eligible list nonempty; finite ordered selection then returns the
latest conditioner reachable through *any* legal directed route.

The source is the witness's original action root, already proved to belong to
the small forest.  No singleton-root assumption, small-forest absorption,
chosen path, or semantic counterexample is supplied to this construction. -/
def HedgeWitness.latestConditionalPivotOfInspectedSinks
    {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    (w : HedgeWitness graph query.jointNumerator)
    (inspected : NodeSet.Subset (keptSinks w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor) query.condition) :
    LatestConditionalPivot graph query w.actionRoot := by
  have sourceIn := HedgeChannelInstallation.outcomeFlow_small_subset w w.actionRoot w.actionRoot_in_small
  let endpoint := forestSink w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor
    w.smallOutcomeFlowSuccessor_wellFormed w.actionRoot sourceIn
  have endpointSelected : query.condition endpoint = true := inspected endpoint
    (forestSink_kept w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor
      w.smallOutcomeFlowSuccessor_wellFormed w.actionRoot sourceIn)
  have bounded := forestFollow_bounded w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor
    w.smallOutcomeFlowSuccessor_wellFormed query.action (HedgeChannelInstallation.outcomeFlow_avoids_action w)
    S.count w.actionRoot sourceIn
  have reachable : FiniteReachability.within finBeq (NodeSet.enumerated S)
      (mutilatedDirected S query.action) S.count w.actionRoot endpoint = true :=
    (FiniteReachability.within_eq_true_iff_boundedWalk finBeq (NodeSet.enumerated S)
      (mutilatedDirected S query.action) finBeq_eq_true_iff (NodeSet.mem_enumerated S) _ _ _).mpr bounded
  exact LatestConditionalPivot.ofReachableConditioner graph query w.actionRoot endpoint endpointSelected reachable

end Causality
end Thesis
