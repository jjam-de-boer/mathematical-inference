import Thesis.CausalTransport.HedgeChannelMarginal

namespace Thesis
namespace Causality
namespace HedgeChannelInstallation

open Probability PathSpecification

/-!
# A balance direction along an entire unconditioned successor path

An omitted sink inside the small forest gives a balance direction by flipping
that one coordinate.  A composed outcome-flow sink can instead lie outside
the small forest.  Flipping only that sink would inject an odd background row
and would not prove a matched conditioning marginal.

This module transports a single odd source along its *whole* successor path.
Every visited bit is true.  At each later row its own bit and its sole visited
incoming predecessor cancel, even when the path leaves or re-enters the small
forest.  All off-path rows are even because the path's final successor is
absent and every earlier successor remains on the path.  Thus the exact local
source is the indicator of the starting small-forest vertex.

The path is computed by following the actual well-formed successor map for a
bounded number of steps.  Topological order proves simplicity and termination.
If every path vertex avoids the conditioner, the resulting direction fixes
both the full original action and condition sets, makes the entire small phase
odd, and makes every outside-small row even.  The existing complete-marginal
and original-alphabet countermodel theorems can then use that direction.

Avoidance of the *whole path* matters: an omitted endpoint alone does not imply
that its preceding vertices are unconditioned.  No such inference is assumed.
-/

variable {S : ObservedSignature.{0}}

/-! ## An actual complete path of a well-formed successor map -/

/-- The actual vertices of a forward successor path, stopping as soon as the
map returns `none`.  The fuel guard makes the definition structurally recursive;
well-formedness and topological order justify the displayed final sink later. -/
private def successorTrace (successor : ForestChild S) (start : Fin S.count) :
    Nat -> List (Fin S.count)
  | 0 => [start]
  | fuel + 1 => match successor start with
      | none => [start]
      | some child => start :: successorTrace successor child fuel

private theorem successorTrace_spec (domain : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool domain successor = true)
    (fuel : Nat) (start : Fin S.count) (selected : domain start = true) :
    (successorTrace successor start fuel).head? = some start ∧
    (successorTrace successor start fuel).getLast? = some (forestFollow successor start fuel) ∧
    Consecutive (fun parent child => successor parent = some child) (successorTrace successor start fuel) ∧
    (forall node, node ∈ successorTrace successor start fuel -> domain node = true) := by
  induction fuel generalizing start with
  | zero =>
      refine ⟨rfl, rfl, True.intro, ?_⟩
      intro node member
      exact List.mem_singleton.mp member ▸ selected
  | succ fuel inductionHypothesis =>
      cases next : successor start with
      | none =>
          simp only [successorTrace, forestFollow, next]
          refine ⟨rfl, rfl, True.intro, ?_⟩
          intro node member
          exact List.mem_singleton.mp member ▸ selected
      | some child =>
          have childIn := (childWellFormed_edge domain successor wellFormed next).2.1
          have rest := inductionHypothesis child childIn
          cases shape : successorTrace successor child fuel with
          | nil =>
              have impossible := rest.1
              rw [shape] at impossible
              cases impossible
          | cons head tail =>
              have same : head = child := by simpa only [shape, List.head?_cons, Option.some.injEq] using rest.1
              subst head
              rw [shape] at rest
              simp only [successorTrace, forestFollow, next, shape]
              refine ⟨rfl, rest.2.1, ⟨next, rest.2.2.1⟩, ?_⟩
              intro node member
              rcases List.mem_cons.mp member with same | later
              · exact same ▸ selected
              · exact rest.2.2.2 node later

/-- A complete simple path of a selected successor map.  The endpoint really
has no successor, and every displayed vertex belongs to the actual domain.
No arbitrary declared edge or alternative route is substituted for this map. -/
structure SuccessorPath (domain : NodeSet S) (successor : ForestChild S) (source : Fin S.count) where
  nodes : List (Fin S.count)
  endpoint : Fin S.count
  starts : nodes.head? = some source
  finishes : nodes.getLast? = some endpoint
  simple : nodes.Nodup
  consecutive : Consecutive (fun parent child => successor parent = some child) nodes
  stopped : successor endpoint = none
  inside : forall node, node ∈ nodes -> domain node = true

namespace SuccessorPath

variable {domain : NodeSet S} {successor : ForestChild S} {source : Fin S.count}

/-- Follow the actual map from a selected source.  Fuel `S.count` suffices
because every selected directed edge advances the signature's finite order. -/
def ofForest (domain : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool domain successor = true)
    (source : Fin S.count) (selected : domain source = true) : SuccessorPath domain successor source := by
  have traced := successorTrace_spec domain successor wellFormed S.count source selected
  refine {
    nodes := successorTrace successor source S.count
    endpoint := forestFollow successor source S.count
    starts := traced.1
    finishes := traced.2.1
    simple := ?_
    consecutive := traced.2.2.1
    stopped := (forestFollow_sink domain successor wellFormed source selected S.count (Nat.sub_le _ _)).2
    inside := traced.2.2.2
  }
  apply Consecutive.nodup_of_fin_lt
  exact Consecutive.mono (fun _ _ next =>
    S.directed_earlier (childWellFormed_edge domain successor wellFormed next).2.2) _ traced.2.2.1

/-! ## The path indicator has exactly one actual local source -/

private def indicator (nodes : List (Fin S.count)) : Fin S.count -> Bool :=
  fun child => decide (child ∈ nodes)

private theorem indicator_cons (head : Fin S.count) (tail : List (Fin S.count))
    (fresh : head ∉ tail) (child : Fin S.count) :
    indicator (head :: tail) child = Bool.xor (decide (child = head)) (indicator tail child) := by
  by_cases same : child = head
  · subst child
    simp only [indicator, List.mem_cons, true_or, decide_true, fresh, decide_false]
    rfl
  · simp only [indicator, List.mem_cons, same, false_or, decide_false, Bool.false_xor]

private theorem incoming_xor (successor : ForestChild S) (left right : Fin S.count -> Bool)
    (child : Fin S.count) :
    hedgeRoutingIncomingBits successor (fun parent => Bool.xor (left parent) (right parent)) child =
      Bool.xor (hedgeRoutingIncomingBits successor left child) (hedgeRoutingIncomingBits successor right child) := by
  unfold hedgeRoutingIncomingBits
  have entries : forall parent,
      hedgeRoutingParentEntry successor (fun node => Bool.xor (left node) (right node)) child parent =
        Bool.xor (hedgeRoutingParentEntry successor left child parent) (hedgeRoutingParentEntry successor right child parent) := by
    intro parent
    by_cases next : successor parent = some child <;>
      simp only [hedgeRoutingParentEntry, next, if_true, if_false, Bool.xor_self]
  exact (foldl_congr _ _ false (List.finRange S.count)
    (fun total parent => congrArg (Bool.xor total) (entries parent))).trans
      (foldl_xor_pointwise _ _ (List.finRange S.count))

private theorem incoming_singleton (successor : ForestChild S) (source child : Fin S.count) :
    hedgeRoutingIncomingBits successor (fun node => decide (node = source)) child =
      decide (successor source = some child) := by
  unfold hedgeRoutingIncomingBits
  have entries : forall parent, hedgeRoutingParentEntry successor (fun node => decide (node = source)) child parent =
      (if parent = source then decide (successor source = some child) else false) := by
    intro parent
    by_cases same : parent = source
    · subst parent
      by_cases next : successor source = some child <;>
        simp only [hedgeRoutingParentEntry, next, if_true, if_false, decide_true, decide_false]
    · by_cases next : successor parent = some child <;>
        simp only [hedgeRoutingParentEntry, next, same, if_true, if_false, decide_false]
  have rewritten := foldl_congr _ _ false (List.finRange S.count)
    (fun total parent => congrArg (Bool.xor total) (entries parent))
  have separated : (List.finRange S.count).foldl
      (fun total parent => Bool.xor total (if parent = source then decide (successor source = some child) else false)) false =
      (List.finRange S.count).foldl
        (fun total parent => if parent = source then Bool.xor total (decide (successor source = some child)) else total) false := by
    apply foldl_congr
    intro total parent
    by_cases same : parent = source <;> simp only [same, if_true, if_false, Bool.xor_false]
  exact rewritten.trans (separated.trans (foldl_xor_bit_at S.count source (decide (successor source = some child))))

/-- Incoming bits of a simple complete successor path mark exactly its tail.
The terminal `none` excludes an unintended read past the displayed endpoint. -/
private theorem incoming_indicator (successor : ForestChild S) (nodes : List (Fin S.count))
    (simple : nodes.Nodup) (endpoint : Fin S.count) (finishes : nodes.getLast? = some endpoint)
    (consecutive : Consecutive (fun parent child => successor parent = some child) nodes)
    (stopped : successor endpoint = none) (child : Fin S.count) :
    hedgeRoutingIncomingBits successor (indicator nodes) child = indicator nodes.tail child := by
  induction nodes with
  | nil => cases finishes
  | cons head tail inductionHypothesis =>
      have fresh := (List.nodup_cons.mp simple).1
      have split : indicator (head :: tail) = fun node => Bool.xor (decide (node = head)) (indicator tail node) :=
        funext (indicator_cons head tail fresh)
      rw [split, incoming_xor, incoming_singleton]
      cases tail with
      | nil =>
          have same : head = endpoint := Option.some.inj finishes
          subst endpoint
          have tailZero : hedgeRoutingIncomingBits successor (indicator []) child = false := by
            unfold hedgeRoutingIncomingBits
            apply foldl_unchanged
            intro total parent
            simp only [hedgeRoutingParentEntry, indicator, List.not_mem_nil, decide_false, ite_self, Bool.xor_false]
          rw [tailZero, stopped]
          simp only [reduceCtorEq, decide_false, Bool.xor_self, List.tail_cons, indicator, List.not_mem_nil]
      | cons next rest =>
          have tailFinishes : (next :: rest).getLast? = some endpoint := finishes
          have smaller := inductionHypothesis (List.nodup_cons.mp simple).2 tailFinishes consecutive.2
          rw [smaller, consecutive.1]
          simp only [Option.some.injEq, List.tail_cons]
          change Bool.xor (decide (next = child)) (indicator rest child) = indicator (next :: rest) child
          rw [indicator_cons next rest (List.nodup_cons.mp (List.nodup_cons.mp simple).2).1]
          have equalTests : decide (next = child) = decide (child = next) := by simp only [eq_comm]
          rw [equalTests]

/-- Flip every coordinate on the displayed path, not just its endpoint. -/
def bits (path : SuccessorPath domain successor source) : Fin S.count -> Bool := indicator path.nodes

/-- Exact local-source identity for the actual successor map.  Each later
visited row has one visited predecessor; off-path rows receive none.  Thus
only the starting row is odd, independently of other declared graph parents. -/
theorem bits_localSource (path : SuccessorPath domain successor source) (child : Fin S.count) :
    hedgeRoutingLocalSource successor path.bits child = decide (child = source) := by
  cases shape : path.nodes with
  | nil => have impossible := path.starts; rw [shape] at impossible; cases impossible
  | cons head tail =>
      have same : head = source := by simpa only [shape, List.head?_cons, Option.some.injEq] using path.starts
      subst head
      have simple : (source :: tail).Nodup := shape ▸ path.simple
      have incoming := incoming_indicator successor path.nodes path.simple path.endpoint path.finishes path.consecutive path.stopped child
      change Bool.xor (indicator path.nodes child) (hedgeRoutingIncomingBits successor (indicator path.nodes) child) = _
      rw [incoming, shape, indicator_cons source tail (List.nodup_cons.mp simple).1]
      change Bool.xor (Bool.xor (decide (child = source)) (indicator tail child)) (indicator tail child) = _
      cases decide (child = source) <;> cases indicator tail child <;> rfl

/-- A coordinate omitted by the entire path is fixed by its indicator. -/
theorem bits_false_of_free (path : SuccessorPath domain successor source) (nodes : NodeSet S)
    (free : forall node, node ∈ path.nodes -> nodes node = false)
    (child : Fin S.count) (selected : nodes child = true) : path.bits child = false := by
  apply decide_eq_false
  intro member
  exact Bool.false_ne_true ((free child member).symm.trans selected)

/-! ## Complete paths cannot diverge after meeting -/

/-- Two complete finite paths of one successor map agree in their entire
lists and endpoints when their starts agree.  The induction compares actual
map values, not a chosen graph edge or uniqueness of incoming graph parents.
The complete-list result also certifies data-preserving policy adapters. -/
private theorem complete_paths_eq (successor : ForestChild S)
    (left : List (Fin S.count)) (leftEnd : Fin S.count)
    (leftFinishes : left.getLast? = some leftEnd)
    (leftConsecutive : Consecutive (fun parent child => successor parent = some child) left)
    (leftStopped : successor leftEnd = none) :
    forall (right : List (Fin S.count)) (rightEnd : Fin S.count),
      left.head? = right.head? -> right.getLast? = some rightEnd ->
      Consecutive (fun parent child => successor parent = some child) right ->
      successor rightEnd = none -> left = right ∧ leftEnd = rightEnd := by
  induction left with
  | nil => cases leftFinishes
  | cons head tail inductionHypothesis =>
      intro right rightEnd sameStart rightFinishes rightConsecutive rightStopped
      cases right with
      | nil => cases rightFinishes
      | cons other rest =>
          have same : head = other := Option.some.inj sameStart
          subst other
          cases tail with
          | nil =>
              have endpointEq : head = leftEnd := Option.some.inj leftFinishes
              subst leftEnd
              cases rest with
              | nil => exact ⟨rfl, Option.some.inj rightFinishes⟩
              | cons next later =>
                  have nextEdge := rightConsecutive.1
                  change successor head = some next at nextEdge
                  rw [leftStopped] at nextEdge
                  cases nextEdge
          | cons next later =>
              cases rest with
              | nil =>
                  have endpointEq : head = rightEnd := Option.some.inj rightFinishes
                  subst rightEnd
                  have nextEdge := leftConsecutive.1
                  change successor head = some next at nextEdge
                  rw [rightStopped] at nextEdge
                  cases nextEdge
              | cons otherNext remaining =>
                  have nextEq : next = otherNext :=
                    Option.some.inj (leftConsecutive.1.symm.trans rightConsecutive.1)
                  subst otherNext
                  have tails := inductionHypothesis leftFinishes leftConsecutive.2
                    (next :: remaining) rightEnd rfl rightFinishes rightConsecutive.2 rightStopped
                  exact ⟨congrArg (List.cons head) tails.1, tails.2⟩

/-- Complete paths beginning at the same source retain exactly the same
observed list.  This compares actual shared-map traces without assuming a
particular forest domain, selected search route or unique incoming parent. -/
theorem nodes_eq_of_same_source (left right : SuccessorPath domain successor source) : left.nodes = right.nodes :=
  (complete_paths_eq successor left.nodes left.endpoint left.finishes left.consecutive left.stopped
    right.nodes right.endpoint (left.starts.trans right.starts.symm) right.finishes right.consecutive right.stopped).1

/-- Actual complete successor paths which share a vertex end at the same
sink.  Shared-vertex suffixes are used only in this propositional proof;
the returned path data are still produced by the finite map traversal. -/
theorem endpoint_eq_of_shared {otherSource : Fin S.count}
    (left : SuccessorPath domain successor source)
    (right : SuccessorPath domain successor otherSource) (node : Fin S.count)
    (leftMember : node ∈ left.nodes) (rightMember : node ∈ right.nodes) : left.endpoint = right.endpoint := by
  rcases List.mem_iff_append.mp leftMember with ⟨leftBefore, leftAfter, leftSplit⟩
  rcases List.mem_iff_append.mp rightMember with ⟨rightBefore, rightAfter, rightSplit⟩
  have leftFinishes : (node :: leftAfter).getLast? = some left.endpoint := by
    have finishes := left.finishes
    rw [leftSplit] at finishes
    exact ObservedGraph.getLast?_suffix_append finishes
  have rightFinishes : (node :: rightAfter).getLast? = some right.endpoint := by
    have finishes := right.finishes
    rw [rightSplit] at finishes
    exact ObservedGraph.getLast?_suffix_append finishes
  have leftSuffix := left.consecutive.drop leftBefore.length
  have rightSuffix := right.consecutive.drop rightBefore.length
  rw [leftSplit, List.drop_append_length] at leftSuffix
  rw [rightSplit, List.drop_append_length] at rightSuffix
  exact (complete_paths_eq successor (node :: leftAfter) left.endpoint leftFinishes leftSuffix
    left.stopped (node :: rightAfter) right.endpoint rfl rightFinishes rightSuffix right.stopped).2

/-- A stopped vertex visited by a complete path is its actual endpoint.
Compare with the certified singleton trace at that vertex.  This avoids
choosing a suffix as output data or unfolding the finite traversal. -/
theorem eq_endpoint_of_stopped (path : SuccessorPath domain successor source) (node : Fin S.count)
    (member : node ∈ path.nodes) (stopped : successor node = none) : node = path.endpoint := by
  let singleton : SuccessorPath domain successor node := {
    nodes := [node]
    endpoint := node
    starts := rfl
    finishes := rfl
    simple := .cons (fun _ impossible => by cases impossible) .nil
    consecutive := True.intro
    stopped := stopped
    inside := by
      intro child present
      have same := List.mem_singleton.mp present
      subst child
      exact path.inside node member
  }
  exact (path.endpoint_eq_of_shared singleton node member (List.mem_singleton.mpr rfl)).symm

/-- A real successor of a visited transmitter remains on the same complete
trace.  Completeness excludes an outgoing arrow at the final vertex, and
simplicity makes the list's next-vertex lookup agree with the shared map.
This is the closure fact needed when pruning a forest to unions of complete
traces; no uniqueness of incoming arrows or disjointness of branches is used. -/
theorem successor_mem (path : SuccessorPath domain successor source) (parent child : Fin S.count)
    (visited : parent ∈ path.nodes) (edge : successor parent = some child) : child ∈ path.nodes := by
  have notLast : path.nodes.getLast? ≠ some parent := by
    intro last
    have same : path.endpoint = parent := Option.some.inj (path.finishes.symm.trans last)
    have stopped := path.stopped
    rw [same, edge] at stopped
    cases stopped
  have found := routeSuccessor_isSome_of_mem_of_not_last path.nodes parent path.simple visited notLast
  cases next : routeSuccessor path.nodes parent with
  | none => rw [next] at found; cases found
  | some actual =>
      have actualEdge := routeSuccessor_rel_of_eq_some (fun parent child => successor parent = some child)
        path.nodes parent actual path.consecutive next
      have same : actual = child := Option.some.inj (actualEdge.symm.trans edge)
      exact same ▸ (routeSuccessor_mem path.nodes parent actual next).2

end SuccessorPath

/-! ## The original conditional balance direction -/

namespace OutcomeFlowBalanceDirection

/-- A complete unconditioned successor path beginning inside the small
forest supplies every balance field.  The endpoint may lie outside Small,
and arbitrary merging incoming parents elsewhere are retained in the map.
The exact path-indicator local-source theorem makes every outside row even. -/
def ofPath {G : ObservedGraph S} {query : JointKernelQuery S}
    (w : HedgeWitness G query) (inspected : NodeSet S) (source : Fin S.count)
    (inside : w.small source = true)
    (path : SuccessorPath w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor source)
    (free : forall node, node ∈ path.nodes -> inspected node = false) : OutcomeFlowBalanceDirection w inspected where
  bits := path.bits
  action_fixed := path.bits_false_of_free query.action
    (fun node member => outcomeFlow_avoids_action w node (path.inside node member))
  inspected_fixed := path.bits_false_of_free inspected free
  small_odd := by
    rw [outcomeFlowSignal, routingPhase_eq_localSource w.smallOutcomeFlowNodes w.small w.smallOutcomeFlowSuccessor
      w.smallOutcomeFlowSuccessor_wellFormed]
    have localSources : hedgeRoutingLocalSource w.smallOutcomeFlowSuccessor path.bits =
        (fun child => decide (child = source)) := funext path.bits_localSource
    rw [localSources]
    exact foldl_xor_indicator_of_mem_nodup (NodeSet.members w.small) source
      ((NodeSet.mem_members_iff w.small source).mpr inside) (NodeSet.nodup_members w.small)
  outside_even := by
    intro child outsideSmall
    rw [path.bits_localSource]
    apply decide_eq_false
    intro same
    subst child
    exact Bool.false_ne_true (outsideSmall.symm.trans inside)

end OutcomeFlowBalanceDirection

end HedgeChannelInstallation
end Causality
end Thesis
