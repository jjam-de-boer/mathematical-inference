import Thesis.CausalTransport.DSeparationCorrectness

namespace Thesis
namespace Causality

universe u

variable {S : ObservedSignature.{u}}

/-!
# Restoring cut edges along an existing active path

Conditional failure exposes a path in the singleton outgoing-cut graph.
The subsequent countermodel argument works in the incoming-cut action graph,
so it must restore that singleton's outgoing edges without losing activity.

Adding arbitrary edges to an arbitrary directed graph need not preserve a
path's collider status.  Here both side graphs are mutilations of the same
expanded DAG.  Its strict vertex rank rules out opposite directed edges.
Consequently an adjacent pair already used by the smaller graph cannot change
orientation in the larger graph.  Collider status along the actual path is
preserved, while collider activation can only increase.

The transport below therefore keeps the exact vertex list and needs only
edge inclusion.  No path is selected from an existence proof, and no new
active-path assumption is introduced.
-/

namespace ObservedGraph

/-- Restoring edges preserves every already verified ancestor relation.
The same finite walk is replayed edge by edge, with its length unchanged. -/
theorem ancestorOf_of_edge_inclusion (G : ObservedGraph S)
    (smaller larger : GraphMutilation S)
    (included : forall left right, G.expandedMutilatedEdge smaller left right = true ->
      G.expandedMutilatedEdge larger left right = true)
    (conditioned : NodeSet S) {node : SeparationNode S}
    (ancestor : G.ancestorOf smaller conditioned node = true) :
    G.ancestorOf larger conditioned node = true := by
  rcases (G.ancestorOf_eq_true_iff smaller conditioned node).mp ancestor with
    ⟨target, selected, length, bound, ⟨walk⟩⟩
  exact (G.ancestorOf_eq_true_iff larger conditioned node).mpr
    ⟨target, selected, length, bound, ⟨walk.mapEdge included⟩⟩

end ObservedGraph

namespace PathSpecification

/-- An existing adjacent pair cannot acquire the opposite orientation when
edges are restored.  Both orientations would contradict the common DAG rank. -/
private theorem edge_of_adjacent_of_edge_inclusion (G : ObservedGraph S)
    (smaller larger : GraphMutilation S)
    (included : forall left right, G.expandedMutilatedEdge smaller left right = true ->
      G.expandedMutilatedEdge larger left right = true)
    {left right : SeparationNode S} (adjacent : Adjacent G smaller left right)
    (forward : G.expandedMutilatedEdge larger left right = true) :
    G.expandedMutilatedEdge smaller left right = true := by
  rcases adjacent with same | opposite
  · exact same
  · have forwardRank := G.expandedMutilatedEdge_rank_lt larger forward
    have oppositeRank := G.expandedMutilatedEdge_rank_lt larger (included _ _ opposite)
    exact False.elim (Nat.lt_asymm forwardRank oppositeRank)

/-- Activity of one internal triple survives restoring edges.  The two
adjacency premises refer to that actual triple, not to all pairs of vertices. -/
theorem TripleActive.ofEdgeInclusion (G : ObservedGraph S)
    (smaller larger : GraphMutilation S)
    (included : forall left right, G.expandedMutilatedEdge smaller left right = true ->
      G.expandedMutilatedEdge larger left right = true)
    (conditioned : NodeSet S) {previous middle next : SeparationNode S}
    (first : Adjacent G smaller previous middle) (second : Adjacent G smaller middle next)
    (active : TripleActive G smaller conditioned previous middle next) :
    TripleActive G larger conditioned previous middle next := by
  rcases active with colliderAndActivated | nonColliderAndOpen
  · exact Or.inl ⟨⟨included _ _ colliderAndActivated.1.1,
      included _ _ colliderAndActivated.1.2⟩,
      G.ancestorOf_of_edge_inclusion smaller larger included conditioned colliderAndActivated.2⟩
  · refine Or.inr ⟨?_, nonColliderAndOpen.2⟩
    intro collider
    apply nonColliderAndOpen.1
    exact ⟨edge_of_adjacent_of_edge_inclusion G smaller larger included first collider.1,
      edge_of_adjacent_of_edge_inclusion G smaller larger included second.symm collider.2⟩

/-- Replay the internal-triple certificates along the unchanged list. -/
theorem InternalTriplesActive.ofEdgeInclusion (G : ObservedGraph S)
    (smaller larger : GraphMutilation S)
    (included : forall left right, G.expandedMutilatedEdge smaller left right = true ->
      G.expandedMutilatedEdge larger left right = true)
    (conditioned : NodeSet S) {nodes : List (SeparationNode S)}
    (active : InternalTriplesActive G smaller conditioned nodes)
    (adjacent : Consecutive (Adjacent G smaller) nodes) :
    InternalTriplesActive G larger conditioned nodes := by
  induction active with
  | nil => exact .nil
  | singleton node => exact .singleton node
  | pair left right => exact .pair left right
  | step triple tail inductionHypothesis =>
      exact .step
        (triple.ofEdgeInclusion G smaller larger included conditioned adjacent.1 adjacent.2.1)
        (inductionHypothesis adjacent.2)

/-- Restore edges while retaining the actual certified path.  Endpoint
openness is unchanged because the conditioning set is unchanged. -/
def ActivePath.ofEdgeInclusion {G : ObservedGraph S}
    {smaller larger : GraphMutilation S} {conditioned : NodeSet S}
    {source target : SeparationNode S}
    (path : ActivePath G smaller conditioned source target)
    (included : forall left right, G.expandedMutilatedEdge smaller left right = true ->
      G.expandedMutilatedEdge larger left right = true) :
    ActivePath G larger conditioned source target where
  nodes := path.nodes
  starts := path.starts
  finishes := path.finishes
  simple := path.simple
  adjacent := Consecutive.mono (fun left right adjacent => by
    rcases adjacent with forward | reverse
    · exact Or.inl (included left right forward)
    · exact Or.inr (included right left reverse)) path.nodes path.adjacent
  source_open := path.source_open
  target_open := path.target_open
  internal_active := path.internal_active.ofEdgeInclusion G smaller larger included
    conditioned path.adjacent

/-! ## Incoming-cut conditioned vertices cannot occur on an active path -/

private theorem edge_into_cut_false (G : ObservedGraph S) (m : GraphMutilation S)
    (node : Fin S.count) (cut : m.removeIncoming node = true) (previous : SeparationNode S) :
    G.expandedMutilatedEdge m previous (.observed node) = false := by
  cases previous with
  | observed parent =>
      simp only [ObservedGraph.expandedMutilatedEdge, cut, Bool.not_true, Bool.and_false]
  | latentPair left right =>
      simp only [ObservedGraph.expandedMutilatedEdge, cut, Bool.not_true, Bool.and_false]

/-- A conditioned incoming-cut vertex cannot be an endpoint, an open
noncollider, or a collider.  This excludes actions from the actual path list,
not merely from an associated ancestor set. -/
theorem ActivePath.not_mem_of_conditioned_incomingCut {G : ObservedGraph S}
    {m : GraphMutilation S} {conditioned : NodeSet S} {source target : SeparationNode S}
    (path : ActivePath G m conditioned source target) (node : Fin S.count)
    (cut : m.removeIncoming node = true) (given : conditioned node = true) :
    Not (.observed node ∈ path.nodes) := by
  intro member
  rcases List.mem_iff_append.mp member with ⟨before, after, split⟩
  cases before with
  | nil =>
      have starts := path.starts
      rw [split] at starts
      change some (.observed node) = some source at starts
      have same := Option.some.inj starts
      have closed : ObservedGraph.blockedBy conditioned source = true := by
        rw [← same]
        exact given
      exact Bool.false_ne_true (path.source_open.symm.trans closed)
  | cons first earlier =>
      cases after with
      | nil =>
          have finishes := path.finishes
          rw [split, List.getLast?_append, List.getLast?_singleton] at finishes
          change some (.observed node) = some target at finishes
          have same := Option.some.inj finishes
          have closed : ObservedGraph.blockedBy conditioned target = true := by
            rw [← same]
            exact given
          exact Bool.false_ne_true (path.target_open.symm.trans closed)
      | cons next rest =>
          let previous := (first :: earlier).getLast (List.cons_ne_nil first earlier)
          have before_eq : first :: earlier = (first :: earlier).dropLast ++ [previous] :=
            (List.dropLast_concat_getLast (List.cons_ne_nil first earlier)).symm
          have active : InternalTriplesActive G m conditioned
              ((first :: earlier).dropLast ++ previous :: .observed node :: next :: rest) := by
            have active := path.internal_active
            rw [split, before_eq] at active
            simpa only [List.append_assoc, List.singleton_append] using active
          have triple := active.triple_of_append (first :: earlier).dropLast rest
            previous (.observed node) next
          rcases triple with colliderAndActivated | nonColliderAndOpen
          · have incoming := colliderAndActivated.1.1
            rw [edge_into_cut_false G m node cut previous] at incoming
            cases incoming
          · have opened := nonColliderAndOpen.2
            change conditioned node = false at opened
            exact Bool.false_ne_true (opened.symm.trans given)

end PathSpecification

end Causality
end Thesis
