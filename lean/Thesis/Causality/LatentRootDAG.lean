import Thesis.Causality.Reductions

namespace Thesis.Causality.LatentRootDAG

/-!
# A full hidden DAG for an arbitrary finite root-incidence table

Place the supplied roots before the unchanged observed nodes. There are no
arrows into roots; root-to-observed arrows are precisely the supplied table,
and observed-to-observed arrows are the signature's directed edges. Reuse the
existing `ExpandedNode` edge and rank definitions rather than adding another
graph convention. The finite sum coding below is explicit in both directions.

Every hidden-internal path in this graph is a single edge: a longer path
would have to enter a hidden root, whose rank is zero. Consequently the full
hidden-DAG projection has exactly the original observed arrows and one
bidirected edge for each pair of distinct children of a common supplied root.
No two-child restriction, probability law, mechanism or model equivalence is
assumed. This graph-only adapter is the foundation for the separate clique-root
construction and its later probability-preserving native realization.
-/

variable (S : ObservedSignature) (rootCount : Nat)

def rootNode (root : Fin rootCount) : Fin (rootCount + S.count) := root.castAdd S.count

def observedNode (node : Fin S.count) : Fin (rootCount + S.count) := Fin.natAdd rootCount node

/-- Decode the two displayed blocks; no representative is selected from a
propositional classification of an arbitrary finite node. -/
def decodeNode : Fin (rootCount + S.count) → ExpandedNode rootCount S.count :=
  Fin.addCases ExpandedNode.latent ExpandedNode.observed

@[simp] theorem decodeNode_root (root : Fin rootCount) :
    decodeNode S rootCount (rootNode S rootCount root) = .latent root := by
  simp only [decodeNode, rootNode, Fin.addCases_left]

@[simp] theorem decodeNode_observed (node : Fin S.count) :
    decodeNode S rootCount (observedNode S rootCount node) = .observed node := by
  simp only [decodeNode, observedNode, Fin.addCases_right]

/-- Acyclicity is the existing root/observed rank, with all roots at zero.
In particular even an empty or unused incidence row is an actual hidden root. -/
def graph (incident : Fin rootCount → Fin S.count → Bool) : FiniteHiddenDAG S where
  count := rootCount + S.count
  observedNode := observedNode S rootCount
  observedNode_injective := by
    intro left right same
    have decoded := congrArg (decodeNode S rootCount) same
    simpa only [decodeNode_observed, ExpandedNode.observed.injEq] using decoded
  hidden := fun node => match decodeNode S rootCount node with
    | .latent _ => true
    | .observed _ => false
  observed_not_hidden := by intro node; simp only [decodeNode_observed]
  node_classified := by
    intro node
    refine Fin.addCases (fun root => ?_) (fun observed => ?_) node
    · exact Or.inl (by simp only [decodeNode, Fin.addCases_left])
    · exact Or.inr ⟨observed, rfl⟩
  edge := fun source target => expandedEdge S rootCount incident
    (decodeNode S rootCount source) (decodeNode S rootCount target)
  rank := fun node => (decodeNode S rootCount node).rank
  edge_rank_lt := fun edge => expandedEdge_rank_lt S rootCount incident edge

variable (incident : Fin rootCount → Fin S.count → Bool)

@[simp] theorem graph_root_hidden (root : Fin rootCount) :
    (graph S rootCount incident).hidden (rootNode S rootCount root) = true := by
  simp only [graph, decodeNode_root]

@[simp] theorem graph_root_observed_edge (root : Fin rootCount) (node : Fin S.count) :
    (graph S rootCount incident).edge (rootNode S rootCount root) (observedNode S rootCount node) = incident root node := by
  simp only [graph, decodeNode_root, decodeNode_observed, expandedEdge]

@[simp] theorem graph_observed_edge (left right : Fin S.count) :
    (graph S rootCount incident).edge (observedNode S rootCount left) (observedNode S rootCount right) = S.directed left right := by
  simp only [graph, decodeNode_observed, expandedEdge]

/-- Classification recovers a concrete root index only in a proposition;
later model constructors use the explicit finite-sum decoder for data. -/
theorem hidden_iff_root (node : Fin (rootCount + S.count)) :
    (graph S rootCount incident).hidden node = true ↔ ∃ root, rootNode S rootCount root = node := by
  refine Fin.addCases (fun root => ?_) (fun observed => ?_) node
  · exact ⟨fun _ => ⟨root, rfl⟩, fun _ => graph_root_hidden S rootCount incident root⟩
  · constructor
    · intro hidden
      change (graph S rootCount incident).hidden (observedNode S rootCount observed) = true at hidden
      have absent : (graph S rootCount incident).hidden (observedNode S rootCount observed) = false :=
        (graph S rootCount incident).observed_not_hidden observed
      rw [absent] at hidden
      cases hidden
    · rintro ⟨root, same⟩
      have decoded := congrArg (decodeNode S rootCount) same
      change decodeNode S rootCount (rootNode S rootCount root) =
        decodeNode S rootCount (observedNode S rootCount observed) at decoded
      simp only [decodeNode_root, decodeNode_observed] at decoded
      cases decoded

theorem rank_of_hidden (node : Fin (rootCount + S.count))
    (hidden : (graph S rootCount incident).hidden node = true) :
    (graph S rootCount incident).rank node = 0 := by
  rcases (hidden_iff_root S rootCount incident node).mp hidden with ⟨root, rfl⟩
  simp only [graph, decodeNode_root, ExpandedNode.rank]

/-- No hidden relay exists in a root graph. This concerns hidden-internal
paths only: ordinary observed directed paths can of course have many edges. -/
theorem hiddenInternalPath_iff_edge (source target : Fin (rootCount + S.count)) :
    (graph S rootCount incident).HiddenInternalPath source target ↔
      (graph S rootCount incident).edge source target = true := by
  constructor
  · intro path
    cases path with
    | direct edge => exact edge
    | tail earlierPath hidden _edge =>
        have impossible := earlierPath.rank_lt
        rw [rank_of_hidden S rootCount incident _ hidden] at impossible
        exact False.elim (Nat.not_lt_zero _ impossible)
  · exact FiniteHiddenDAG.HiddenInternalPath.direct

theorem projectedDirected_iff (left right : Fin S.count) :
    (graph S rootCount incident).projectedDirected left right ↔ S.directed left right = true := by
  change (graph S rootCount incident).HiddenInternalPath
    (observedNode S rootCount left) (observedNode S rootCount right) ↔ _
  rw [hiddenInternalPath_iff_edge, graph_observed_edge]

/-- Exact shared-root projection, retaining roots with any number of
children. In particular a three-child row contributes all three pair edges
without being replaced by three independent probability sources. -/
theorem projectedBidirected_iff (left right : Fin S.count) :
    (graph S rootCount incident).projectedBidirected left right ↔
      left ≠ right ∧ ∃ root, incident root left = true ∧ incident root right = true := by
  constructor
  · rintro ⟨different, source, hidden, leftPath, rightPath⟩
    rcases (hidden_iff_root S rootCount incident source).mp hidden with ⟨root, same⟩
    subst source
    refine ⟨different, root, ?_, ?_⟩
    · exact (graph_root_observed_edge S rootCount incident root left) ▸
        (hiddenInternalPath_iff_edge S rootCount incident _ _).mp leftPath
    · exact (graph_root_observed_edge S rootCount incident root right) ▸
        (hiddenInternalPath_iff_edge S rootCount incident _ _).mp rightPath
  · rintro ⟨different, root, leftIncident, rightIncident⟩
    refine ⟨different, rootNode S rootCount root, graph_root_hidden S rootCount incident root, ?_, ?_⟩
    · apply (hiddenInternalPath_iff_edge S rootCount incident _ _).mpr
      change (graph S rootCount incident).edge (rootNode S rootCount root) (observedNode S rootCount left) = true
      rw [graph_root_observed_edge]
      exact leftIncident
    · apply (hiddenInternalPath_iff_edge S rootCount incident _ _).mpr
      change (graph S rootCount incident).edge (rootNode S rootCount root) (observedNode S rootCount right) = true
      rw [graph_root_observed_edge]
      exact rightIncident

end Thesis.Causality.LatentRootDAG
