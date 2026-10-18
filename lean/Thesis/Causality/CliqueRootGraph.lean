import Thesis.Causality.LatentRootDAG
import Thesis.Causality.NodeSetEnumeration
import Thesis.Probability.FiniteEnumerationBounds

namespace Thesis.Causality

open Probability

/-!
# One fixed root for every bidirected clique mask

The list is determined by the observed graph alone: enumerate its Boolean
node masks and retain exactly those whose distinct members are joined by
bidirected edges. Empty and singleton masks are included. The former handles
unused original roots without a chosen default node; the latter will collect
private observed noise. All larger masks remain available, including shared
causes with three or more children. Nothing asserts pairwise independence
between the children of such a root.

Root incidences are precisely their listed masks. The graph-only full-DAG
adapter proves exact directed projection. Clique validity excludes forbidden
bidirected edges, and the two-node mask of every existing bidirected edge
supplies the converse. There are at most `2^n` roots and hence at most
`n + 2^n` full-DAG nodes, independently of any original hidden topology.

This is not yet a probability-preserving model transformation. Grouping old
roots into these slots and proving their whole independent law and evaluator
simulation are separate next stages. Unused slots may later have deterministic
laws, but their graphical arrows must still be justified by clique validity.
-/

namespace ObservedGraph

variable {S : ObservedSignature}

private instance maskDecidableEq : DecidableEq (NodeSet S) :=
  FiniteProduct.assignmentDecidableEq S.count (fun _ => Bool) (fun _ => inferInstance)

def IsClique (graph : ObservedGraph S) (mask : NodeSet S) : Prop :=
  ∀ left right, mask left = true → mask right = true → left ≠ right → graph.bidirected left right = true

/-- Only finite Boolean bits and finite index equalities are decided. -/
def cliqueCheck (graph : ObservedGraph S) (mask : NodeSet S) : Bool :=
  finAll S.count (fun left => finAll S.count (fun right =>
    if mask left = true then
      if mask right = true then
        if left = right then true else graph.bidirected left right
      else true
    else true))

theorem cliqueCheck_eq_true_iff (graph : ObservedGraph S) (mask : NodeSet S) :
    graph.cliqueCheck mask = true ↔ graph.IsClique mask := by
  constructor
  · intro accepted left right leftSelected rightSelected different
    have pair := (finAll_eq_true_iff _).mp ((finAll_eq_true_iff _).mp accepted left) right
    simpa only [leftSelected, rightSelected, if_true, if_neg different] using pair
  · intro clique
    apply (finAll_eq_true_iff _).mpr
    intro left
    apply (finAll_eq_true_iff _).mpr
    intro right
    by_cases leftSelected : mask left = true
    · rw [if_pos leftSelected]
      by_cases rightSelected : mask right = true
      · rw [if_pos rightSelected]
        by_cases same : left = right
        · rw [if_pos same]
        · rw [if_neg same]
          exact clique left right leftSelected rightSelected same
      · rw [if_neg rightSelected]
    · rw [if_neg leftSelected]

def cliqueMasks (graph : ObservedGraph S) : List (NodeSet S) :=
  (NodeSet.subsets NodeSet.full).filter graph.cliqueCheck

theorem mem_cliqueMasks_iff (graph : ObservedGraph S) (mask : NodeSet S) :
    mask ∈ graph.cliqueMasks ↔ graph.IsClique mask := by
  constructor
  · intro listed
    exact (graph.cliqueCheck_eq_true_iff mask).mp (List.mem_filter.mp listed).2
  · intro clique
    exact List.mem_filter.mpr ⟨(NodeSet.subsets_member_iff NodeSet.full mask).mpr (fun _ _ => rfl),
      (graph.cliqueCheck_eq_true_iff mask).mpr clique⟩

theorem cliqueMasks_nodup (graph : ObservedGraph S) : graph.cliqueMasks.Nodup :=
  List.Pairwise.filter _ (NodeSet.subsets_nodup NodeSet.full)

def cliqueRootCount (graph : ObservedGraph S) : Nat := graph.cliqueMasks.length

def cliqueRootMask (graph : ObservedGraph S) (root : Fin graph.cliqueRootCount) : NodeSet S :=
  graph.cliqueMasks.get root

theorem cliqueRootMask_valid (graph : ObservedGraph S) (root : Fin graph.cliqueRootCount) :
    graph.IsClique (graph.cliqueRootMask root) :=
  (graph.mem_cliqueMasks_iff _).mp (List.get_mem _ root)

/-- A valid mask is supplied as actual Boolean data. Its first listed index
is computed, not selected from an existential clique-membership statement. -/
def cliqueRootOf (graph : ObservedGraph S) (mask : NodeSet S) (valid : graph.IsClique mask) : Fin graph.cliqueRootCount :=
  ⟨graph.cliqueMasks.idxOf mask, List.idxOf_lt_length_of_mem ((graph.mem_cliqueMasks_iff mask).mpr valid)⟩

theorem cliqueRootMask_of (graph : ObservedGraph S) (mask : NodeSet S) (valid : graph.IsClique mask) :
    graph.cliqueRootMask (graph.cliqueRootOf mask valid) = mask := by
  apply beq_iff_eq.mp
  change (graph.cliqueMasks.get (graph.cliqueRootOf mask valid) == mask) = true
  simpa only [List.get_eq_getElem, cliqueRootOf, List.idxOf] using
    (List.findIdx_getElem (p := fun value => value == mask) (xs := graph.cliqueMasks)
      (w := List.idxOf_lt_length_of_mem ((graph.mem_cliqueMasks_iff mask).mpr valid)))

theorem isClique_empty (graph : ObservedGraph S) : graph.IsClique NodeSet.empty :=
  fun _ _ selected _ _ => False.elim (Bool.false_ne_true selected)

theorem isClique_singleton (graph : ObservedGraph S) (node : Fin S.count) :
    graph.IsClique (NodeSet.singleton node) := by
  intro left right leftSelected rightSelected different
  exact False.elim (different (((NodeSet.singleton_eq_true_iff node left).mp leftSelected).trans
    ((NodeSet.singleton_eq_true_iff node right).mp rightSelected).symm))

theorem isClique_edge (graph : ObservedGraph S) {left right : Fin S.count}
    (edge : graph.bidirected left right = true) :
    graph.IsClique (NodeSet.union (NodeSet.singleton left) (NodeSet.singleton right)) := by
  intro first second firstSelected secondSelected different
  have firstCases : first = left ∨ first = right := by
    simpa only [NodeSet.union, NodeSet.singleton, Bool.or_eq_true, decide_eq_true_eq] using firstSelected
  have secondCases : second = left ∨ second = right := by
    simpa only [NodeSet.union, NodeSet.singleton, Bool.or_eq_true, decide_eq_true_eq] using secondSelected
  rcases firstCases with atLeft | atRight <;> rcases secondCases with otherLeft | otherRight
  · exact False.elim (different (atLeft.trans otherLeft.symm))
  · simpa only [atLeft, otherRight] using edge
  · simpa only [atRight, otherLeft] using graph.bidirected_symmetric edge
  · exact False.elim (different (atRight.trans otherRight.symm))

/-- Even an empty observed signature has its one empty incidence slot.
Its existence follows from a computed index, not a classical nonempty test. -/
theorem cliqueRootCount_positive (graph : ObservedGraph S) : 0 < graph.cliqueRootCount :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) (graph.cliqueRootOf NodeSet.empty graph.isClique_empty).isLt

theorem cliqueRootCount_le_pow (graph : ObservedGraph S) : graph.cliqueRootCount ≤ 2 ^ S.count := by
  apply Nat.le_trans (List.length_filter_le graph.cliqueCheck (NodeSet.subsets NodeSet.full))
  rw [NodeSet.subsets, FiniteProduct.enumeration_length]
  apply FiniteProduct.natProduct_le_pow
  intro node
  simp only [NodeSet.subsetChoices, NodeSet.full, if_true, List.length_cons, List.length_nil]
  exact Nat.le_refl 2

/-- Fixed by the observed graph alone; no original model's hidden-node
count, values, mechanisms or probability parameters enter this graph. -/
def cliqueRootHiddenDAG (graph : ObservedGraph S) : FiniteHiddenDAG S :=
  LatentRootDAG.graph S graph.cliqueRootCount graph.cliqueRootMask

theorem cliqueRootHiddenDAG_count_le (graph : ObservedGraph S) :
    graph.cliqueRootHiddenDAG.count ≤ S.count + 2 ^ S.count := by
  have bound := graph.cliqueRootCount_le_pow
  change graph.cliqueRootCount + S.count ≤ _
  omega

theorem cliqueRootHiddenDAG_projectedBidirected (graph : ObservedGraph S) (left right : Fin S.count) :
    graph.cliqueRootHiddenDAG.projectedBidirected left right ↔ graph.bidirected left right = true := by
  rw [cliqueRootHiddenDAG, LatentRootDAG.projectedBidirected_iff]
  constructor
  · rintro ⟨different, root, leftIncident, rightIncident⟩
    exact graph.cliqueRootMask_valid root left right leftIncident rightIncident different
  · intro edge
    have different : left ≠ right := by
      intro same
      subst right
      rw [graph.bidirected_irreflexive] at edge
      cases edge
    let mask := NodeSet.union (NodeSet.singleton left) (NodeSet.singleton right)
    let root := graph.cliqueRootOf mask (graph.isClique_edge edge)
    refine ⟨different, root, ?_, ?_⟩
    · rw [show graph.cliqueRootMask root = mask from graph.cliqueRootMask_of mask (graph.isClique_edge edge)]
      simp only [mask, NodeSet.union, NodeSet.singleton, decide_true, Bool.true_or]
    · rw [show graph.cliqueRootMask root = mask from graph.cliqueRootMask_of mask (graph.isClique_edge edge)]
      simp only [mask, NodeSet.union, NodeSet.singleton, decide_true, Bool.or_true]

/-- Both projected classifiers are proved, not accepted as a native-model
transfer interface. This construction alone installs no probability law. -/
def cliqueRootProjection (graph : ObservedGraph S) : FiniteLatentProjection S where
  hiddenDAG := graph.cliqueRootHiddenDAG
  directed_matches := fun left right =>
    (LatentRootDAG.projectedDirected_iff S graph.cliqueRootCount graph.cliqueRootMask left right).symm
  bidirected := graph.bidirected
  bidirected_matches := fun left right => (graph.cliqueRootHiddenDAG_projectedBidirected left right).symm

theorem cliqueRootProjection_observedGraph (graph : ObservedGraph S) (left right : Fin S.count) :
    graph.cliqueRootProjection.observedGraph.bidirected left right = graph.bidirected left right := rfl

end ObservedGraph
end Thesis.Causality
