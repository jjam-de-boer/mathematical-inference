import Thesis.Causality.Reductions

namespace Thesis
namespace Causality

/-!
# Compact finite hidden DAGs

`FiniteHiddenDAG` stores both an observed-node embedding and an explicit hidden
classifier, together with proofs that they classify every node consistently.
For construction, the classifier is redundant: on a finite total node type it
can be computed as the complement of the observed image.

This module provides that compact presentation and an additive bridge to the
existing theorem-facing record. No existing representation or theorem is
changed.
-/

/-- A finite directed graph carrying an explicit well-founded rank. -/
structure RankedFiniteDAG where
  count : Nat
  edge : Fin count -> Fin count -> Bool
  rank : Fin count -> Nat
  edge_rank_lt : forall {i j}, edge i j = true -> rank i < rank j

/--
A ranked finite DAG together with an embedding of the observed nodes. Nodes
outside the image of `observedNode` are canonically classified as hidden.
-/
structure CompactFiniteHiddenDAG (S : ObservedSignature) where
  graph : RankedFiniteDAG
  observedNode : Fin S.count -> Fin graph.count
  observedNode_injective : Function.Injective observedNode

namespace CompactFiniteHiddenDAG

/-- The computed classifier for nodes outside the finite observed image. -/
def hidden (H : CompactFiniteHiddenDAG S)
    (node : Fin H.graph.count) : Bool :=
  decide (Not (Exists fun i => H.observedNode i = node))

theorem hidden_eq_true_iff (H : CompactFiniteHiddenDAG S) (node) :
    H.hidden node = true <->
      Not (Exists fun i => H.observedNode i = node) := by
  simp [hidden]

theorem hidden_eq_false_iff (H : CompactFiniteHiddenDAG S) (node) :
    H.hidden node = false <->
      Exists fun i => H.observedNode i = node := by
  constructor
  · intro hfalse
    have hnn : Not (Not (Exists fun i => H.observedNode i = node)) := by
      intro hnot
      have htrue : H.hidden node = true := by
        simp [hidden, hnot]
      rw [htrue] at hfalse
      contradiction
    exact Decidable.of_not_not hnn
  · intro h
    simp [hidden, h]

/-- Expand the computed classification into the theorem-facing record. -/
def toFiniteHiddenDAG (H : CompactFiniteHiddenDAG S) : FiniteHiddenDAG S where
  count := H.graph.count
  observedNode := H.observedNode
  observedNode_injective := H.observedNode_injective
  hidden := H.hidden
  observed_not_hidden := by
    intro i
    exact (H.hidden_eq_false_iff (H.observedNode i)).mpr <| Exists.intro i rfl
  node_classified := by
    intro node
    cases hhidden : H.hidden node with
    | true => exact Or.inl rfl
    | false => exact Or.inr ((H.hidden_eq_false_iff node).mp hhidden)
  edge := H.graph.edge
  rank := H.graph.rank
  edge_rank_lt := H.graph.edge_rank_lt

theorem toFiniteHiddenDAG_count (H : CompactFiniteHiddenDAG S) :
    H.toFiniteHiddenDAG.count = H.graph.count := rfl

theorem toFiniteHiddenDAG_observedNode
    (H : CompactFiniteHiddenDAG S) (i) :
    H.toFiniteHiddenDAG.observedNode i = H.observedNode i := rfl

theorem toFiniteHiddenDAG_hidden
    (H : CompactFiniteHiddenDAG S) (node) :
    H.toFiniteHiddenDAG.hidden node = H.hidden node := rfl

theorem toFiniteHiddenDAG_edge
    (H : CompactFiniteHiddenDAG S) (i j) :
    H.toFiniteHiddenDAG.edge i j = H.graph.edge i j := rfl

theorem toFiniteHiddenDAG_rank
    (H : CompactFiniteHiddenDAG S) (i) :
    H.toFiniteHiddenDAG.rank i = H.graph.rank i := rfl

end CompactFiniteHiddenDAG

namespace FiniteHiddenDAG

/-- Forget the redundant hidden classifier and its classification proofs. -/
def toCompact (H : FiniteHiddenDAG S) : CompactFiniteHiddenDAG S where
  graph := {
    count := H.count
    edge := H.edge
    rank := H.rank
    edge_rank_lt := H.edge_rank_lt
  }
  observedNode := H.observedNode
  observedNode_injective := H.observedNode_injective

/-- Existing hidden-DAG records carry exactly the computed classification. -/
theorem hidden_iff_outside_observed_image (H : FiniteHiddenDAG S) (node) :
    H.hidden node = true <->
      Not (Exists fun i => H.observedNode i = node) := by
  constructor
  · intro hhidden hexists
    cases hexists with
    | intro i hi =>
        subst node
        rw [H.observed_not_hidden i] at hhidden
        contradiction
  · intro houtside
    rcases H.node_classified node with hhidden | hobserved
    · exact hhidden
    · exact (houtside hobserved).elim

/-- Compacting and re-expanding preserves the hidden classifier pointwise. -/
theorem toCompact_toFiniteHiddenDAG_hidden
    (H : FiniteHiddenDAG S) (node) :
    H.toCompact.toFiniteHiddenDAG.hidden node = H.hidden node := by
  cases h : H.hidden node with
  | false =>
      have hnot : Not (H.hidden node = true) := by simp [h]
      have hobserved : Exists fun i => H.observedNode i = node := by
        rcases H.node_classified node with hhidden | hobserved
        · exact (hnot hhidden).elim
        · exact hobserved
      exact (H.toCompact.hidden_eq_false_iff node).mpr hobserved
  | true =>
      exact (H.toCompact.hidden_eq_true_iff node).mpr
        ((H.hidden_iff_outside_observed_image node).mp h)

end FiniteHiddenDAG

end Causality
end Thesis
