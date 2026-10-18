import Thesis.Causality.CliqueRootGraph

namespace Thesis.Causality.Examples.CliqueRootGraph

/-!
# Empty, sparse and multi-child clique-root graph regressions

These small graph checks do not instantiate probabilities or evaluate large
structural catalogues. The empty graph retains the unused empty-mask root.
On three observed vertices a complete bidirected graph permits all eight
masks, whereas one edge permits only the empty mask, three private masks and
that edge's mask. Thus unused/private slots are retained and forbidden shared
incidences are excluded. The complete graph also has one actual root feeding
all three children, rather than merely three independent pair-root slots.
-/

def emptySignature : ObservedSignature where
  count := 0
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; decide
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun _ _ => false
  directed_earlier := by intro _ _ impossible; cases impossible

def emptyGraph : ObservedGraph emptySignature where
  bidirected := fun _ _ => false
  bidirected_symmetric := by intro _ _ impossible; cases impossible
  bidirected_irreflexive := fun _ => rfl

theorem empty_has_one_unused_root : emptyGraph.cliqueRootCount = 1 := by decide +kernel

theorem empty_full_graph_has_one_node : emptyGraph.cliqueRootHiddenDAG.count = 1 := by decide +kernel

def signature : ObservedSignature where
  count := 3
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; decide
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun _ _ => false
  directed_earlier := by intro _ _ impossible; cases impossible

def completeGraph : ObservedGraph signature where
  bidirected := fun left right => decide (left ≠ right)
  bidirected_symmetric := fun edge => decide_eq_true (Ne.symm (of_decide_eq_true edge))
  bidirected_irreflexive := by intro node; simp

theorem complete_has_all_eight_masks : completeGraph.cliqueRootCount = 8 := by decide +kernel

theorem full_mask_valid : completeGraph.IsClique NodeSet.full :=
  fun _ _ _ _ different => decide_eq_true different

def threeChildRoot : Fin completeGraph.cliqueRootCount := completeGraph.cliqueRootOf NodeSet.full full_mask_valid

/-- One root feeds every child. No probability independence between its
three outputs is inferred or imposed by the graph construction. -/
theorem threeChildRoot_incident (child : Fin signature.count) :
    completeGraph.cliqueRootMask threeChildRoot child = true := by
  rw [show completeGraph.cliqueRootMask threeChildRoot = NodeSet.full from
    completeGraph.cliqueRootMask_of NodeSet.full full_mask_valid]
  rfl

def sparseGraph : ObservedGraph signature where
  bidirected := fun left right =>
    (decide (left.val = 0) && decide (right.val = 1)) ||
      (decide (left.val = 1) && decide (right.val = 0))
  bidirected_symmetric := by
    intro left right edge
    simpa only [Bool.and_comm, Bool.or_comm] using edge
  bidirected_irreflexive := by
    intro node
    apply Bool.eq_false_iff.mpr
    intro edge
    rcases Bool.or_eq_true_iff.mp edge with forward | backward
    · have bits := Bool.and_eq_true_iff.mp forward
      have atZero := of_decide_eq_true bits.1
      have atOne := of_decide_eq_true bits.2
      omega
    · have bits := Bool.and_eq_true_iff.mp backward
      have atOne := of_decide_eq_true bits.1
      have atZero := of_decide_eq_true bits.2
      omega

theorem sparse_has_only_five_masks : sparseGraph.cliqueRootCount = 5 := by decide +kernel

/-- The public full-DAG projection, not just a computed root-list count,
retains exactly the intended observed bidirected classifier. -/
theorem sparse_projection_exact (left right : Fin signature.count) :
    sparseGraph.cliqueRootHiddenDAG.projectedBidirected left right ↔ sparseGraph.bidirected left right = true :=
  sparseGraph.cliqueRootHiddenDAG_projectedBidirected left right

theorem uniform_node_bound (graph : ObservedGraph signature) : graph.cliqueRootHiddenDAG.count ≤ 11 :=
  graph.cliqueRootHiddenDAG_count_le

end Thesis.Causality.Examples.CliqueRootGraph
