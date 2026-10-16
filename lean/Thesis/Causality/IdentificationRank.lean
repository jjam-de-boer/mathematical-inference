import Thesis.Causality.ComponentConnectivity

namespace Thesis
namespace Causality

open Probability

/-!
# A shared graph-only rank for identification recursion

The host-size term and a one-bit product bonus provide a decreasing measure
for the historical recursion, and reusable bounds for the current engine's
stronger rank. These lemmas inspect finite sets and c-component partitions;
they neither depend on legacy trace types nor assume denotational soundness.

The current engine still proves its own augmentation-aware progress in
CausalTransport.KernelIdentification. Reusing this smaller structural layer
does not certify outputs of the quarantined legacy program or change either
program. All moved public names and theorem statements remain unchanged.
-/

/-! ## Host-size bounds and the product bonus -/

/--
Rank of an ID invocation for fuel-totality.  Every strict host restriction
costs at least two units.  A multi-component product receives one additional
unit, which that product consumes before recursing on a factor whose free set
is a single c-component.  This two-level measure is substantially tighter
than the public cubic fuel allowance.
-/
def identificationTraceRank (G : ObservedGraph S)
    (remaining action : NodeSet S) : Nat :=
  2 * (NodeSet.members remaining).length +
    match G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) with
    | _ :: _ :: _ => 1
    | _ => 0

theorem identificationTraceRank_lower
    (G : ObservedGraph S) (remaining action : NodeSet S) :
    2 * (NodeSet.members remaining).length ≤
      identificationTraceRank G remaining action := by
  unfold identificationTraceRank
  cases components :
      G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) with
  | nil => simp
  | cons component rest =>
      cases rest with
      | nil => simp
      | cons component2 rest => simp

theorem identificationTraceRank_upper
    (G : ObservedGraph S) (remaining action : NodeSet S) :
    identificationTraceRank G remaining action ≤
      2 * (NodeSet.members remaining).length + 1 := by
  unfold identificationTraceRank
  cases components :
      G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) with
  | nil => simp
  | cons component rest =>
      cases rest with
      | nil => simp
      | cons component2 rest => simp

/-- An ancestral-shrink frame strictly decreases the invocation rank. -/
theorem identificationTraceRank_shrink_lt
    (G : ObservedGraph S) (remaining outcome action : NodeSet S)
    (notAncestral :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = false) :
    identificationTraceRank G
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        action <
      identificationTraceRank G remaining action := by
  have shorter :
      (NodeSet.members
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))).length <
        (NodeSet.members remaining).length :=
    NodeSet.length_members_lt_of_subset_of_equal_false
      (ancestralSet_subset G remaining
        (GraphMutilation.bar (NodeSet.inter action remaining))
        (NodeSet.inter outcome remaining))
      notAncestral
  have nestedUpper := identificationTraceRank_upper G
    (G.ancestralSet remaining
      (GraphMutilation.bar (NodeSet.inter action remaining))
      (NodeSet.inter outcome remaining)) action
  have outerLower := identificationTraceRank_lower G remaining action
  omega

/-- A 4.3 c-component restriction strictly decreases the invocation rank. -/
theorem identificationTraceRank_restrict_lt
    (G : ObservedGraph S) (remaining action component larger : NodeSet S)
    (severalRemainingComponents : G.isSingleCComponent remaining = false)
    (containingComponent :
      G.containingCComponent remaining component = some larger) :
    identificationTraceRank G larger
        (NodeSet.inter (NodeSet.inter action remaining) larger) <
      identificationTraceRank G remaining action := by
  have containingSpec :=
    containingCComponent_spec G remaining component containingComponent
  have largerDifferent : NodeSet.equal larger remaining = false := by
    cases equalResult : NodeSet.equal larger remaining with
    | false =>
        rfl
    | true =>
        have largerEq : larger = remaining :=
          (NodeSet.equal_eq_true_iff larger remaining).mp equalResult
        have singletonPartition : G.cComponents remaining = [remaining] :=
          cComponents_eq_of_mem_host G remaining containingSpec.1 largerEq
        have singleTrue : G.isSingleCComponent remaining = true := by
          simp only [ObservedGraph.isSingleCComponent, singletonPartition]
          exact (NodeSet.equal_eq_true_iff remaining remaining).mpr rfl
        exact False.elim
          (Bool.false_ne_true
            (severalRemainingComponents.symm.trans singleTrue))
  have shorter :
      (NodeSet.members larger).length <
        (NodeSet.members remaining).length :=
    NodeSet.length_members_lt_of_subset_of_equal_false
      (containingCComponent_subset_host G remaining component
        containingComponent)
      largerDifferent
  have nestedUpper := identificationTraceRank_upper G larger
    (NodeSet.inter (NodeSet.inter action remaining) larger)
  have outerLower := identificationTraceRank_lower G remaining action
  omega

/--
A product frame consumes exactly the rank's product bonus.  Its selected
factor is a c-component of the current free set; on the factor query the new
free set simplifies to that factor, whose own c-component partition is a
singleton.
-/
theorem identificationTraceRank_product_lt
    (G : ObservedGraph S) (remaining action : NodeSet S)
    (component component2 : NodeSet S) (rest : List (NodeSet S))
    (piece : NodeSet S)
    (freeComponents :
      G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) =
        component :: component2 :: rest)
    (pieceMem : piece ∈ component :: component2 :: rest) :
    identificationTraceRank G remaining (NodeSet.diff remaining piece) <
      identificationTraceRank G remaining action := by
  have pieceMemFree :
      piece ∈
        G.cComponents
          (NodeSet.diff remaining (NodeSet.inter action remaining)) := by
    rw [freeComponents]
    exact pieceMem
  have pieceSubsetRemaining : NodeSet.Subset piece remaining :=
    NodeSet.Subset.trans
      (cComponents_subset G _ pieceMemFree)
      (NodeSet.diff_subset_left _ _)
  have nestedActionInter :
      NodeSet.inter (NodeSet.diff remaining piece) remaining =
        NodeSet.diff remaining piece := by
    rw [NodeSet.inter_comm]
    exact NodeSet.inter_eq_of_subset (NodeSet.diff_subset_left _ _)
  have nestedFree :
      NodeSet.diff remaining
          (NodeSet.inter (NodeSet.diff remaining piece) remaining) =
        piece := by
    rw [nestedActionInter, NodeSet.diff_diff,
      NodeSet.inter_eq_of_subset pieceSubsetRemaining]
  have nestedComponents :
      G.cComponents
          (NodeSet.diff remaining
            (NodeSet.inter (NodeSet.diff remaining piece) remaining)) =
        [piece] := by
    rw [nestedFree]
    exact cComponents_self_of_mem G _ pieceMemFree
  simp [identificationTraceRank, freeComponents, nestedComponents]

end Causality
end Thesis
