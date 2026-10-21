import Thesis.CausalTransport.HedgeConditionalReadout
import Thesis.Examples.KernelFailureExtraction
import Thesis.Examples.HedgeConditionalReadout.Failure

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeConditionalMergedReadout

open Probability

/-!
# A routed two-root countermodel for an irreducible conditional failure

The directed graph is `X → R₁`, `X → R₂`, `R₁ → M`, `R₂ → M`,
`M → Y`, and `Y → Z`; only `X,R₁,R₂` are bidirected-confounded.
The query is `P(Y | do(X), Z)`.  The edge `Y → Z` blocks the rule-2
exchange, so its nonempty conditioner remains in the actual IDC terminal.
Corrected joint ID fails on the terminal numerator `P(Y,Z | do(X))`.

Neither common hedge root is a queried outcome.  The canonical all-root
plan injects their bits, merges them at `M`, and routes the result to `Y`.
The selected routes stop at `Y`, leaving `Z` outside both the large forest
and the modified pivots.  The general preservation theorem therefore proves
denominator equality in the *routed* pair.  Positive numerator separation and
the checked chain rule refute the actual conditional in these same models.

No countermodel, observed-law equality, conditional gap, denominator
identifiability, hand-written plan, or parity identity is supplied to the
constructor.  Finite tests only check this concrete graph's engine result
and geometric premises; the semantic proofs are the general library theorems.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000


noncomputable def extraction := identifyJointKernelFailedHedge query.jointNumerator joint_failed

private theorem root_child_none (node : Fin signature.count) (selected : rootMask node = true) :
    extraction.witness.child node = none := by
  have noInternalEdge : forall parent child : Fin signature.count,
      rootMask parent = true -> forestHost child = true -> signature.directed parent child = false := by decide +kernel
  cases childEq : extraction.witness.child node with
  | none => rfl
  | some child =>
      have edge := extraction.witness.large_forest.child_edge node child childEq
      have included : forestHost child = true := by simpa only [extraction.large_eq] using edge.2.1
      rw [noInternalEdge node child selected included] at edge
      cases edge.2.2

theorem extracted_roots : extraction.witness.roots = rootMask := by
  funext node
  cases selected : rootMask node with
  | false =>
      cases root : extraction.witness.roots node with
      | false => rfl
      | true =>
          have small := ((extraction.witness.small_forest.roots_exact node).mp root).1
          rw [extraction.small_eq] at small
          change rootMask node = true at small
          rw [selected] at small
          cases small
  | true =>
      apply (extraction.witness.large_forest.roots_exact node).mpr
      have small : extraction.witness.small node = true := by rw [extraction.small_eq]; exact selected
      exact ⟨extraction.witness.small_subset_large node small, root_child_none node selected⟩

/-- In particular, the earlier queried-root conditional constructor cannot
apply: both roots lie outside the original conditional outcome. -/
theorem roots_outside_outcome : NodeSet.Disjoint extraction.witness.roots query.outcome := by
  rw [extracted_roots]
  apply (NodeSet.disjointBool_eq_true_iff _ _).mp
  decide +kernel

/-! ## Generated routing geometry and a preserved nonempty denominator -/

theorem route_kept_sinks (node : Fin signature.count)
    (routed : extraction.witness.rootReadoutNodes node = true) :
    extraction.witness.child node = none := by
  cases selected : forestHost node with
  | false =>
      exact extraction.witness.large_forest.child_off_set node (by rw [extraction.large_eq]; exact selected)
  | true =>
      have free := extraction.witness.rootReadoutNodes_avoids_action node routed
      have rootOfFreeForestNode : forall node : Fin signature.count,
          forestHost node = true -> query.jointNumerator.action node = false -> rootMask node = true := by decide +kernel
      exact root_child_none node (rootOfFreeForestNode node selected free)

/-- The canonical root routes select `Y` before its descendant `Z` in the
numerator outcome enumeration.  Thus the actual modified node set consists
of the two roots, the merge, and `Y`, and does not contain the conditioner. -/
theorem route_nodes : extraction.witness.rootReadoutNodes =
    fun node => decide (0 < node.val ∧ node.val < 5) := by
  unfold HedgeWitness.rootReadoutNodes HedgeWitness.rootReadoutRoutes
  rw [extracted_roots]
  unfold HedgeWitness.rootReadoutRoute HedgeWitness.rootReadoutOutcome
  simp only [extracted_roots]
  apply (NodeSet.equal_eq_true_iff _ _).mp
  decide +kernel

theorem condition_outside_large : NodeSet.Disjoint query.condition extraction.witness.large := by
  rw [extraction.large_eq]
  apply (NodeSet.disjointBool_eq_true_iff _ _).mp
  decide +kernel

theorem condition_outside_routes : NodeSet.Disjoint query.condition extraction.witness.rootReadoutNodes := by
  rw [route_nodes]
  apply (NodeSet.disjointBool_eq_true_iff _ _).mp
  decide +kernel

/-- The general automatic constructor supplies this positive conditional
countermodel.  Common-root routing and matched-denominator preservation are
both needed; the nonempty conditioner is never deleted from the query. -/
noncomputable def conditionalCounterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  extraction.witness.positiveConditionalCounterexampleOfRootReadoutSinksOfConditionOutside
    rich route_kept_sinks condition_outside_large condition_outside_routes

theorem original_query_not_identifiable : Not ((GraphModelClass.positive graph).conditionalIdentifiable query) :=
  conditionalCounterexample.not_identifiable

/-- The conditional construction retains the routed numerator's model
pair, rather than substituting unmodified carrier models for its denominator. -/
noncomputable def jointCounterexample :=
  extraction.witness.positiveCounterexampleOfRootReadoutSinks rich route_kept_sinks

theorem conditional_left_unchanged : conditionalCounterexample.left = jointCounterexample.left := rfl
theorem conditional_right_unchanged : conditionalCounterexample.right = jointCounterexample.right := rfl

end HedgeConditionalMergedReadout
end Examples
end Causality
end Thesis
