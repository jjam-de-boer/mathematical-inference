import Thesis.CausalTransport.ConditionalFailureSmallInteraction
import Thesis.CausalTransport.ActivePathEndpointHeads
import Thesis.Examples.ConditionalFailureActivationSelectionGraph

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureSmallInteraction

open PathSpecification HedgeChannelEnvironmentInstallation
open CurrentConditionalFailureActivationSelection

/-!
# Structural complete-Small coverage for the actual normalized construction

The original five-vertex three-valued hedge has Small `C,Z,P` for the
unchanged query `P(Y | do(X),P,Z)`.  The general normal-form result remains
opaque: these certificates do not replace it with the displayed example path
or evaluate its exhaustive search.

The queried endpoint `Y` has no incoming expanded arrow, and its only kept
outgoing neighbour is `C`.  The general endpoint theorem therefore proves
that `C` is a selected head of the actual normalized path.  The other two
mandatory rows `P,Z` are original conditioners and are retained by the actual
conditioned completion, whether or not they need an activation edge.

Thus every genuine Small row is covered, and the actual latest pivot is in
Small.  These are finite graph/membership certificates, not supplied parity,
conservation, denominator or query-gap premises.  The semantic companion
uses them to build the full normalized-interaction countermodel pair.
-/

/-- The normal form retains the unchanged query's unique endpoint.  Only
its selection certificate is used, not reduction of its search constructor. -/
theorem normal_outcome_eq : normal.outcome = outcome :=
  (NodeSet.singleton_eq_true_iff outcome normal.outcome).mp normal.outcome_selected

/-- Every actual normalized path must select `C` as a head, because `Y`
has no incoming arrow and only that real outgoing neighbour.  This fact
does not require a guessed exact path or collider/Small disjointness. -/
theorem normal_collider_is_head : normal.pathHeads collider = true := by
  have distinct : pivot.node ≠ normal.outcome := by
    intro equal
    have free := query.outcome_condition_disjoint normal.outcome normal.outcome_selected
    exact Bool.false_ne_true (free.symm.trans (equal ▸ pivot.selected))
  have noIncoming : forall neighbor, graph.expandedMutilatedEdge
      (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) neighbor (.observed normal.outcome) = false := by
    rw [normal_outcome_eq]
    intro neighbor
    cases neighbor with
    | observed parent =>
        exact (by decide +kernel : forall parent : Fin signature.count, graph.expandedMutilatedEdge
          (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) (.observed parent) (.observed outcome) = false) parent
    | latentPair left right =>
        exact (by decide +kernel : forall left right : Fin signature.count, graph.expandedMutilatedEdge
          (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) (.latentPair left right) (.observed outcome) = false) left right
  rcases ActivePathInput.target_has_outgoing_head normal.cutPath distinct noIncoming with ⟨child, outgoing, head⟩
  have onlyChild : forall child : Fin signature.count, graph.expandedMutilatedEdge
      (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) (.observed outcome) (.observed child) = true ->
        child = collider := by decide +kernel
  rw [normal_outcome_eq] at outgoing
  have same := onlyChild child outgoing
  exact same ▸ head

/-- The actual pivot is a mandatory Small vertex in the original hedge,
not an arbitrary conditioner selected merely to fit the parity adapter. -/
theorem pivot_in_small : witness.small pivot.node = true := by decide +kernel

/-- Every mandatory Small row is present in the actual completed union.
`C` is forced by the endpoint theorem; `P,Z` are retained original evidence
rows.  Nothing is dropped, duplicated, or transported to another query. -/
theorem actual_small_coverage : NodeSet.Subset witness.small (normal.smallInteractionRows pivot.toRetained forest.toCutForest) := by
  intro child inside
  have classification : forall child : Fin signature.count, witness.small child = true ->
      child = collider ∨ query.condition child = true := by decide +kernel
  rcases classification child inside with same | conditioned
  · subst child
    apply NodeSet.subset_union_left
    apply NodeSet.subset_union_left
    exact normal_collider_is_head
  · exact NodeSet.subset_union_right _ _ child conditioned

end CurrentConditionalFailureSmallInteraction
end Examples
end Causality
end Thesis
