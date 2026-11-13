import Thesis.Examples.ConditionalFailureSmallApproachGraph

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureSmallApproach

open PathSpecification HedgeChannelInstallation HedgeChannelEnvironmentInstallation

/-!
# First-conditioned approaches and the fully conditioned semantic branch

The genuine hedge companion proves both original singleton-exchange searches
exhausted.  In the first query, Small source `U` is unconditioned and its
actual stopped path is `U -> P`.  Original-graph latest selection instead
returns `Z`; its directed route `U -> P -> Z` has conditioned `P` in the
proper prefix.  The new constructor retains the first endpoint without any
maximality flag, and all approach arrows survive that endpoint's exact cut.

The exhaustive residual classifier really returns the complete `U,P` list,
not merely a right-branch Boolean tag or a separately supplied route.  Its
source is a genuine unconditioned Small row and its proper prefix is nonempty.
This remains the hard oddness-transfer branch, not a claimed countermodel.

In the second query all Small rows are originally conditioned.  The general
normalized conservation/covariance theorem constructs positive original-query
countermodels and the exhaustive classifier returns that semantic branch.
No model probability table, positivity flag, matched denominator or oddness
certificate is supplied by this regression.
-/

/-- Both actual stopped Small-source paths end at conditioned `P`. -/
def boundary : ConditionedSmallFlowBoundary (witness false) where
  encounters_condition := by decide +kernel

def approach : FirstConditionedSmallApproach (witness false) :=
  .ofBoundary boundary source (by decide +kernel)

theorem approach_codes : approach.path.nodes.map Fin.val = [2, 3] := by decide +kernel

theorem actual_prefix : approach.before = [source] := by decide +kernel

/-- The older original-graph maximizer advances past the first conditioner. -/
def latest : LatestConditionalPivot graph (query false) source := boundary.latestPivot source (by decide +kernel)

theorem first_before_latest : approach.pivot.node = firstConditioner ∧ latest.node = laterConditioner ∧
    approach.pivot.node.val < latest.node.val := by decide +kernel

private theorem reaches_latest : FiniteReachability.within finBeq (NodeSet.enumerated signature)
    (mutilatedDirected signature (query false).action) signature.count source laterConditioner = true := by decide +kernel

def latestRoute : List (Fin signature.count) :=
  mutilatedDirectedRoute (query false).action laterConditioner signature.count source reaches_latest

/-- Replacing the endpoint by the latest conditioner loses proper-prefix
freedom on the actual directed route, not merely on a hypothetical list. -/
theorem latest_route_conditioned_interior : latestRoute.map Fin.val = [2, 3, 4] ∧
    firstConditioner ∈ latestRoute.dropLast ∧ (query false).condition firstConditioner = true := by decide +kernel

/-- The constructed first approach has actual original-cut arrows. -/
theorem actual_approach_cut_arrows : Consecutive (fun parent child => graph.expandedMutilatedEdge
    (GraphMutilation.barUnderline (query false).action (NodeSet.singleton approach.pivot.node))
      (.observed parent) (.observed child) = true) approach.path.nodes := approach.consecutive_cut

/-- All prefix action, outcome and condition freedom is derived from the
actual policy, not added as three independent readiness flags. -/
theorem original_prefix_free (node : Fin signature.count) (member : node ∈ approach.before) :
    (query false).action node = false ∧ (query false).outcome node = false ∧ (query false).condition node = false :=
  ⟨approach.prefix_action_free node member, approach.prefix_outcome_free node member, approach.prefix_condition_free node member⟩

private def residualCodes {left : Type _} : Sum left (UnconditionedFirstSmallApproach (witness false)) -> List Nat
  | .inl _ => []
  | .inr remaining => remaining.path.nodes.map Fin.val

/-- Check the actual data returned by the exhaustive two-stage classifier.
No countermodel payload is reduced, and no alternative approach is inserted. -/
theorem residual_classifier_codes :
    residualCodes ((witness false).conditionalCounterexampleOrFirstSmallApproach rich (no_exchange false)) = [2, 3] := by
  decide +kernel

/-- Every mandatory Small row is original evidence in the second query. -/
theorem all_small_conditioned : NodeSet.Subset (witness true).small (query true).condition := by
  unfold NodeSet.Subset
  decide +kernel

/-- The new general semantic branch constructs the actual positive pair
on all original three-valued labels and the unchanged second query. -/
noncomputable def all_conditioned_counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) (query true) :=
  conditionalCounterexampleOfConditionedSmall (witness true) rich (no_exchange true) all_small_conditioned

theorem all_conditioned_query_not_identifiable : ¬ (GraphModelClass.positive graph).conditionalIdentifiable (query true) :=
  all_conditioned_counterexample.not_identifiable

private def counterexampleCase {left : Type _} {right : Type _} : Sum left right -> Bool
  | .inl _ => true
  | .inr _ => false

/-- The fully conditioned branch is actually closed by the exhaustive
classifier; it is not left as a zero-edge residual approach. -/
theorem all_conditioned_classifier_returns_counterexample :
    counterexampleCase ((witness true).conditionalCounterexampleOrFirstSmallApproach rich (no_exchange true)) = true := by
  decide +kernel

end CurrentConditionalFailureSmallApproach
end Examples
end Causality
end Thesis
