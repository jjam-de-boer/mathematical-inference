import Thesis.CausalTransport.ConditionalFailureFlowBoundary
import Thesis.CausalTransport.ConditionalFailureSmallInteraction

namespace Thesis
namespace Causality

open PathSpecification HedgeChannelInstallation HedgeChannelEnvironmentInstallation

variable {S : ObservedSignature.{0}}

/-!
# Preserve the first conditioned approach from an original Small source

The exhaustive all-Small flow boundary already gives a complete stopped
path from every original Small source.  Because the policy stops at every
queried outcome or conditioner, a conditioned encounter is necessarily its
actual endpoint.  No proper vertex is originally queried.  Retaining that
endpoint therefore preserves an unconditioned approach, whereas selecting
a later reachable conditioner can introduce conditioned intermediate rows.

The path and endpoint below are the actual finite policy output.  No path
or first-conditioner representative is selected from propositional existence.
The remaining negative exchange test supplies its normalized path and one
common cut policy through the already generalized retained-pivot interfaces.

The all-Small-conditioned case is closed by the complete normalized covariance
construction: choose the hedge's actual Small action root, retain all original
conditioners, and derive full Small coverage.  A second finite source scan then
returns either positive original-query countermodels or a first-conditioned
approach whose Small source is unconditioned.  This is an exhaustive reduction
of the hard case, not the missing universal oddness-transfer theorem.  Contacts
with normalized heads, activation traces and nonzero omitted forks still need
handling, together with every uncovered mandatory Small row.
-/

/-- A complete actual boundary-flow path from an original Small source,
whose real endpoint is conditioned.  Its proper-prefix freedom and actual
graph arrows are derived below, not independent readiness fields. -/
structure FirstConditionedSmallApproach {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    (w : HedgeWitness graph query.jointNumerator) where
  source : Fin S.count
  source_in_small : w.small source = true
  path : SuccessorPath w.smallOutcomeFlowNodes w.conditionalBoundarySuccessor source
  endpoint_condition : query.condition path.endpoint = true

namespace FirstConditionedSmallApproach

variable {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    {w : HedgeWitness graph query.jointNumerator}

/-- Construct the approach from the exhaustive boundary's actual complete
path.  An encountered conditioner stops, so complete-path determinism identifies
it with the computed endpoint; the existential is eliminated only in `Prop`. -/
def ofBoundary (boundary : ConditionedSmallFlowBoundary w) (source : Fin S.count)
    (inside : w.small source = true) : FirstConditionedSmallApproach w := by
  let path := w.conditionalBoundaryPath source inside
  have conditioned : query.condition path.endpoint = true := by
    rcases List.any_eq_true.mp (boundary.encounters_condition source inside) with ⟨node, member, selected⟩
    have queried : query.jointNumerator.outcome node = true := by
      change (query.outcome node || query.condition node) = true
      rw [selected]
      exact Bool.or_true _
    have stopped : w.conditionalBoundarySuccessor node = none := by
      simp only [HedgeWitness.conditionalBoundarySuccessor, queried, if_true]
    have same := path.eq_endpoint_of_stopped node member stopped
    exact same ▸ selected
  exact { source := source, source_in_small := inside, path := path, endpoint_condition := conditioned }

/-- The first conditioner is the path's literal endpoint, not a later
maximizer or a fresh search result.  This transparent adapter retains its index. -/
abbrev pivot (approach : FirstConditionedSmallApproach w) : RetainedConditionalPivot query where
  node := approach.path.endpoint
  selected := approach.endpoint_condition

/-- The literal proper prefix of the complete computed path.  It may be
empty when the original Small source is itself conditioned. -/
def before (approach : FirstConditionedSmallApproach w) : List (Fin S.count) := approach.path.nodes.dropLast

/-- The computed prefix and first conditioner reconstruct the complete
original list.  Nonemptiness follows from its displayed source, not an
empty-list classical equivalence or a selected existential decomposition. -/
theorem nodes_eq_before_endpoint (approach : FirstConditionedSmallApproach w) :
    approach.path.nodes = approach.before ++ [approach.pivot.node] := by
  have nonempty : approach.path.nodes ≠ [] := by
    intro empty
    have starts := approach.path.starts
    rw [empty] at starts
    cases starts
  have lastEq : approach.path.nodes.getLast nonempty = approach.path.endpoint :=
    Option.some.inj ((List.getLast?_eq_some_getLast nonempty).symm.trans approach.path.finishes)
  have full := (List.dropLast_concat_getLast nonempty).symm
  rw [lastEq] at full
  exact full

private theorem prefix_member_parts (approach : FirstConditionedSmallApproach w) (node : Fin S.count)
    (member : node ∈ approach.before) : node ∈ approach.path.nodes ∧ node ≠ approach.path.endpoint := by
  refine ⟨?_, ?_⟩
  · rw [approach.nodes_eq_before_endpoint]
    exact List.mem_append.mpr (Or.inl member)
  · exact (List.nodup_append.mp (approach.nodes_eq_before_endpoint ▸ approach.path.simple)).2.2
      node member approach.path.endpoint (List.mem_singleton.mpr rfl)

/-- Every visited row avoids the full original action set. -/
theorem action_free (approach : FirstConditionedSmallApproach w) (node : Fin S.count)
    (member : node ∈ approach.path.nodes) : query.action node = false :=
  outcomeFlow_avoids_action w node (approach.path.inside node member)

/-- Every proper path vertex avoids the entire original queried union.
If it were an outcome or conditioner, the stopped policy would make it the
endpoint.  The premise concerns the actual list, not a proposed route mask. -/
theorem before_queried_free (approach : FirstConditionedSmallApproach w) (node : Fin S.count)
    (member : node ∈ approach.path.nodes) (different : node ≠ approach.path.endpoint) :
    query.jointNumerator.outcome node = false := by
  cases queried : query.jointNumerator.outcome node with
  | false => rfl
  | true =>
      have stopped : w.conditionalBoundarySuccessor node = none := by
        simp only [HedgeWitness.conditionalBoundarySuccessor, queried, if_true]
      exact False.elim (different (approach.path.eq_endpoint_of_stopped node member stopped))

/-- In particular every proper vertex is unconditioned in the unchanged
original query, not merely in a singleton exchange's smaller given-set. -/
theorem before_condition_free (approach : FirstConditionedSmallApproach w) (node : Fin S.count)
    (member : node ∈ approach.path.nodes) (different : node ≠ approach.path.endpoint) : query.condition node = false :=
  (Bool.or_eq_false_iff.mp (approach.before_queried_free node member different)).2

/-- Proper vertices cannot already be queried outcomes either; first-queried
stopping preserves this stronger approach contract automatically. -/
theorem before_outcome_free (approach : FirstConditionedSmallApproach w) (node : Fin S.count)
    (member : node ∈ approach.path.nodes) (different : node ≠ approach.path.endpoint) : query.outcome node = false :=
  (Bool.or_eq_false_iff.mp (approach.before_queried_free node member different)).1

/-- Every vertex of a conditioned complete boundary path avoids all
original queried outcomes, including its endpoint.  An outcome would stop
the map there; the same endpoint is conditioned, contradicting the original
query's disjointness.  No endpoint omission is mistaken for route freedom. -/
theorem outcome_free (approach : FirstConditionedSmallApproach w) (node : Fin S.count)
    (member : node ∈ approach.path.nodes) : query.outcome node = false := by
  cases selected : query.outcome node with
  | false => rfl
  | true =>
      have queried : query.jointNumerator.outcome node = true := by
        change (query.outcome node || query.condition node) = true
        rw [selected]
        rfl
      have stopped : w.conditionalBoundarySuccessor node = none := by
        simp only [HedgeWitness.conditionalBoundarySuccessor, queried, if_true]
      have same := approach.path.eq_endpoint_of_stopped node member stopped
      have conditioned : query.condition node = true := same ▸ approach.endpoint_condition
      have free := query.outcome_condition_disjoint node selected
      exact False.elim (Bool.false_ne_true (free.symm.trans conditioned))

/-- The literal prefix requires no separate nonendpoint certificate. -/
theorem prefix_condition_free (approach : FirstConditionedSmallApproach w) (node : Fin S.count)
    (member : node ∈ approach.before) : query.condition node = false :=
  approach.before_condition_free node (approach.prefix_member_parts node member).1 (approach.prefix_member_parts node member).2

/-- First-queried stopping also excludes original outcomes from the prefix. -/
theorem prefix_outcome_free (approach : FirstConditionedSmallApproach w) (node : Fin S.count)
    (member : node ∈ approach.before) : query.outcome node = false :=
  approach.before_outcome_free node (approach.prefix_member_parts node member).1 (approach.prefix_member_parts node member).2

/-- Prefix coordinates retain full original action freedom. -/
theorem prefix_action_free (approach : FirstConditionedSmallApproach w) (node : Fin S.count)
    (member : node ∈ approach.before) : query.action node = false :=
  approach.action_free node (approach.prefix_member_parts node member).1

/-- The endpoint is the only conditioned vertex in the actual list. -/
theorem conditioned_member_eq_endpoint (approach : FirstConditionedSmallApproach w) (node : Fin S.count)
    (member : node ∈ approach.path.nodes) (selected : query.condition node = true) : node = approach.path.endpoint := by
  have queried : query.jointNumerator.outcome node = true := by
    change (query.outcome node || query.condition node) = true
    rw [selected]
    exact Bool.or_true _
  have stopped : w.conditionalBoundarySuccessor node = none := by
    simp only [HedgeWitness.conditionalBoundarySuccessor, queried, if_true]
  exact approach.path.eq_endpoint_of_stopped node member stopped

/-- Replay every actual forward arrow in the original incoming action cut.
The original outcome-flow certificates supply declared arrows and receivers. -/
theorem consecutive_bar (approach : FirstConditionedSmallApproach w) :
    Consecutive (fun parent child => mutilatedDirected S query.action parent child = true) approach.path.nodes := by
  apply Consecutive.mono (fun parent child edge => ?_) _ approach.path.consecutive
  have actual := childWellFormed_edge w.smallOutcomeFlowNodes w.conditionalBoundarySuccessor
    w.conditionalBoundarySuccessor_wellFormed edge
  have free := outcomeFlow_avoids_action w child actual.2.1
  change query.action child = false at free
  simpa only [mutilatedDirected, free, Bool.false_eq_true, if_false] using actual.2.2

/-- The same arrows survive the first conditioner's outgoing cut, because
that vertex is a real sink and cannot transmit a step of this path. -/
theorem consecutive_cut (approach : FirstConditionedSmallApproach w) :
    Consecutive (fun parent child => graph.expandedMutilatedEdge
      (GraphMutilation.barUnderline query.action (NodeSet.singleton approach.pivot.node))
        (.observed parent) (.observed child) = true) approach.path.nodes := by
  apply Consecutive.mono (fun parent child edge => ?_) _ approach.path.consecutive
  have actual := childWellFormed_edge w.smallOutcomeFlowNodes w.conditionalBoundarySuccessor
    w.conditionalBoundarySuccessor_wellFormed edge
  have free := outcomeFlow_avoids_action w child actual.2.1
  change query.action child = false at free
  have different : parent ≠ approach.path.endpoint := by
    intro same
    have stopped := approach.path.stopped
    rw [← same, edge] at stopped
    cases stopped
  have absent : NodeSet.singleton approach.path.endpoint parent = false := by
    apply Bool.eq_false_iff.mpr
    intro selected
    exact different ((NodeSet.singleton_eq_true_iff _ _).mp selected)
  change (S.directed parent child && !(NodeSet.singleton approach.path.endpoint parent) && !(query.action child)) = true
  rw [actual.2.2, absent, free]
  rfl

/-- An exhausted terminal supplies the actual collider-normal path at this
first conditioner.  No maximality or independently chosen negative-test flag
is supplied; the original terminal exchange answer is reused directly. -/
def normalForm (approach : FirstConditionedSmallApproach w)
    (exhausted : conditionalExchangeStep? graph query = none) :
    ConditionalBackdoorPathNormalForm graph query approach.pivot.node :=
  .ofNoExchange graph query exhausted approach.pivot.node approach.pivot.selected

/-- One merged activation policy at the retained first conditioner.
Its domain, coverage, exact cut arrows and conditioned sinks are constructed. -/
def cutForest (approach : FirstConditionedSmallApproach w) : ConditionalCutColliderActivationForest query approach.pivot.node :=
  .ofRetainedPivot graph query approach.pivot.node approach.pivot.selected

end FirstConditionedSmallApproach

/-! ## Close the fully conditioned Small case before oddness transfer -/

/-- When all mandatory Small rows are originally conditioned, their actual
action root is a legal retained pivot in Small.  Conditioned completion covers
every Small row, so the generalized conservation/covariance theorem constructs
positive countermodels for the unchanged query.  No matching or oddness premise
is supplied.  This is a proved branch, not a universal Small-coverage assertion. -/
noncomputable def conditionalCounterexampleOfConditionedSmall {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (exhausted : conditionalExchangeStep? graph query = none) (conditioned : NodeSet.Subset w.small query.condition) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query := by
  let pivot : RetainedConditionalPivot query := {
    node := w.actionRoot
    selected := conditioned w.actionRoot w.actionRoot_in_small
  }
  let normal := ConditionalBackdoorPathNormalForm.ofNoExchange graph query exhausted pivot.node pivot.selected
  let forest := ConditionalCutColliderActivationForest.ofRetainedPivot graph query pivot.node pivot.selected
  have covered : NodeSet.Subset w.small (normal.smallInteractionRows pivot forest) := by
    intro node inside
    exact NodeSet.subset_union_right _ _ node (conditioned node inside)
  exact conditionalCounterexampleOfNormalizedActivation w rich pivot normal forest w.actionRoot_in_small covered

/-- The remaining approach begins at a genuinely unconditioned original
Small row.  Its source and path are finite data returned by the scan below;
no existential source or route is chosen from a proposition. -/
structure UnconditionedFirstSmallApproach {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    (w : HedgeWitness graph query.jointNumerator) extends FirstConditionedSmallApproach w where
  source_unconditioned : query.condition source = false

namespace UnconditionedFirstSmallApproach

variable {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {w : HedgeWitness graph query.jointNumerator}

/-- A genuinely unconditioned source differs from its conditioned endpoint,
so this hard branch cannot be a disguised zero-edge conditioned approach. -/
theorem source_ne_endpoint (approach : UnconditionedFirstSmallApproach w) : approach.source ≠ approach.path.endpoint := by
  intro same
  have free := approach.source_unconditioned
  rw [same, approach.endpoint_condition] at free
  cases free

/-- The residual source is genuinely in the proper approach prefix. -/
theorem source_mem_before (approach : UnconditionedFirstSmallApproach w) : approach.source ∈ approach.before := by
  have member := List.mem_of_head? approach.path.starts
  rw [approach.toFirstConditionedSmallApproach.nodes_eq_before_endpoint] at member
  rcases List.mem_append.mp member with before | endpoint
  · exact before
  · exact False.elim (approach.source_ne_endpoint (List.mem_singleton.mp endpoint))

/-- The remaining approach has at least one proper vertex.  The proof
uses its actual source membership and never an empty-filter choice lemma. -/
theorem before_ne_nil (approach : UnconditionedFirstSmallApproach w) : approach.before ≠ [] := by
  intro empty
  have member := approach.source_mem_before
  rw [empty] at member
  cases member

end UnconditionedFirstSmallApproach

/-- Exhaust both the free-path countermodel branch and the fully conditioned
Small branch.  The only residual data are an actual first-conditioned approach
from an unconditioned Small source.  Boolean scans inspect all original Small
vertices; there is no semantic decision, excluded middle or axiom of choice. -/
noncomputable def HedgeWitness.conditionalCounterexampleOrFirstSmallApproach
    {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (exhausted : conditionalExchangeStep? graph query = none) :
    Sum (ConditionalCounterexampleIn (GraphModelClass.positive graph) query) (UnconditionedFirstSmallApproach w) := by
  cases w.conditionalCounterexampleOrSmallFlowBoundary rich with
  | inl counterexample => exact .inl counterexample
  | inr boundary =>
      let sources := (NodeSet.members w.small).attach
      let free := fun source : { source // source ∈ NodeSet.members w.small } => !(query.condition source.val)
      cases found : sources.any free with
      | true =>
          let chosen := listFirstAny sources free found
          have inside : w.small chosen.val = true := (NodeSet.mem_members_iff _ _).mp chosen.property
          have unconditioned : query.condition chosen.val = false := by
            simpa only [free, Bool.not_eq_true'] using listFirstAny_pred sources free found
          exact .inr {
            toFirstConditionedSmallApproach := .ofBoundary boundary chosen.val inside
            source_unconditioned := unconditioned
          }
      | false =>
          have conditioned : NodeSet.Subset w.small query.condition := by
            intro source inside
            cases selected : query.condition source with
            | true => rfl
            | false =>
                let candidate : { source // source ∈ NodeSet.members w.small } :=
                  ⟨source, (NodeSet.mem_members_iff _ _).mpr inside⟩
                have accepted : free candidate = true := by
                  change Bool.not (query.condition source) = true
                  rw [selected]
                  rfl
                have present : sources.any free = true := List.any_eq_true.mpr ⟨candidate, List.mem_attach _ _, accepted⟩
                rw [found] at present
                cases present
          exact .inl (conditionalCounterexampleOfConditionedSmall w rich exhausted conditioned)

end Causality
end Thesis
