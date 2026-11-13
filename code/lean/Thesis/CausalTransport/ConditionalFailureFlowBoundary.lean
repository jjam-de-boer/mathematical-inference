import Thesis.CausalTransport.HedgeChannelEnvironmentRouting
import Thesis.CausalTransport.ConditionalFailurePivot

namespace Thesis
namespace Causality

open PathSpecification HedgeChannelInstallation HedgeChannelEnvironmentInstallation

variable {S : ObservedSignature.{0}}

/-!
# Exhaust every Small source before the general active-path branch

Checking only the hedge's stored action-root path misses other Small sources.
The original outcome-flow policy may also continue past a queried Small
vertex.  Here the same actual flow domain is retained, but a queried outcome
or conditioner is made a genuine sink immediately.  This is a local change
of legal kept arrows, not a change to the original query or hedge.

A finite scan checks the entire complete path from every original Small
vertex.  An unconditioned path supplies a positive original-query countermodel
through the arbitrary-forest covariance theorem.  Otherwise every such path
encounters a conditioner.  This hard boundary is returned with proved
certificates; it is not a new readiness assumption of conditional failure.

In particular Small cannot contain an original queried outcome at that
boundary: its stopped path would be the unconditioned singleton.  Every
Small source still supplies an actual reachable conditioner, so latest-pivot
selection remains constructive and does not need a guessed endpoint or
all-original-sinks-conditioned premise.  The remaining normalized active-path
branch still needs the combined signal/conservation construction.
`ConditionalFailureSmallApproach` now preserves the actual first conditioned
endpoint of this stopped policy instead.  It proves original proper-prefix
freedom, closes the fully conditioned Small case and returns an unconditioned
Small-source approach for the remaining routing/oddness-transfer argument.
-/

namespace HedgeChannelInstallation.SuccessorPath

/-- A complete path from a source whose actual successor is `none` is
literally the singleton source.  This follows from its list certificates,
without unfolding or evaluating a finite trace search. -/
theorem nodes_eq_singleton_of_source_stopped {domain : NodeSet S} {successor : ForestChild S} {source : Fin S.count}
    (path : SuccessorPath domain successor source) (stopped : successor source = none) : path.nodes = [source] := by
  cases shape : path.nodes with
  | nil => have impossible := path.starts; rw [shape] at impossible; cases impossible
  | cons head tail =>
      have same : head = source := by simpa only [shape, List.head?_cons, Option.some.injEq] using path.starts
      subst head
      cases tail with
      | nil => rfl
      | cons next rest =>
          have edges := path.consecutive
          rw [shape] at edges
          have edge := edges.1
          change successor source = some next at edge
          rw [stopped] at edge
          cases edge

end HedgeChannelInstallation.SuccessorPath

namespace HedgeWitness

variable {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    (w : HedgeWitness graph query.jointNumerator)

/-- Stop at the first original outcome or conditioner on the actual
composed flow.  A stopped vertex does not fall through to the old policy. -/
def conditionalBoundarySuccessor : ForestChild S := fun parent =>
  if query.jointNumerator.outcome parent then none else w.smallOutcomeFlowSuccessor parent

/-- Stopping selected transmitters preserves the old action-free domain
and every retained genuine arrow.  No receiving vertex is invented. -/
theorem conditionalBoundarySuccessor_wellFormed :
    childWellFormedBool w.smallOutcomeFlowNodes w.conditionalBoundarySuccessor = true := by
  apply List.all_eq_true.mpr
  intro parent member
  cases queried : query.jointNumerator.outcome parent with
  | true =>
      cases w.smallOutcomeFlowNodes parent <;>
        simp only [conditionalBoundarySuccessor, queried, if_true]
  | false =>
      have old := (List.all_eq_true.mp w.smallOutcomeFlowSuccessor_wellFormed) parent member
      simpa only [conditionalBoundarySuccessor, queried, Bool.false_eq_true, if_false] using old

/-- A new sink is either an immediately queried vertex or an original
flow sink, already proved to belong to the same original numerator outcome. -/
theorem conditionalBoundarySinks_queried :
    NodeSet.Subset (keptSinks w.smallOutcomeFlowNodes w.conditionalBoundarySuccessor)
      (NodeSet.union query.outcome query.condition) := by
  intro node sink
  have parts := (keptSinks_iff w.smallOutcomeFlowNodes w.conditionalBoundarySuccessor node).mp sink
  cases queried : query.jointNumerator.outcome node with
  | true => exact queried
  | false =>
      have stopped : w.smallOutcomeFlowSuccessor node = none := by
        simpa only [conditionalBoundarySuccessor, queried, Bool.false_eq_true, if_false] using parts.2
      exact w.smallOutcomeFlowSinks_subset_outcome node
        ((keptSinks_iff w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor node).mpr ⟨parts.1, stopped⟩)

/-- Complete stopped-flow data from every original Small source.  The
domain still contains all mandatory Small rows, not just this source. -/
def conditionalBoundaryPath (source : Fin S.count) (inside : w.small source = true) :
    SuccessorPath w.smallOutcomeFlowNodes w.conditionalBoundarySuccessor source :=
  .ofForest w.smallOutcomeFlowNodes w.conditionalBoundarySuccessor w.conditionalBoundarySuccessor_wellFormed source
    (outcomeFlow_small_subset w source inside)

end HedgeWitness

/-- The hard side of an exhaustive finite source scan.  Its sole field is
proved by the constructor below; callers of that constructor do not supply
this boundary as another assumption of an irreducible terminal. -/
structure ConditionedSmallFlowBoundary {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    (w : HedgeWitness graph query.jointNumerator) : Type where
  encounters_condition : forall source, forall inside : w.small source = true,
    (w.conditionalBoundaryPath source inside).nodes.any query.condition = true

namespace ConditionedSmallFlowBoundary

variable {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    {w : HedgeWitness graph query.jointNumerator}

/-- Small cannot contain a queried outcome on the hard boundary.  Its
actual stopped path would be an unconditioned singleton, already covered
by the constructive countermodel branch of the scan. -/
theorem small_avoids_outcome (boundary : ConditionedSmallFlowBoundary w) : NodeSet.Disjoint w.small query.outcome := by
  intro source inside
  cases selected : query.outcome source with
  | false => rfl
  | true =>
      have queried : query.jointNumerator.outcome source = true := by
        change (query.outcome source || query.condition source) = true
        rw [selected]
        rfl
      have stopped : w.conditionalBoundarySuccessor source = none := by
        simp only [HedgeWitness.conditionalBoundarySuccessor, queried, if_true]
      have single := (w.conditionalBoundaryPath source inside).nodes_eq_singleton_of_source_stopped stopped
      have encountered := boundary.encounters_condition source inside
      rw [single] at encountered
      simp only [List.any_cons, List.any_nil, Bool.or_false] at encountered
      have free := query.outcome_condition_disjoint source selected
      rw [free] at encountered
      cases encountered

private theorem reachable_member (edge : Fin S.count -> Fin S.count -> Bool)
    (nodes : List (Fin S.count)) (source : Fin S.count) (starts : nodes.head? = some source)
    (consecutive : Consecutive (fun parent child => edge parent child = true) nodes)
    (target : Fin S.count) (member : target ∈ nodes) : FiniteReachability.Reachable edge source target := by
  induction nodes generalizing source with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      have same : head = source := Option.some.inj starts
      subst head
      rcases List.mem_cons.mp member with equal | later
      · subst target
        exact FiniteReachability.Reachable.refl edge source
      · cases tail with
        | nil => cases later
        | cons next rest =>
            exact FiniteReachability.Reachable.prepend consecutive.1
              (inductionHypothesis next rfl consecutive.2 later)

/-- Every Small source gives actual latest-pivot data.  The initial
conditioner is the first member found on its stopped path, and all retained
arrows are replayed in the full original incoming action cut.  Reachability
is used only propositionally; conditioner and pivot data come from searches. -/
def latestPivot (boundary : ConditionedSmallFlowBoundary w)
    (source : Fin S.count) (inside : w.small source = true) : LatestConditionalPivot graph query source := by
  let path := w.conditionalBoundaryPath source inside
  let encountered := boundary.encounters_condition source inside
  let conditioner := listFirstAny path.nodes query.condition encountered
  have selected := listFirstAny_pred path.nodes query.condition encountered
  have member := listFirstAny_mem path.nodes query.condition encountered
  have arrows : Consecutive (fun parent child => mutilatedDirected S query.action parent child = true) path.nodes := by
    apply Consecutive.mono (fun parent child edge => ?_) path.nodes path.consecutive
    have parts := childWellFormed_edge w.smallOutcomeFlowNodes w.conditionalBoundarySuccessor
      w.conditionalBoundarySuccessor_wellFormed edge
    have free : query.action child = false := outcomeFlow_avoids_action w child parts.2.1
    simpa only [mutilatedDirected, free, Bool.false_eq_true, if_false] using parts.2.2
  have reaches := reachable_member (mutilatedDirected S query.action) path.nodes source path.starts arrows conditioner member
  have bounded := FiniteReachability.boundedWalk_of_reachable finBeq (NodeSet.enumerated S)
    (mutilatedDirected S query.action) finBeq_eq_true_iff (NodeSet.mem_enumerated S) reaches
  rw [NodeSet.length_enumerated] at bounded
  have actual := (FiniteReachability.within_eq_true_iff_boundedWalk finBeq (NodeSet.enumerated S)
    (mutilatedDirected S query.action) finBeq_eq_true_iff (NodeSet.mem_enumerated S) _ _ _).mpr bounded
  exact LatestConditionalPivot.ofReachableConditioner graph query source conditioner selected actual

end ConditionedSmallFlowBoundary

/-! ## An exhaustive scan returns a semantic pair or the proved hard boundary -/

/-- Exhaust all original Small sources using the first-queried stopping
policy.  A successful branch returns actual positive countermodels for the
unchanged conditional query.  The other branch proves its boundary for every
Small source, not merely for the stored action root or one chosen route.
No semantic identifiability test, excluded middle, or choice is involved. -/
noncomputable def HedgeWitness.conditionalCounterexampleOrSmallFlowBoundary
    {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S) :
    Sum (ConditionalCounterexampleIn (GraphModelClass.positive graph) query) (ConditionedSmallFlowBoundary w) := by
  let sources := (NodeSet.members w.small).attach
  let free : { source // source ∈ NodeSet.members w.small } -> Bool := fun source =>
    !((w.conditionalBoundaryPath source.val ((NodeSet.mem_members_iff _ _).mp source.property)).nodes.any query.condition)
  cases found : sources.any free with
  | true =>
      let chosen := listFirstAny sources free found
      have tested := listFirstAny_pred sources free found
      have inside : w.small chosen.val = true := (NodeSet.mem_members_iff _ _).mp chosen.property
      let path := w.conditionalBoundaryPath chosen.val inside
      have answer : path.nodes.any query.condition = false := by
        simpa only [free, Bool.not_eq_true'] using tested
      have unconditioned : forall child, child ∈ path.nodes -> query.condition child = false := by
        intro child member
        cases selected : query.condition child with
        | false => rfl
        | true =>
            have present : path.nodes.any query.condition = true := List.any_eq_true.mpr ⟨child, member, selected⟩
            rw [answer] at present
            cases present
      exact .inl (conditionalCounterexampleOfSuccessorPath w rich w.smallOutcomeFlowNodes w.conditionalBoundarySuccessor
        w.conditionalBoundarySuccessor_wellFormed (outcomeFlow_small_subset w) (outcomeFlow_avoids_action w)
        w.conditionalBoundarySinks_queried chosen.val inside path unconditioned)
  | false =>
      refine .inr ⟨?_⟩
      intro source inside
      let candidate : { source // source ∈ NodeSet.members w.small } :=
        ⟨source, (NodeSet.mem_members_iff _ _).mpr inside⟩
      cases answer : (w.conditionalBoundaryPath source inside).nodes.any query.condition with
      | true => rfl
      | false =>
          have freeCandidate : free candidate = true := by
            change Bool.not ((w.conditionalBoundaryPath source inside).nodes.any query.condition) = true
            rw [answer]
            rfl
          have present : sources.any free = true := List.any_eq_true.mpr ⟨candidate, List.mem_attach _ _, freeCandidate⟩
          rw [found] at present
          cases present

end Causality
end Thesis
