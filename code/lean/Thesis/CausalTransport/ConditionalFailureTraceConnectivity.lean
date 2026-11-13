import Thesis.CausalTransport.ConditionalFailureApproachConnectivity

namespace Thesis
namespace Causality

open PathSpecification Probability FiniteBooleanInteraction
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S} {query : ConditionalKernelQuery S}

/-!
# Complete actual activation traces connect to their normalized collider

Every unconditioned transmitter in the pruned common activation policy has
a supported outcome-even own/successor pair column.  Hence each edge of a
collider's literal complete trace is an edge of the actual incidence graph.
Every visited trace row is connected back to that same original collider,
including a conditioned sink, a shared suffix, or a zero-edge activation.

Only actual trace union membership is used.  The larger auxiliary activation
domain need not be disjoint from the normalized path, and merged branches
are not replaced by independently installed copies.  The genuine collider
is a path head; the argument supplies no extra selected-head or trace-cover
readiness field to a terminal caller.

Together with `ConditionalFailureApproachConnectivity`, a true outcome-to-
collider connection and a mandatory approach contact anywhere on that trace
close the complete finite outcome-to-Small search.  The remaining normalized
path argument must derive such a contact or a direct approach connection;
these trace lemmas do not assert that every arbitrary pivot does so.
-/

namespace ConditionalBackdoorPathNormalForm

variable {w : HedgeWitness graph query.jointNumerator}
    (boundary : ConditionedSmallFlowBoundary w) (pivot : RetainedConditionalPivot query)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (forest : ConditionalCutColliderActivationForest query pivot.node)

/-- Every genuine trace edge is a tested pair edge on the full original
cube.  The real restricted map's well-formedness derives transmitter
membership, so no separate domain-wide row coverage assumption is needed. -/
theorem activationTracePath_incidence_consecutive (collider : Fin S.count)
    (seed : normal.colliderSeeds collider = true) :
    Consecutive (fun parent child => normal.forkPairIncidence boundary pivot forest parent child = true)
      (normal.activationTracePath pivot forest collider seed).nodes := by
  apply Consecutive.mono (fun parent child edge => ?_) _
    (normal.activationTracePath pivot forest collider seed).consecutive
  have selected := (childWellFormed_edge _ _ (normal.activationTraceSuccessor_wellFormed pivot forest) edge).1
  exact normal.activationTrace_incidence_edge boundary pivot forest selected edge

/-- The actual collider is connected to every row in its whole actual
trace, not just to an independently supplied activation endpoint. -/
theorem activationTracePath_reaches_member (collider : Fin S.count)
    (seed : normal.colliderSeeds collider = true) (node : Fin S.count)
    (visited : node ∈ (normal.activationTracePath pivot forest collider seed).nodes) :
    FiniteReachability.Reachable (normal.forkPairIncidence boundary pivot forest) collider node :=
  LinearSignal.pairIncidence_reaches_member _ _ _ _ _ collider
    (normal.activationTracePath pivot forest collider seed).starts
    (normal.activationTracePath_incidence_consecutive boundary pivot forest collider seed) node visited

/-- Incidence symmetry sends every actual visited trace row back to its
original collider, without reversing a legal directed activation arrow. -/
theorem activationTracePath_member_reaches_seed (collider : Fin S.count)
    (seed : normal.colliderSeeds collider = true) (node : Fin S.count)
    (visited : node ∈ (normal.activationTracePath pivot forest collider seed).nodes) :
    FiniteReachability.Reachable (normal.forkPairIncidence boundary pivot forest) node collider :=
  LinearSignal.pairIncidence_reachable_swap _ _ _ _
    (normal.activationTracePath_reaches_member boundary pivot forest collider seed node visited)

/-- Every row of the real pruned trace union is connected to a genuine
original collider head.  The finite union's existential is unpacked only
inside this proposition, not to select route or collider data into `Type`. -/
theorem activationTraceNodes_reaches_head (node : Fin S.count)
    (selected : normal.activationTraceNodes pivot forest node = true) :
    Exists fun collider : Fin S.count => normal.colliderSeeds collider = true ∧ normal.pathHeads collider = true ∧
      FiniteReachability.Reachable (normal.forkPairIncidence boundary pivot forest) node collider := by
  unfold activationTraceNodes at selected
  rcases List.any_eq_true.mp selected with ⟨entry, _listed, visited⟩
  have seed := (NodeSet.mem_members_iff normal.colliderSeeds entry.val).mp entry.property
  exact ⟨entry.val, seed, normal.colliderSeeds_subset_pathHeads pivot entry.val seed,
    normal.activationTracePath_member_reaches_seed boundary pivot forest entry.val seed node (of_decide_eq_true visited)⟩

/-- If the outcome component reaches this genuine collider and any row
of its trace is an actual mandatory approach contact, the full finite Small
search succeeds.  Conditioned trace sinks and arbitrary Small overlaps are
covered by the same proved whole-trace/whole-approach connection. -/
theorem forkOutcomeReachesSmallTest_of_trace_contact (collider : Fin S.count)
    (seed : normal.colliderSeeds collider = true) (node : Fin S.count)
    (visited : node ∈ (normal.activationTracePath pivot forest collider seed).nodes)
    (retained : normal.forkApproachNodes boundary pivot forest node = true)
    (connection : FiniteReachability.Reachable (normal.forkPairIncidence boundary pivot forest)
      (normal.forkOutcomeIncidenceRow boundary pivot forest) collider) :
    normal.forkOutcomeReachesSmallTest boundary pivot forest S.count = true :=
  normal.forkOutcomeReachesSmallTest_of_approach_contact boundary pivot forest node retained
    (LinearSignal.pairIncidence_reachable_trans _ _ _ _ connection
      (normal.activationTracePath_reaches_member boundary pivot forest collider seed node visited))

end ConditionalBackdoorPathNormalForm
end Causality
end Thesis
