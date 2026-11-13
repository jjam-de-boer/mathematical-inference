import Thesis.CausalTransport.ConditionalFailureIncidenceEdges

namespace Thesis
namespace Causality

open PathSpecification Probability FiniteBooleanInteraction
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S} {query : ConditionalKernelQuery S}

/-!
# Every actual retained approach contact is connected to original Small

The complete mandatory-source prefixes were constructed before the actual
fork exit policy.  At every proper prefix vertex their old stopped map agrees
with the new map, and the noncontact column is a supported outcome-even pair.
Consequently every consecutive edge of the literal original prefix is also
an edge of the actual tested incidence graph.

The receiving endpoint is retained in this theorem.  In particular a prefix
ending at a fork remains a complete connection to that fork even though the
new policy then resumes it into a path head.  No false claim that the new map
stops at that fork is used.  Shared prefixes, merged branches, zero-edge
approaches and Small/core overlaps are all permitted.

Every vertex in the actual approach union therefore has an incidence walk
back to some original Small source.  Original finite walk shortening bounds
the final search by the unchanged observed count.  If the outcome component
meets any such vertex, its precise outcome-to-Small test succeeds and the
already proved connection-to-countermodel constructor applies.

This closes the approach side of global connectivity.  The remaining
normalized-path/activation argument must prove that the actual outcome
component meets this actual union for the terminal construction.  No arbitrary
pivot or supplied contact flag is asserted to make that fact automatic.
-/

namespace ConditionalBackdoorPathNormalForm

variable {w : HedgeWitness graph query.jointNumerator}
    (boundary : ConditionedSmallFlowBoundary w) (pivot : RetainedConditionalPivot query)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (forest : ConditionalCutColliderActivationForest query pivot.node)

-- Work on literal sublists of one actual approach.  Membership is carried
-- through the induction because an old stopped-map arrow by itself does not
-- prove that its source belongs to this retained union.
private theorem approach_consecutive (source : Fin S.count) (inside : w.small source = true) :
    forall nodes : List (Fin S.count),
      (forall node, node ∈ nodes -> node ∈ (normal.forkApproachPath boundary pivot forest source inside).nodes) ->
      Consecutive (fun parent child =>
        w.smallInteractionStopSuccessor (normal.forkAbsorptionTargets pivot forest) parent = some child) nodes ->
      Consecutive (fun parent child => normal.forkPairIncidence boundary pivot forest parent child = true) nodes
  | [], _, _ => True.intro
  | [_], _, _ => True.intro
  | parent :: next :: rest, listed, consecutive => by
      have oldEdge := consecutive.1
      have retained := normal.forkApproachPath_retained boundary pivot forest source inside parent
        (listed parent (List.mem_cons.mpr (Or.inl rfl)))
      have noncontact : normal.forkAbsorptionTargets pivot forest parent = false := by
        cases target : normal.forkAbsorptionTargets pivot forest parent with
        | false => rfl
        | true => simp only [HedgeWitness.smallInteractionStopSuccessor, target, if_true, reduceCtorEq] at oldEdge
      have newEdge : normal.forkAbsorptionSuccessor boundary pivot forest parent = some next := by
        rw [normal.forkAbsorptionSuccessor_noncontact boundary pivot forest parent retained noncontact]
        simpa only [HedgeWitness.smallInteractionStopSuccessor, noncontact, Bool.false_eq_true, if_false] using oldEdge
      exact ⟨normal.forkApproach_incidence_edge boundary pivot forest retained noncontact newEdge,
        approach_consecutive source inside (next :: rest)
          (fun node member => listed node (List.mem_cons.mpr (Or.inr member))) consecutive.2⟩

/-- Every genuine edge of this computed first-contact prefix is an actual
incidence edge.  The receiving endpoint is included without being resumed
inside this list or required to stop in the new fork-aware policy. -/
theorem forkApproachPath_incidence_consecutive (source : Fin S.count) (inside : w.small source = true) :
    Consecutive (fun parent child => normal.forkPairIncidence boundary pivot forest parent child = true)
      (normal.forkApproachPath boundary pivot forest source inside).nodes :=
  normal.approach_consecutive boundary pivot forest source inside _ (fun _ listed => listed)
    (normal.forkApproachPath boundary pivot forest source inside).consecutive

/-- An original Small source is connected to every actually visited
approach row, not only to the final head, trace or fork receiving endpoint. -/
theorem forkApproachPath_reaches_member (source : Fin S.count) (inside : w.small source = true)
    (node : Fin S.count) (visited : node ∈ (normal.forkApproachPath boundary pivot forest source inside).nodes) :
    FiniteReachability.Reachable (normal.forkPairIncidence boundary pivot forest) source node :=
  LinearSignal.pairIncidence_reaches_member _ _ _ _ _ source
    (normal.forkApproachPath boundary pivot forest source inside).starts
    (normal.forkApproachPath_incidence_consecutive boundary pivot forest source inside) node visited

/-- Reverse incidence, not causal arrows, connects each actual retained
prefix row back to the same genuine original Small source. -/
theorem forkApproachPath_member_reaches_source (source : Fin S.count) (inside : w.small source = true)
    (node : Fin S.count) (visited : node ∈ (normal.forkApproachPath boundary pivot forest source inside).nodes) :
    FiniteReachability.Reachable (normal.forkPairIncidence boundary pivot forest) node source :=
  LinearSignal.pairIncidence_reachable_swap _ _ _ _
    (normal.forkApproachPath_reaches_member boundary pivot forest source inside node visited)

/-- Every row in the complete actual approach union reaches an original
Small row in the real pair graph.  Union membership is used inside Prop;
the later successful test still computes its own target and route data. -/
theorem forkApproachNodes_reaches_small (node : Fin S.count)
    (retained : normal.forkApproachNodes boundary pivot forest node = true) :
    Exists fun source : Fin S.count => w.small source = true ∧
      FiniteReachability.Reachable (normal.forkPairIncidence boundary pivot forest) node source := by
  have receives : NodeSet.Subset query.condition (normal.forkAbsorptionTargets pivot forest) := fun row selected =>
    NodeSet.subset_union_left _ _ row (NodeSet.subset_union_right _ _ row selected)
  rcases (boundary.absorbingNodes_eq_true_iff (normal.forkAbsorptionTargets pivot forest) receives node).mp retained with
    ⟨source, inside, visited⟩
  exact ⟨source, inside, normal.forkApproachPath_member_reaches_source boundary pivot forest source inside node visited⟩

/-- Any proved actual connection to a genuine Small row is recognized
by the finite all-Small search at the original observed-count bound. -/
theorem forkOutcomeReachesSmallTest_of_reachable_small (source : Fin S.count) (inside : w.small source = true)
    (connection : FiniteReachability.Reachable (normal.forkPairIncidence boundary pivot forest)
      (normal.forkOutcomeIncidenceRow boundary pivot forest) source) :
    normal.forkOutcomeReachesSmallTest boundary pivot forest S.count = true := by
  apply List.any_eq_true.mpr
  exact ⟨source, (NodeSet.mem_members_iff w.small source).mpr inside,
    LinearSignal.pairIncidence_within_of_reachable _ _ _ _ connection⟩

/-- Reaching any actual mandatory approach contact is sufficient.  Its
whole literal prefix supplies the rest of the connection to an original
Small source; no Small-membership flag for the contact itself is needed. -/
theorem forkOutcomeReachesSmallTest_of_approach_contact (node : Fin S.count)
    (retained : normal.forkApproachNodes boundary pivot forest node = true)
    (connection : FiniteReachability.Reachable (normal.forkPairIncidence boundary pivot forest)
      (normal.forkOutcomeIncidenceRow boundary pivot forest) node) :
    normal.forkOutcomeReachesSmallTest boundary pivot forest S.count = true := by
  rcases normal.forkApproachNodes_reaches_small boundary pivot forest node retained with ⟨source, inside, rest⟩
  exact normal.forkOutcomeReachesSmallTest_of_reachable_small boundary pivot forest source inside
    (LinearSignal.pairIncidence_reachable_trans _ _ _ _ connection rest)

/-- If the true starting incidence already belongs to an actual mandatory
approach, no normalized-path connection step is needed.  The empty first
walk plus the proved approach route supplies the successful complete test. -/
theorem forkOutcomeReachesSmallTest_of_starting_approach
    (retained : normal.forkApproachNodes boundary pivot forest
      (normal.forkOutcomeIncidenceRow boundary pivot forest) = true) :
    normal.forkOutcomeReachesSmallTest boundary pivot forest S.count = true :=
  normal.forkOutcomeReachesSmallTest_of_approach_contact boundary pivot forest _ retained
    (FiniteReachability.Reachable.refl _ _)

end ConditionalBackdoorPathNormalForm
end Causality
end Thesis
