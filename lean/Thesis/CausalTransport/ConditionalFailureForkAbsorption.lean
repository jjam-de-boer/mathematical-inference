import Thesis.CausalTransport.ConditionalFailureSmallAbsorption
import Thesis.CausalTransport.ActivePathForkRouting

namespace Thesis
namespace Causality

open PathSpecification Probability FiniteBooleanInteraction
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S} {query : ConditionalKernelQuery S}

/-!
# All-Small absorption with actual normalized-fork exits

The ordinary first-interaction absorber can retain an omitted normalized fork
as a new row while giving it a different outgoing edge from its old two path
inputs.  Its observed column can then affect four rows, and a real prefix
read need not vanish.  Here a mandatory-source path stops earlier: at its
first completed-interaction row or omitted observed path vertex.

At a receiving interaction row the policy stops.  At an omitted path vertex
it takes the actual outgoing path-head exit constructed by `ActivePathForkRouting`.
Elsewhere it retains the original boundary-flow successor.  The domain is
the completed core plus the union of all actual stopped Small-source prefixes.
Exit destinations are already in that core, so no extra route or sink flag
is needed.  Original Small coverage, well-formedness, action freedom and
receiving-sink coverage are proved from those actual data.

Whole-cube conservation and original-cylinder matching remain valid.  More
importantly, a fork's chosen receiver already reads that original fork in
the fused path/activation signal.  The new XOR parent mask cancels that one
input, retaining the receiver's own bit and all original reserved inputs.
This is a proved parity-aware routing operation, not yet the universal
supported-direction theorem: contacts at actual heads and the full remaining
outside-Small partition still require the graph-to-direction argument.
-/

namespace ConditionalBackdoorPathNormalForm

variable {w : HedgeWitness graph query.jointNumerator}
    (boundary : ConditionedSmallFlowBoundary w) (pivot : RetainedConditionalPivot query)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (forest : ConditionalCutColliderActivationForest query pivot.node)

private theorem endpoints_ne : pivot.node ≠ normal.outcome := by
  intro same
  have free := query.outcome_condition_disjoint normal.outcome normal.outcome_selected
  rw [← same, pivot.selected] at free
  cases free

/-- Stop each original Small-source path at its first core or omitted
path contact.  Every original conditioner is still a stopping target. -/
def forkAbsorptionTargets : NodeSet S := NodeSet.union (normal.smallInteractionRows pivot forest) normal.cutPath.forkNodes

private theorem receives_condition : NodeSet.Subset query.condition (normal.forkAbsorptionTargets pivot forest) :=
  fun node selected => NodeSet.subset_union_left _ _ node (NodeSet.subset_union_right _ _ node selected)

/-- The actual complete prefix union from all mandatory sources.  An
omitted path contact is retained, not discarded merely because it lacks a head. -/
def forkApproachNodes : NodeSet S := boundary.absorbingNodes (normal.forkAbsorptionTargets pivot forest)
  (normal.receives_condition pivot forest)

/-- Retain the complete actual core and every mandatory-source prefix. -/
def forkAbsorbedInteractionRows : NodeSet S := NodeSet.union (normal.smallInteractionRows pivot forest)
  (normal.forkApproachNodes boundary pivot forest)

/-- One common map: stop core rows, take actual path-head exits at
retained omitted vertices, and otherwise replay the original boundary policy.
Off-domain vertices have no outgoing continuation. -/
def forkAbsorptionSuccessor : ForestChild S := fun parent =>
  if normal.smallInteractionRows pivot forest parent then none else
    if normal.forkApproachNodes boundary pivot forest parent then
      if normal.cutPath.forkNodes parent then normal.cutPath.forkSuccessor (normal.endpoints_ne pivot) parent
      else w.conditionalBoundarySuccessor parent
    else none

private theorem heads_in_core (child : Fin S.count)
    (head : ActivePathInput.headRows graph
      (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes child = true) :
    normal.smallInteractionRows pivot forest child = true :=
  NodeSet.subset_union_left _ _ child (NodeSet.subset_union_left _ _ child head)

private theorem ordinary_successor_closed (parent child : Fin S.count)
    (retained : normal.forkApproachNodes boundary pivot forest parent = true)
    (outside : normal.smallInteractionRows pivot forest parent = false)
    (notFork : normal.cutPath.forkNodes parent = false)
    (edge : w.conditionalBoundarySuccessor parent = some child) :
    normal.forkApproachNodes boundary pivot forest child = true := by
  apply boundary.absorbingNodes_successor_closed (normal.forkAbsorptionTargets pivot forest)
    (normal.receives_condition pivot forest) parent child retained
  simpa only [HedgeWitness.smallInteractionStopSuccessor, forkAbsorptionTargets, NodeSet.union,
    outside, notFork, Bool.false_or, Bool.false_eq_true, if_false] using edge

/-- Every mandatory Small source starts a retained prefix, independently
of whether its endpoint is a head, activation row or omitted path vertex. -/
theorem forkAbsorbedInteraction_contains_small : NodeSet.Subset w.small (normal.forkAbsorbedInteractionRows boundary pivot forest) := by
  intro node inside
  exact NodeSet.subset_union_right _ _ node
    (boundary.small_subset_absorbingNodes (normal.forkAbsorptionTargets pivot forest) (normal.receives_condition pivot forest) node inside)

/-- New prefixes inherit the original action-free flow domain; the core
inherits its existing graph certificates.  Fork exits change arrows, not masks. -/
theorem forkAbsorbedInteraction_action_free (node : Fin S.count)
    (selected : normal.forkAbsorbedInteractionRows boundary pivot forest node = true) : query.action node = false := by
  rcases Bool.or_eq_true_iff.mp selected with core | routed
  · exact normal.smallInteractionRows_action_free pivot forest node core
  · exact boundary.absorbingNodes_action_free (normal.forkAbsorptionTargets pivot forest)
      (normal.receives_condition pivot forest) node routed

/-- The complete common map is well formed on its actual full domain.
Ordinary prefixes are successor-closed, and every fork exit enters an
original head already retained in the core.  No auxiliary arrow is invented. -/
theorem forkAbsorptionSuccessor_wellFormed :
    childWellFormedBool (normal.forkAbsorbedInteractionRows boundary pivot forest)
      (normal.forkAbsorptionSuccessor boundary pivot forest) = true := by
  apply List.all_eq_true.mpr
  intro parent _member
  cases core : normal.smallInteractionRows pivot forest parent with
  | true =>
      have parentIn : normal.forkAbsorbedInteractionRows boundary pivot forest parent = true :=
        NodeSet.subset_union_left _ (normal.forkApproachNodes boundary pivot forest) parent core
      simp only [forkAbsorptionSuccessor, core, if_true, parentIn]
  | false =>
      cases retained : normal.forkApproachNodes boundary pivot forest parent with
      | false => simp only [forkAbsorptionSuccessor, forkAbsorbedInteractionRows, NodeSet.union, core,
          retained, Bool.false_eq_true, if_false, Bool.false_or]
      | true =>
          have parentIn : normal.forkAbsorbedInteractionRows boundary pivot forest parent = true :=
            NodeSet.subset_union_right (normal.smallInteractionRows pivot forest) _ parent retained
          cases fork : normal.cutPath.forkNodes parent with
          | true =>
              cases next : normal.cutPath.forkSuccessor (normal.endpoints_ne pivot) parent with
              | none => simp only [forkAbsorptionSuccessor, core, retained, fork, Bool.false_eq_true, if_false, if_true, next, parentIn]
              | some child =>
                  have input := (normal.cutPath.forkSuccessor_edge (normal.endpoints_ne pivot) next).2
                  have childIn : normal.forkAbsorbedInteractionRows boundary pivot forest child = true :=
                    NodeSet.subset_union_left _ (normal.forkApproachNodes boundary pivot forest) child
                    (normal.heads_in_core pivot forest child (ActivePathInput.incomingEdge_head input))
                  have declared : S.directed parent child = true :=
                    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp input).2).1).1
                  simp only [forkAbsorptionSuccessor, core, retained, fork, Bool.false_eq_true, if_false, if_true,
                    next, parentIn, childIn, declared, Bool.and_self]
          | false =>
              cases next : w.conditionalBoundarySuccessor parent with
              | none => simp only [forkAbsorptionSuccessor, core, retained, fork, Bool.false_eq_true, if_false, if_true, next, parentIn]
              | some child =>
                  have kept := normal.ordinary_successor_closed boundary pivot forest parent child retained core fork next
                  have childIn : normal.forkAbsorbedInteractionRows boundary pivot forest child = true :=
                    NodeSet.subset_union_right (normal.smallInteractionRows pivot forest) _ child kept
                  have declared := (childWellFormed_edge w.smallOutcomeFlowNodes w.conditionalBoundarySuccessor
                    w.conditionalBoundarySuccessor_wellFormed next).2.2
                  simp only [forkAbsorptionSuccessor, core, retained, fork, Bool.false_eq_true, if_false, if_true,
                    next, parentIn, childIn, declared, Bool.and_self]

/-- Every receiving core row stops, including unvisited conditioners.
No fork or boundary continuation falls through this first policy clause. -/
theorem forkAbsorptionSuccessor_stops_core (node : Fin S.count)
    (selected : normal.smallInteractionRows pivot forest node = true) :
    normal.forkAbsorptionSuccessor boundary pivot forest node = none := by
  simp only [forkAbsorptionSuccessor, selected, if_true]

/-- A retained noncore fork has a real exit, while a retained nonfork
cannot be a stopped noncontact in a complete prefix.  Hence every sink is
an actual receiving row without another sink-coverage assumption. -/
theorem forkAbsorptionSinks_subset_core :
    NodeSet.Subset (keptSinks (normal.forkAbsorbedInteractionRows boundary pivot forest)
      (normal.forkAbsorptionSuccessor boundary pivot forest)) (normal.smallInteractionRows pivot forest) := by
  intro node sink
  have parts := (keptSinks_iff _ _ node).mp sink
  cases core : normal.smallInteractionRows pivot forest node with
  | true => rfl
  | false =>
      have retained : normal.forkApproachNodes boundary pivot forest node = true := by
        simpa only [forkAbsorbedInteractionRows, NodeSet.union, core, Bool.false_or] using parts.1
      cases fork : normal.cutPath.forkNodes node with
      | true =>
          have stopped : normal.cutPath.forkSuccessor (normal.endpoints_ne pivot) node = none := by
            simpa only [forkAbsorptionSuccessor, core, retained, fork, Bool.false_eq_true, if_false, if_true] using parts.2
          have present := normal.cutPath.forkSuccessor_isSome (normal.endpoints_ne pivot) node fork
          rw [stopped] at present
          cases present
      | false =>
          have oldStopped : w.smallInteractionStopSuccessor (normal.forkAbsorptionTargets pivot forest) node = none := by
            have stopped : w.conditionalBoundarySuccessor node = none := by
              simpa only [forkAbsorptionSuccessor, core, retained, fork, Bool.false_eq_true, if_false, if_true] using parts.2
            simpa only [HedgeWitness.smallInteractionStopSuccessor, forkAbsorptionTargets, NodeSet.union,
              core, fork, Bool.false_or, Bool.false_eq_true, if_false] using stopped
          rcases (boundary.absorbingNodes_eq_true_iff (normal.forkAbsorptionTargets pivot forest)
            (normal.receives_condition pivot forest) node).mp retained with ⟨source, inside, visited⟩
          let path := boundary.interactionStopPath (normal.forkAbsorptionTargets pivot forest)
            (normal.receives_condition pivot forest) source inside
          have same := path.eq_endpoint_of_stopped node visited oldStopped
          have contacted := boundary.interactionStopPath_endpoint_in_interaction (normal.forkAbsorptionTargets pivot forest)
            (normal.receives_condition pivot forest) source inside
          change normal.forkAbsorptionTargets pivot forest path.endpoint = true at contacted
          rw [← same] at contacted
          simp only [forkAbsorptionTargets, NodeSet.union, core, fork, Bool.false_or] at contacted
          cases contacted

/-- The actual fork-aware legal installation uses the original fused
path/activation signal, with one own bit at every receiving mechanism. -/
def forkAbsorbedInteractionSignal : LinearSignal graph := (normal.activationInteractionSignal pivot forest).absorbSuccessor
  (normal.smallInteractionRows pivot forest) (normal.forkAbsorptionSuccessor boundary pivot forest)

/-- A real omitted path vertex cannot belong to the retained activation
union.  Actual path/trace intersections are collider seeds, and each such
seed is a head; this contradicts the executable omitted-head classifier.
The statement concerns the actual trace union, not all auxiliary ancestors. -/
theorem forkNodes_activationTrace_free (parent : Fin S.count)
    (fork : normal.cutPath.forkNodes parent = true) :
    normal.activationTraceNodes pivot forest parent = false := by
  have parts := (normal.cutPath.forkNodes_eq_true_iff parent).mp fork
  cases selected : normal.activationTraceNodes pivot forest parent with
  | false => rfl
  | true =>
      have seed := (normal.activationTraceNodes_intersection_iff_collider pivot forest parent parts.1).mp selected
      have head := normal.colliderSeeds_subset_pathHeads pivot parent seed
      change ActivePathInput.headRows graph
        (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes parent = true at head
      rw [parts.2] at head
      cases head

/-- Fusion with activation does not remove an omitted vertex's original
outgoing path input.  That vertex is outside the actual activation union,
so its activation successor is absent.  This is the nonzero read that the
fork-aware absorber must cancel, rather than a zero-prefix-read premise. -/
theorem forkInput_in_activationInteraction {parent child : Fin S.count}
    (fork : normal.cutPath.forkNodes parent = true)
    (input : ActivePathInput.incomingEdge graph
      (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes (.observed parent) child = true) :
    (normal.activationInteractionSignal pivot forest).parentMask child parent = true := by
  have stopped : normal.activationTraceSuccessor pivot forest parent = none :=
    restrictChild_of_false (normal.forkNodes_activationTrace_free pivot forest parent fork)
  have head := ActivePathInput.incomingEdge_head input
  simp only [activationInteractionSignal, LinearSignal.absorbSuccessor, pathHeads,
    LinearSignal.ofActivePath, head, if_true, input, stopped, reduceCtorEq,
    decide_false, Bool.xor_false]

/-- A returned exit from an actual omitted vertex is exactly its computed
outgoing path-head exit.  The core-first and off-domain clauses cannot return
an edge, so neither clause hides an additional routing assumption. -/
theorem forkAbsorptionSuccessor_fork_edge {parent child : Fin S.count}
    (fork : normal.cutPath.forkNodes parent = true)
    (edge : normal.forkAbsorptionSuccessor boundary pivot forest parent = some child) :
    normal.cutPath.forkSuccessor (normal.endpoints_ne pivot) parent = some child := by
  cases core : normal.smallInteractionRows pivot forest parent with
  | true => simp only [forkAbsorptionSuccessor, core, if_true] at edge; cases edge
  | false =>
      cases retained : normal.forkApproachNodes boundary pivot forest parent with
      | false => simp only [forkAbsorptionSuccessor, core, retained, Bool.false_eq_true, if_false] at edge; cases edge
      | true => simpa only [forkAbsorptionSuccessor, core, retained, fork, Bool.false_eq_true,
          if_false, if_true] using edge

/-- Absorption cancels the chosen fork input in the *actual fused* signal.
The original path input survives activation fusion by the preceding theorem;
the new successor contributes the same bit once more.  XOR removes this one
duplicate read, without deleting an original root coordinate or own bit. -/
theorem forkAbsorbedInteraction_cancels_fork_input {parent child : Fin S.count}
    (fork : normal.cutPath.forkNodes parent = true)
    (edge : normal.forkAbsorptionSuccessor boundary pivot forest parent = some child) :
    (normal.forkAbsorbedInteractionSignal boundary pivot forest).parentMask child parent = false := by
  have actual := normal.forkAbsorptionSuccessor_fork_edge boundary pivot forest fork edge
  have input := (normal.cutPath.forkSuccessor_edge (normal.endpoints_ne pivot) actual).2
  have core := normal.heads_in_core pivot forest child (ActivePathInput.incomingEdge_head input)
  have original := normal.forkInput_in_activationInteraction pivot forest fork input
  simp only [forkAbsorbedInteractionSignal, LinearSignal.absorbSuccessor, core, if_true,
    original, edge, decide_true, Bool.xor_self]

/-- A receiving row retains each original parent input not routed into that
row by this layer.  Cancellation is local to the returned receiver, not a
blanket erasure of an omitted fork's other outgoing path input. -/
theorem forkAbsorbedInteraction_preserves_other_input (parent child : Fin S.count)
    (core : normal.smallInteractionRows pivot forest child = true)
    (other : normal.forkAbsorptionSuccessor boundary pivot forest parent ≠ some child) :
    (normal.forkAbsorbedInteractionSignal boundary pivot forest).parentMask child parent =
      (normal.activationInteractionSignal pivot forest).parentMask child parent := by
  simp only [forkAbsorbedInteractionSignal, LinearSignal.absorbSuccessor, core, if_true,
    other, decide_false, Bool.xor_false]

/-- All original reserved inputs survive at every receiving core row.
Only declared observed-parent masks are changed by the added routing layer. -/
theorem forkAbsorbedInteraction_preserves_root_input (child : Fin S.count)
    (core : normal.smallInteractionRows pivot forest child = true) (root : Fin (pairRootCount graph.binary)) :
    (normal.forkAbsorbedInteractionSignal boundary pivot forest).rootMask child root =
      (normal.activationInteractionSignal pivot forest).rootMask child root := by
  simp only [forkAbsorbedInteractionSignal, LinearSignal.absorbSuccessor, core, if_true]

/-- The background is the actual complete fork-aware union outside the
entire original Small set.  An overlap is installed once at its Small row. -/
def forkAbsorbedInteractionBackgroundRows : NodeSet S :=
  NodeSet.diff (normal.forkAbsorbedInteractionRows boundary pivot forest) w.small

/-- Whole-cube conservation includes all mandatory Small rows and every
actual fork-exit overlap, with no zero-tail or original-prefix-read premise. -/
theorem forkAbsorbedInteraction_phase (point : Cube graph) :
    ((normal.forkAbsorbedInteractionSignal boundary pivot forest).forestPhase
      (normal.forkAbsorbedInteractionRows boundary pivot forest)).value point =
      ((normal.activationInteractionSignal pivot forest).forestPhase (normal.smallInteractionRows pivot forest)).value point := by
  have enlarged : NodeSet.union (normal.smallInteractionRows pivot forest)
      (normal.forkAbsorbedInteractionRows boundary pivot forest) = normal.forkAbsorbedInteractionRows boundary pivot forest := by
    funext node
    change (normal.smallInteractionRows pivot forest node ||
      (normal.smallInteractionRows pivot forest node || normal.forkApproachNodes boundary pivot forest node)) =
      (normal.smallInteractionRows pivot forest node || normal.forkApproachNodes boundary pivot forest node)
    cases normal.smallInteractionRows pivot forest node <;> cases normal.forkApproachNodes boundary pivot forest node <;> rfl
  rw [← enlarged]
  exact LinearSignal.absorbSuccessor_forestPhase _ _ _ _
    (normal.forkAbsorptionSuccessor_wellFormed boundary pivot forest)
    (normal.forkAbsorptionSuccessor_stops_core boundary pivot forest)
    (normal.forkAbsorptionSinks_subset_core boundary pivot forest) point

/-- The fork-aware all-Small union preserves the actual outcome character
on the complete unchanged original action/condition cylinder. -/
theorem forkAbsorbedInteraction_conditionalPhase (point : Cube graph)
    (listed : point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count)
      (cubeMask graph (NodeSet.union query.action query.condition))) :
    ((normal.forkAbsorbedInteractionSignal boundary pivot forest).forestPhase
      (normal.forkAbsorbedInteractionRows boundary pivot forest)).value point =
      (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value point := by
  rw [normal.forkAbsorbedInteraction_phase boundary pivot forest point]
  exact normal.smallInteraction_conditionalPhase pivot forest point listed

/-- Every actual background row is outside the complete mandatory set. -/
theorem forkAbsorbedInteractionBackground_outside_small (node : Fin S.count)
    (selected : normal.forkAbsorbedInteractionBackgroundRows boundary pivot forest node = true) : w.small node = false := by
  simpa only [Bool.not_eq_true'] using (Bool.and_eq_true_iff.mp selected).2

/-- The outside-Small background retains the full original action cut. -/
theorem forkAbsorbedInteractionBackground_action_free (node : Fin S.count)
    (selected : normal.forkAbsorbedInteractionBackgroundRows boundary pivot forest node = true) : query.action node = false :=
  normal.forkAbsorbedInteraction_action_free boundary pivot forest node (Bool.and_eq_true_iff.mp selected).1

/-- Full Small coverage and whole-cube conservation give the exact matching
identity on the unchanged original evidence cylinder.  This does not yet
construct a balance direction: the remaining graph argument must make every
one of these actual outside-Small rows even while making the outcome odd. -/
theorem forkAbsorbedInteraction_matching (point : Cube graph)
    (listed : point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count)
      (cubeMask graph (NodeSet.union query.action query.condition))) :
    (((normal.forkAbsorbedInteractionSignal boundary pivot forest).forestPhase w.small).xor
      (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome)))).value point =
      (selectedPhase _ S.count (normal.forkAbsorbedInteractionBackgroundRows boundary pivot forest)
        (normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase).value point := by
  let data := normal.forkAbsorbedInteractionSignal boundary pivot forest
  let background := normal.forkAbsorbedInteractionBackgroundRows boundary pivot forest
  have partition : NodeSet.union w.small background = normal.forkAbsorbedInteractionRows boundary pivot forest :=
    NodeSet.union_diff_eq (normal.forkAbsorbedInteraction_contains_small boundary pivot forest)
  have whole : Bool.xor ((data.forestPhase w.small).value point)
      ((selectedPhase _ S.count background data.rowPhase).value point) =
      (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value point := by
    rw [LinearSignal.selectedPhase_value_eq_forestPhase,
      ← LinearSignal.forestPhase_union_of_disjoint data w.small background
        (NodeSet.disjoint_diff (normal.forkAbsorbedInteractionRows boundary pivot forest) w.small),
      partition]
    exact normal.forkAbsorbedInteraction_conditionalPhase boundary pivot forest point listed
  change Bool.xor ((data.forestPhase w.small).value point)
    ((maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value point) = _
  rw [← whole]
  generalize (data.forestPhase w.small).value point = smallBit
  generalize (selectedPhase _ S.count background data.rowPhase).value point = backgroundBit
  cases smallBit <;> cases backgroundBit <;> rfl

end ConditionalBackdoorPathNormalForm

/-! ## The remaining direction obligation feeds the semantic countermodel

All mandatory coverage, legality and original-cylinder matching obligations
have been discharged above.  The assembler below deliberately leaves only
the supported direction and its outcome/background parities as premises.
It accepts a corrected direction as well as the original path direction,
and never asks that actual nonzero prefix or fork inputs be zero.  These
direction premises are still the load-bearing universal theorem to prove;
having this assembler is not an inhabitant of `PublishedCompleteness`.
-/

/-- Package any genuinely supported odd-outcome/even-background direction
for the computed fork-aware signal.  Complete Small oddness is derived from
the proved full-cylinder matching identity, not supplied independently. -/
def HedgeChannelEnvironmentInstallation.ConditionalParityWitness.ofForkAbsorbedInteraction
    (w : HedgeWitness graph query.jointNumerator) (boundary : ConditionedSmallFlowBoundary w)
    (pivot : RetainedConditionalPivot query)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (forest : ConditionalCutColliderActivationForest query pivot.node)
    (direction : Cube graph)
    (supported : direction ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count)
      (cubeMask graph (NodeSet.union query.action query.condition)))
    (outcomeOdd : (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value direction = true)
    (backgroundEven : forall child, normal.forkAbsorbedInteractionBackgroundRows boundary pivot forest child = true ->
      ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase child).value direction = false) :
    ConditionalParityWitness w (normal.forkAbsorbedInteractionSignal boundary pivot forest)
      (normal.forkAbsorbedInteractionSignal boundary pivot forest) := by
  let data := normal.forkAbsorbedInteractionSignal boundary pivot forest
  have conserved := normal.forkAbsorbedInteraction_matching boundary pivot forest direction supported
  change Bool.xor ((data.forestPhase w.small).value direction)
    ((maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value direction) = _ at conserved
  rw [outcomeOdd, selectedPhase_value_eq_false_of_even _ _
    (normal.forkAbsorbedInteractionBackgroundRows boundary pivot forest) data.rowPhase direction backgroundEven] at conserved
  have smallOdd : (data.forestPhase w.small).value direction = true := by
    cases bit : (data.forestPhase w.small).value direction with
    | false => rw [bit] at conserved; cases conserved
    | true => rfl
  exact {
    outcomeMask := cubeMask graph (NodeSet.singleton normal.outcome)
    outcomeMask_member := normal.activationInteraction_outcome_mask_member pivot
    direction := direction
    direction_member := supported
    small_odd := smallOdd
    outcome_odd := outcomeOdd
    selected := normal.forkAbsorbedInteractionBackgroundRows boundary pivot forest
    selected_outside_small := normal.forkAbsorbedInteractionBackground_outside_small boundary pivot forest
    selected_avoids_action := normal.forkAbsorbedInteractionBackground_action_free boundary pivot forest
    selected_even := backgroundEven
    matching := normal.forkAbsorbedInteraction_matching boundary pivot forest
  }

/-- Convert that explicit remaining direction into positive models over
every original observed label.  No matched denominator, new common input,
Small-membership flag or coverage flag is required by this constructor. -/
noncomputable def conditionalCounterexampleOfForkAbsorbedInteraction
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (boundary : ConditionedSmallFlowBoundary w) (pivot : RetainedConditionalPivot query)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (forest : ConditionalCutColliderActivationForest query pivot.node)
    (direction : Cube graph)
    (supported : direction ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count)
      (cubeMask graph (NodeSet.union query.action query.condition)))
    (outcomeOdd : (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value direction = true)
    (backgroundEven : forall child, normal.forkAbsorbedInteractionBackgroundRows boundary pivot forest child = true ->
      ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase child).value direction = false) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  conditionalCounterexampleOfParity w rich (normal.forkAbsorbedInteractionSignal boundary pivot forest)
    (normal.forkAbsorbedInteractionSignal boundary pivot forest)
    (.ofForkAbsorbedInteraction w boundary pivot normal forest direction supported outcomeOdd backgroundEven)

end Causality
end Thesis
