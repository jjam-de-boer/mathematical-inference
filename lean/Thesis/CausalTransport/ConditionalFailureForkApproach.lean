import Thesis.CausalTransport.ConditionalFailureForkAbsorption
import Thesis.CausalTransport.HedgeChannelEnvironmentPrefixDirection

namespace Thesis
namespace Causality

open PathSpecification Probability FiniteBooleanInteraction
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S} {query : ConditionalKernelQuery S}

/-!+# Actual proper approaches have no hidden normalized-path prefix read

The first-core-only construction could let a proper prefix pass through an
omitted observed path fork.  That fork genuinely feeds an original receiving
row, so the original-prefix residual cannot be assumed zero.  The fork-aware
targets now stop at every such vertex as well as the complete core.

Consequently every proper approach vertex is off the normalized path and
outside the retained activation union.  Its original observed-parent column
is absent in the fused signal, and its new installed column is precisely its
own row plus its one actual successor row.  These are graph-derived facts,
not zero-tail or column-sparsity flags passed to a terminal constructor.

The literal old first-contact list is retained, even when its endpoint is a
fork which the new policy continues into a head.  The direction flips only
the proper prefix.  The continued endpoint has bit zero, so only successors
at flipped vertices matter.  Their maps agree, and the real installed signal
therefore has exactly the Small-source XOR receiving-contact row correction.
Support, original-root preservation and outcome-character preservation are
proved on the unchanged full query cylinder.

This supplies a universal approach-transfer operation at actual head, trace
or fork contacts.  It does not yet choose the globally successful combination
of such transfers: the outcome-side incidence/connectivity argument and all
outside-Small row parities are still required for conditional completeness.
-/

namespace ConditionalBackdoorPathNormalForm

variable {w : HedgeWitness graph query.jointNumerator}
    (boundary : ConditionedSmallFlowBoundary w) (pivot : RetainedConditionalPivot query)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (forest : ConditionalCutColliderActivationForest query pivot.node)

private theorem receives_condition : NodeSet.Subset query.condition (normal.forkAbsorptionTargets pivot forest) :=
  fun node selected => NodeSet.subset_union_left _ _ node (NodeSet.subset_union_right _ _ node selected)

/-! ## Combined contacts exclude original path and trace parent columns -/

/-- Every observed normalized-path vertex is either an incoming head in
the completed core or an omitted vertex in the executable fork mask.  No
on-path noncollider can evade the combined stopping targets. -/
theorem forkAbsorptionTargets_contains_path (parent : Fin S.count)
    (onPath : .observed parent ∈ normal.cutPath.nodes) : normal.forkAbsorptionTargets pivot forest parent = true := by
  cases head : normal.pathHeads parent with
  | true =>
      exact NodeSet.subset_union_left _ _ parent
        (NodeSet.subset_union_left _ _ parent (NodeSet.subset_union_left _ _ parent head))
  | false =>
      apply NodeSet.subset_union_right _ _ parent
      exact (normal.cutPath.forkNodes_eq_true_iff parent).mpr ⟨onPath, head⟩

/-- A proper noncontact is genuinely off the observed normalized path.
The implication uses the head/fork partition, not an assumed disjoint route. -/
theorem forkAbsorption_noncontact_off_path (parent : Fin S.count)
    (absent : normal.forkAbsorptionTargets pivot forest parent = false) : .observed parent ∉ normal.cutPath.nodes := by
  intro onPath
  exact Bool.false_ne_true (absent.symm.trans (normal.forkAbsorptionTargets_contains_path pivot forest parent onPath))

/-- No old path or activation parent input reads a noncontact vertex.
The path scan has no such observed member, and core omission removes that
vertex from the actual activation union and its restricted successor map. -/
theorem activationInteraction_noncontact_parent (parent child : Fin S.count)
    (absent : normal.forkAbsorptionTargets pivot forest parent = false) :
    (normal.activationInteractionSignal pivot forest).parentMask child parent = false := by
  have core := (Bool.or_eq_false_iff.mp absent).1
  have trace : normal.activationTraceNodes pivot forest parent = false :=
    (Bool.or_eq_false_iff.mp (Bool.or_eq_false_iff.mp core).1).2
  have stopped : normal.activationTraceSuccessor pivot forest parent = none := restrictChild_of_false trace
  have input : ActivePathInput.incomingEdge graph
      (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes (.observed parent) child = false := by
    apply Bool.eq_false_iff.mpr
    intro read
    exact normal.forkAbsorption_noncontact_off_path pivot forest parent absent
      (ActivePathInput.stepOnPath_members (Bool.and_eq_true_iff.mp read).1).1
  simp only [activationInteractionSignal, LinearSignal.absorbSuccessor, LinearSignal.ofActivePath,
    input, stopped, reduceCtorEq, decide_false, Bool.xor_self, ite_self]

/-- At a noncontact retained prefix vertex, the fork-aware policy replays
the one original boundary successor.  Neither the core nor fork branch can
alter a proper transmitting vertex. -/
theorem forkAbsorptionSuccessor_noncontact (parent : Fin S.count)
    (retained : normal.forkApproachNodes boundary pivot forest parent = true)
    (absent : normal.forkAbsorptionTargets pivot forest parent = false) :
    normal.forkAbsorptionSuccessor boundary pivot forest parent = w.conditionalBoundarySuccessor parent := by
  have parts := Bool.or_eq_false_iff.mp absent
  simp only [forkAbsorptionSuccessor, parts.1, parts.2, retained, Bool.false_eq_true, if_false, if_true]

/-- Every noncontact observed column has exactly the forest form: its own
row XOR the unique actual successor row.  Original path and activation reads
were proved absent, and global well-formedness removes the interpreter's
declared-edge guard only for a genuinely returned successor. -/
theorem forkAbsorbedInteraction_noncontact_coefficient (parent child : Fin S.count)
    (absent : normal.forkAbsorptionTargets pivot forest parent = false) :
    (normal.forkAbsorbedInteractionSignal boundary pivot forest).observedRowCoefficient child parent =
      Bool.xor (decide (child = parent))
        (decide (normal.forkAbsorptionSuccessor boundary pivot forest parent = some child)) := by
  have original := normal.activationInteraction_noncontact_parent pivot forest parent child absent
  have mask : (normal.forkAbsorbedInteractionSignal boundary pivot forest).parentMask child parent =
      decide (normal.forkAbsorptionSuccessor boundary pivot forest parent = some child) := by
    simp only [forkAbsorbedInteractionSignal, LinearSignal.absorbSuccessor, original, Bool.false_xor, ite_self]
  rw [LinearSignal.observedRowCoefficient, mask]
  by_cases edge : normal.forkAbsorptionSuccessor boundary pivot forest parent = some child
  · have declared := (childWellFormed_edge (normal.forkAbsorbedInteractionRows boundary pivot forest)
      (normal.forkAbsorptionSuccessor boundary pivot forest)
      (normal.forkAbsorptionSuccessor_wellFormed boundary pivot forest) edge).2.2
    rw [declared, Bool.true_and]
  · rw [decide_eq_false edge, Bool.and_false]

/-- At an actual returned edge, that column is exactly the two displayed
row incidences.  No other installed row reads this noncontact coordinate. -/
theorem forkAbsorbedInteraction_noncontact_column_pair {parent child : Fin S.count}
    (absent : normal.forkAbsorptionTargets pivot forest parent = false)
    (edge : normal.forkAbsorptionSuccessor boundary pivot forest parent = some child) (row : Fin S.count) :
    (normal.forkAbsorbedInteractionSignal boundary pivot forest).observedRowCoefficient row parent =
      Bool.xor (decide (row = parent)) (decide (row = child)) := by
  rw [normal.forkAbsorbedInteraction_noncontact_coefficient boundary pivot forest parent row absent, edge]
  simp only [Option.some.injEq, eq_comm]

/-- The actual full-cube observed basis direction has those same two row
values.  This bridges sparse graph columns to the real homogeneous signal,
retaining the literal original reserved-prefix coordinate offset. -/
theorem forkAbsorbedInteraction_noncontact_basis_pair {parent child : Fin S.count}
    (absent : normal.forkAbsorptionTargets pivot forest parent = false)
    (edge : normal.forkAbsorptionSuccessor boundary pivot forest parent = some child) (row : Fin S.count) :
    ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase row).value
      (basisAssignment (pairRootCount graph.binary + S.count) (Fin.natAdd (pairRootCount graph.binary) parent)) =
      Bool.xor (decide (row = parent)) (decide (row = child)) := by
  rw [LinearSignal.rowPhase_observed_basis]
  exact normal.forkAbsorbedInteraction_noncontact_column_pair boundary pivot forest absent edge row

/-! ## Retain the literal complete first-contact list and its proper freedom -/

/-- The full original first-contact list from this Small source.  Its
stopped map is used to certify the old endpoint; the new policy may resume
a fork endpoint, so it is deliberately not given a false new-stop field. -/
def forkApproachPath (source : Fin S.count) (inside : w.small source = true) :
    SuccessorPath w.smallOutcomeFlowNodes (w.smallInteractionStopSuccessor (normal.forkAbsorptionTargets pivot forest)) source :=
  boundary.interactionStopPath (normal.forkAbsorptionTargets pivot forest)
    (normal.receives_condition pivot forest) source inside

/-- A proved target-mask identity transports only the actual path data.
This permits lightweight clients to use a known normal window without
reducing its exhaustive normalization search or rewriting dependent route
certificates through a computed mask. -/
theorem forkApproachPath_nodes_of_targets_eq (targets : NodeSet S)
    (receives : NodeSet.Subset query.condition targets)
    (same : normal.forkAbsorptionTargets pivot forest = targets)
    (source : Fin S.count) (inside : w.small source = true) :
    (normal.forkApproachPath boundary pivot forest source inside).nodes =
      (boundary.interactionStopPath targets receives source inside).nodes := by
  cases same
  rfl

/-- Target-mask transport retains the literal receiving endpoint too. -/
theorem forkApproachPath_endpoint_of_targets_eq (targets : NodeSet S)
    (receives : NodeSet.Subset query.condition targets)
    (same : normal.forkAbsorptionTargets pivot forest = targets)
    (source : Fin S.count) (inside : w.small source = true) :
    (normal.forkApproachPath boundary pivot forest source inside).endpoint =
      (boundary.interactionStopPath targets receives source inside).endpoint := by
  cases same
  rfl

/-- Every actual vertex of this complete approach is in the all-Small
prefix union, including its head, trace or fork receiving endpoint. -/
theorem forkApproachPath_retained (source : Fin S.count) (inside : w.small source = true)
    (parent : Fin S.count) (visited : parent ∈ (normal.forkApproachPath boundary pivot forest source inside).nodes) :
    normal.forkApproachNodes boundary pivot forest parent = true :=
  (boundary.absorbingNodes_eq_true_iff (normal.forkAbsorptionTargets pivot forest)
    (normal.receives_condition pivot forest) parent).mpr ⟨source, inside, visited⟩

/-- The receiving endpoint is an actual combined target.  It need not be
the eventual conditioner, nor need it already belong to Small or the core. -/
theorem forkApproachPath_endpoint_target (source : Fin S.count) (inside : w.small source = true) :
    normal.forkAbsorptionTargets pivot forest (normal.forkApproachPath boundary pivot forest source inside).endpoint = true :=
  boundary.interactionStopPath_endpoint_in_interaction (normal.forkAbsorptionTargets pivot forest)
    (normal.receives_condition pivot forest) source inside

/-- Every proper transmitting vertex precedes *both* kinds of contact. -/
theorem forkApproachPath_before_free (source : Fin S.count) (inside : w.small source = true)
    (parent : Fin S.count) (visited : parent ∈ (normal.forkApproachPath boundary pivot forest source inside).nodes)
    (different : parent ≠ (normal.forkApproachPath boundary pivot forest source inside).endpoint) :
    normal.forkAbsorptionTargets pivot forest parent = false :=
  boundary.interactionStopPath_before_free (normal.forkAbsorptionTargets pivot forest)
    (normal.receives_condition pivot forest) source inside parent visited different

/-- In particular no actual proper prefix reads a normalized-path fork.
This is stronger than omission from the selected head mask. -/
theorem forkApproachPath_before_off_path (source : Fin S.count) (inside : w.small source = true)
    (parent : Fin S.count) (visited : parent ∈ (normal.forkApproachPath boundary pivot forest source inside).nodes)
    (different : parent ≠ (normal.forkApproachPath boundary pivot forest source inside).endpoint) :
    .observed parent ∉ normal.cutPath.nodes :=
  normal.forkAbsorption_noncontact_off_path pivot forest parent
    (normal.forkApproachPath_before_free boundary pivot forest source inside parent visited different)

/-- The proper prefix avoids the complete original action and condition.
Action freedom is inherited from the real original flow domain; conditioners
are combined stopping targets and therefore cannot be proper vertices. -/
theorem forkApproachPath_before_fixed_free (source : Fin S.count) (inside : w.small source = true)
    (parent : Fin S.count) (visited : parent ∈ (normal.forkApproachPath boundary pivot forest source inside).nodes)
    (different : parent ≠ (normal.forkApproachPath boundary pivot forest source inside).endpoint) :
    NodeSet.union query.action query.condition parent = false := by
  have action := outcomeFlow_avoids_action w parent
    ((normal.forkApproachPath boundary pivot forest source inside).inside parent visited)
  have absent := normal.forkApproachPath_before_free boundary pivot forest source inside parent visited different
  have condition : query.condition parent = false := by
    apply Bool.eq_false_iff.mpr
    intro selected
    exact Bool.false_ne_true (absent.symm.trans (normal.receives_condition pivot forest parent selected))
  exact Bool.or_eq_false_iff.mpr ⟨action, condition⟩

/-- The chosen original outcome is on the actual normalized path, so it
cannot be a proper vertex of this first combined-contact approach. -/
theorem forkApproachPath_before_outcome_free (source : Fin S.count) (inside : w.small source = true)
    (parent : Fin S.count) (visited : parent ∈ (normal.forkApproachPath boundary pivot forest source inside).nodes)
    (different : parent ≠ (normal.forkApproachPath boundary pivot forest source inside).endpoint) :
    NodeSet.singleton normal.outcome parent = false := by
  apply Bool.eq_false_iff.mpr
  intro selected
  have same := (NodeSet.singleton_eq_true_iff _ _).mp selected
  apply normal.forkApproachPath_before_off_path boundary pivot forest source inside parent visited different
  rw [same]
  exact List.mem_of_getLast? normal.cutPath.finishes

/-- New and old policies agree at every actually flipped proper vertex.
The endpoint is intentionally excluded: a fork endpoint has a new real exit. -/
theorem forkApproachPath_prefix_successors (source : Fin S.count) (inside : w.small source = true)
    (parent : Fin S.count)
    (flipped : (normal.forkApproachPath boundary pivot forest source inside).prefixBits parent = true) :
    normal.forkAbsorptionSuccessor boundary pivot forest parent =
      w.smallInteractionStopSuccessor (normal.forkAbsorptionTargets pivot forest) parent := by
  have parts := ((normal.forkApproachPath boundary pivot forest source inside).prefixBits_eq_true_iff parent).mp flipped
  have absent := normal.forkApproachPath_before_free boundary pivot forest source inside parent parts.1 parts.2
  rw [normal.forkAbsorptionSuccessor_noncontact boundary pivot forest parent
    (normal.forkApproachPath_retained boundary pivot forest source inside parent parts.1) absent]
  simp only [HedgeWitness.smallInteractionStopSuccessor, absent, Bool.false_eq_true, if_false]

/-! ## The real installed prefix direction has exactly two boundary rows -/

/-- The actual proper-prefix cube uses no new shared coordinate and flips
no receiving endpoint.  It is data from the complete first-contact list. -/
def forkApproachPrefixDirection (source : Fin S.count) (inside : w.small source = true) : Cube graph :=
  LinearSignal.successorPrefixDirection (normal.forkApproachPath boundary pivot forest source inside)

/-- Support is on the unchanged full action/condition cylinder. -/
theorem forkApproachPrefixDirection_supported (source : Fin S.count) (inside : w.small source = true) :
    normal.forkApproachPrefixDirection boundary pivot forest source inside ∈
      FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count)
        (cubeMask graph (NodeSet.union query.action query.condition)) :=
  LinearSignal.successorPrefixDirection_member _ _
    (normal.forkApproachPath_before_fixed_free boundary pivot forest source inside)

/-- The actual selected outcome character is unchanged by this correction. -/
theorem forkApproachPrefixDirection_outcome_even (source : Fin S.count) (inside : w.small source = true) :
    (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value
      (normal.forkApproachPrefixDirection boundary pivot forest source inside) = false :=
  LinearSignal.successorPrefixDirection_mask_zero _ _
    (normal.forkApproachPath_before_outcome_free boundary pivot forest source inside)

/-- Every receiving core coordinate is zero in the literal proper-prefix
direction.  It cannot be a flipped proper vertex because it is a target. -/
theorem forkApproachPrefixDirection_core_zero (source : Fin S.count) (inside : w.small source = true)
    (child : Fin S.count) (core : normal.smallInteractionRows pivot forest child = true) :
    cubeSample graph (normal.forkApproachPrefixDirection boundary pivot forest source inside) child = false := by
  rw [forkApproachPrefixDirection, LinearSignal.successorPrefixDirection_sample]
  apply Bool.eq_false_iff.mpr
  intro flipped
  have parts := ((normal.forkApproachPath boundary pivot forest source inside).prefixBits_eq_true_iff child).mp flipped
  have absent := normal.forkApproachPath_before_free boundary pivot forest source inside child parts.1 parts.2
  exact Bool.false_ne_true (absent.symm.trans (NodeSet.subset_union_left _ _ child core))

/-- The original fused receiving mechanism has *proved* zero value on
every such actual prefix.  Its own bit is zero, no flipped observed vertex
is an old path/trace parent, and all original reserved bits are zero in the
correction.  This does not assert zero on arbitrary first-core-only prefixes. -/
theorem activationInteraction_forkApproach_read_zero (source : Fin S.count) (inside : w.small source = true)
    (child : Fin S.count) (core : normal.smallInteractionRows pivot forest child = true) :
    ((normal.activationInteractionSignal pivot forest).rowPhase child).value
      (normal.forkApproachPrefixDirection boundary pivot forest source inside) = false := by
  let point := normal.forkApproachPrefixDirection boundary pivot forest source inside
  have roots : cubeEnvironment graph point = (fun _ => false) := LinearSignal.successorPrefixDirection_environment _
  have parentsZero : (List.finRange S.count).foldl (fun total parent => Bool.xor total
      (if S.directed parent child = true then
        if (normal.activationInteractionSignal pivot forest).parentMask child parent then cubeSample graph point parent else false
      else false)) false = false := by
    apply foldl_unchanged
    intro total parent
    cases flipped : cubeSample graph point parent with
    | false => simp only [ite_self, Bool.xor_false]
    | true =>
        have actual : (normal.forkApproachPath boundary pivot forest source inside).prefixBits parent = true := by
          simpa only [point, forkApproachPrefixDirection, LinearSignal.successorPrefixDirection_sample] using flipped
        have parts := ((normal.forkApproachPath boundary pivot forest source inside).prefixBits_eq_true_iff parent).mp actual
        have absent := normal.forkApproachPath_before_free boundary pivot forest source inside parent parts.1 parts.2
        have unread := normal.activationInteraction_noncontact_parent pivot forest parent child absent
        simp only [unread, Bool.false_eq_true, if_false, ite_self, Bool.xor_false]
  have rootsZero : (List.finRange (pairRootCount graph.binary)).foldl (fun total root => Bool.xor total
      (if pairRootIncident graph.binary root child = true then
        if (normal.activationInteractionSignal pivot forest).rootMask child root then cubeEnvironment graph point root else false
      else false)) false = false := by
    apply foldl_unchanged
    intro total root
    simp only [roots, ite_self, Bool.xor_false]
  rw [LinearSignal.rowPhase_value,
    normal.forkApproachPrefixDirection_core_zero boundary pivot forest source inside child core,
    parentsZero, rootsZero]
  rfl

/-- A fork endpoint's new outgoing exit does not change the correction:
the old and new maps agree at every true proper-prefix bit. -/
theorem forkApproachPrefixDirection_forest_rows (source : Fin S.count) (inside : w.small source = true) (child : Fin S.count) :
    ((LinearSignal.ofSuccessor (G := graph) (normal.forkAbsorptionSuccessor boundary pivot forest)).rowPhase child).value
      (normal.forkApproachPrefixDirection boundary pivot forest source inside) =
      Bool.xor (decide (child = source))
        (decide (child = (normal.forkApproachPath boundary pivot forest source inside).endpoint)) :=
  LinearSignal.successorPrefixDirection_rowPhase_of_agrees_on_prefix _ _ _
    (normal.forkAbsorptionSuccessor_wellFormed boundary pivot forest)
    (normal.forkApproachPath_prefix_successors boundary pivot forest source inside) child

/-- Every actual installed row has precisely the two receiving-boundary
correction.  At core rows the original residual was proved zero; elsewhere
the installation is the real forest row.  This covers all observed rows,
not just a selected head or one mandatory source. -/
theorem forkApproachPrefixDirection_rows (source : Fin S.count) (inside : w.small source = true) (child : Fin S.count) :
    ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase child).value
      (normal.forkApproachPrefixDirection boundary pivot forest source inside) =
      Bool.xor (decide (child = source))
        (decide (child = (normal.forkApproachPath boundary pivot forest source inside).endpoint)) := by
  unfold forkAbsorbedInteractionSignal
  cases core : normal.smallInteractionRows pivot forest child with
  | false =>
      rw [LinearSignal.absorbSuccessor_rowPhase_outside _ _ _ child core]
      exact normal.forkApproachPrefixDirection_forest_rows boundary pivot forest source inside child
  | true =>
      rw [LinearSignal.absorbSuccessor_rowPhase_inside _ _ _ child core,
        normal.activationInteraction_forkApproach_read_zero boundary pivot forest source inside child core,
        normal.forkApproachPrefixDirection_forest_rows boundary pivot forest source inside child,
        normal.forkApproachPrefixDirection_core_zero boundary pivot forest source inside child core,
        Bool.xor_false, Bool.false_xor]

/-! ## Transfer on the original cylinder without changing the outcome -/

/-- Apply the literal first-contact proper prefix on the original cube.
The receiving contact and all original independent root coordinates remain
unchanged, even when the new map resumes a fork contact. -/
def forkApproachShift (source : Fin S.count) (inside : w.small source = true) (point : Cube graph) : Cube graph :=
  LinearSignal.shiftBySuccessorPrefix (normal.forkApproachPath boundary pivot forest source inside) point

/-- The actual installed row changes only at the Small source and its
receiving contact.  Equal endpoints cancel for a zero-edge approach. -/
theorem forkApproachShift_rowPhase (source : Fin S.count) (inside : w.small source = true) (point : Cube graph) (child : Fin S.count) :
    ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase child).value
      (normal.forkApproachShift boundary pivot forest source inside point) =
      Bool.xor (((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase child).value point)
        (Bool.xor (decide (child = source))
          (decide (child = (normal.forkApproachPath boundary pivot forest source inside).endpoint))) := by
  rw [forkApproachShift, LinearSignal.shiftBySuccessorPrefix_rowPhase]
  exact congrArg (Bool.xor _) (normal.forkApproachPrefixDirection_rows boundary pivot forest source inside child)

/-- On every outside-Small row only the receiving contact can change.
The actual source is in the original mandatory Small set, not a guessed
odd pivot; this is the precise transfer operation needed by the global proof. -/
theorem forkApproachShift_outside_small (source : Fin S.count) (inside : w.small source = true)
    (point : Cube graph) (child : Fin S.count) (outside : w.small child = false) :
    ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase child).value
      (normal.forkApproachShift boundary pivot forest source inside point) =
      Bool.xor (((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase child).value point)
        (decide (child = (normal.forkApproachPath boundary pivot forest source inside).endpoint)) := by
  have different : child ≠ source := by
    intro same
    exact Bool.false_ne_true (outside.symm.trans (same ▸ inside))
  rw [normal.forkApproachShift_rowPhase boundary pivot forest source inside point child,
    decide_eq_false different, Bool.false_xor]

/-- XOR with this proved-supported prefix preserves the full original
action/condition cylinder for any already supported point. -/
theorem forkApproachShift_supported (source : Fin S.count) (inside : w.small source = true) (point : Cube graph)
    (supported : point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count)
      (cubeMask graph (NodeSet.union query.action query.condition))) :
    normal.forkApproachShift boundary pivot forest source inside point ∈
      FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count)
        (cubeMask graph (NodeSet.union query.action query.condition)) :=
  LinearSignal.shiftBySuccessorPrefix_member _ _
    (normal.forkApproachPath_before_fixed_free boundary pivot forest source inside) point supported

/-- The original outcome character is retained at every shifted point,
not merely after an oddness hypothesis is supplied. -/
theorem forkApproachShift_outcome (source : Fin S.count) (inside : w.small source = true) (point : Cube graph) :
    (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value
      (normal.forkApproachShift boundary pivot forest source inside point) =
      (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value point :=
  LinearSignal.shiftBySuccessorPrefix_maskPhase _ _
    (normal.forkApproachPath_before_outcome_free boundary pivot forest source inside) point

/-- All original reserved inputs are retained literally by the shift.
No shared switching input or additional pair-root coordinate is introduced. -/
theorem forkApproachShift_roots (source : Fin S.count) (inside : w.small source = true) (point : Cube graph) :
    cubeEnvironment graph (normal.forkApproachShift boundary pivot forest source inside point) = cubeEnvironment graph point := by
  funext root
  change Bool.xor (cubeEnvironment graph point root)
    (cubeEnvironment graph (LinearSignal.successorPrefixDirection
      (normal.forkApproachPath boundary pivot forest source inside)) root) = _
  rw [LinearSignal.successorPrefixDirection_environment, Bool.xor_false]

end ConditionalBackdoorPathNormalForm

end Causality
end Thesis
