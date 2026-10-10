import Thesis.CausalTransport.ActivePathHeadInputs
import Thesis.CausalTransport.ConditionalFailureCoreIncidence

namespace Thesis
namespace Causality

open PathSpecification Probability FiniteBooleanInteraction
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S} {query : ConditionalKernelQuery S}

/-!
# Actual chain-head columns and the incoming outcome endpoint

The completed all-Small installation already has proved columns for proper
approaches, retained forks, activation traces, and original pair roots.  Here
ordinary noncollider path heads retain their actual original columns through
both absorption layers.  The real trace/path intersection excludes activation
transmission at such a head, and the later mandatory-source map stops at that
completed core row.  Neither layer can add an arbitrary outgoing continuation.

The graph-only `ActivePathHeadInputs` theorem derives exactly one observed
outgoing receiver for every internal noncollider head.  Its original column,
including all zero entries, therefore becomes the installed own-row/receiver
pair.  Both rows are actual heads and remain in the full selected union.
The coordinate is free on the original evidence cylinder, proved using the
actual supported path direction and not an independently supplied freedom flag.

An incoming outcome endpoint is different: it has no outgoing path-parent
read, and its installed observed basis has just its own selected row incidence.
Its outcome coordinate remains supported.  A global incidence route must
account separately for the omitted outgoing outcome endpoint: the actual
boundary routes cannot retain that outcome as a new row, and its one original
outgoing receiver remains a selected head.  Both orientations therefore give
exactly one selected-row incidence, at a genuine retained row.  The unified
endpoint theorem supplies this starting column without an orientation flag.

These are derived local columns for arbitrary retained pivots and complete
all-Small boundaries.  They do not yet prove global outcome-to-Small
connectivity, its supported successful direction, or universal conditional
terminal countermodels.  No path window or receiving row is assumed as a
new terminal-readiness field, and no witness is chosen from Prop to make data.
-/

namespace ConditionalBackdoorPathNormalForm

variable {w : HedgeWitness graph query.jointNumerator}
    (boundary : ConditionedSmallFlowBoundary w) (pivot : RetainedConditionalPivot query)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (forest : ConditionalCutColliderActivationForest query pivot.node)

private theorem head_in_core (parent : Fin S.count) (head : normal.pathHeads parent = true) :
    normal.smallInteractionRows pivot forest parent = true :=
  NodeSet.subset_union_left _ _ parent (NodeSet.subset_union_left _ _ parent head)

/-! ## Neither absorption changes a noncollider head's original column -/

/-- An actual noncollider path head is outside the whole real trace union.
This is proved from actual membership and the trace/path collider classifier,
not from disjointness of auxiliary activation domains. -/
theorem pathHead_noncollider_trace_free (parent : Fin S.count)
    (head : normal.pathHeads parent = true) (noncollider : normal.colliderSeeds parent = false) :
    normal.activationTraceNodes pivot forest parent = false := by
  apply Bool.eq_false_iff.mpr
  intro selected
  have onPath := ActivePathInput.headRows_member head
  have collider := (normal.activationTraceNodes_intersection_iff_collider pivot forest parent onPath).mp selected
  exact Bool.false_ne_true (noncollider.symm.trans collider)

/-- Activation fusion preserves this complete original parent column.
An original true read always has a selected receiving path head, so the
unselected-head branch cannot conceal a discarded nonzero entry. -/
theorem activationInteraction_head_parent_mask (parent row : Fin S.count)
    (head : normal.pathHeads parent = true) (noncollider : normal.colliderSeeds parent = false) :
    (normal.activationInteractionSignal pivot forest).parentMask row parent =
      ActivePathInput.incomingEdge graph
        (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes (.observed parent) row := by
  have stopped : normal.activationTraceSuccessor pivot forest parent = none :=
    restrictChild_of_false (normal.pathHead_noncollider_trace_free pivot forest parent head noncollider)
  cases receiver : normal.pathHeads row with
  | true =>
      simp only [activationInteractionSignal, LinearSignal.absorbSuccessor, receiver, if_true,
        LinearSignal.ofActivePath, stopped, reduceCtorEq, decide_false, Bool.xor_false]
  | false =>
      have absent : ActivePathInput.incomingEdge graph
          (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes (.observed parent) row = false := by
        apply Bool.eq_false_iff.mpr
        intro read
        exact Bool.false_ne_true (receiver.symm.trans (ActivePathInput.incomingEdge_head read))
      simp only [activationInteractionSignal, LinearSignal.absorbSuccessor, receiver, Bool.false_eq_true,
        if_false, stopped, reduceCtorEq, decide_false, absent]

/-- The mandatory-source policy is stopped at the actual head coordinate,
which is already core.  Full-column preservation also holds at all rows
outside the core, whose original entries must genuinely be zero. -/
theorem forkAbsorbedInteraction_head_parent_mask (parent row : Fin S.count)
    (head : normal.pathHeads parent = true) (noncollider : normal.colliderSeeds parent = false) :
    (normal.forkAbsorbedInteractionSignal boundary pivot forest).parentMask row parent =
      ActivePathInput.incomingEdge graph
        (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes (.observed parent) row := by
  have stopped := normal.forkAbsorptionSuccessor_stops_core boundary pivot forest parent (normal.head_in_core pivot forest parent head)
  have original := normal.activationInteraction_head_parent_mask pivot forest parent row head noncollider
  cases receiver : normal.smallInteractionRows pivot forest row with
  | true =>
      simp only [forkAbsorbedInteractionSignal, LinearSignal.absorbSuccessor, receiver, if_true,
        original, stopped, reduceCtorEq, decide_false, Bool.xor_false]
  | false =>
      have absent : ActivePathInput.incomingEdge graph
          (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes (.observed parent) row = false := by
        apply Bool.eq_false_iff.mpr
        intro read
        have present := normal.head_in_core pivot forest row (ActivePathInput.incomingEdge_head read)
        exact Bool.false_ne_true (receiver.symm.trans present)
      simp only [forkAbsorbedInteractionSignal, LinearSignal.absorbSuccessor, receiver, Bool.false_eq_true,
        if_false, stopped, reduceCtorEq, decide_false, absent]

/-- The interpreter's actual declared-parent coefficient retains one
own bit and the original consecutive input.  The directed-edge guard is
eliminated only using the original path arrow's availability theorem. -/
theorem forkAbsorbedInteraction_head_coefficient (parent row : Fin S.count)
    (head : normal.pathHeads parent = true) (noncollider : normal.colliderSeeds parent = false) :
    (normal.forkAbsorbedInteractionSignal boundary pivot forest).observedRowCoefficient row parent =
      Bool.xor (decide (row = parent))
        (ActivePathInput.incomingEdge graph
          (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes (.observed parent) row) := by
  rw [LinearSignal.observedRowCoefficient,
    normal.forkAbsorbedInteraction_head_parent_mask boundary pivot forest parent row head noncollider]
  cases read : ActivePathInput.incomingEdge graph
      (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes (.observed parent) row with
  | false => rw [Bool.and_false]
  | true =>
      have declared := LinearSignal.ofActivePath_parent_available normal.cutPath row parent read
      rw [declared, Bool.true_and]

/-! ## Actual chain columns are retained and supported -/

/-- Every actual non-source noncollider head has a true original path
direction coordinate.  Membership is derived from the head classifier, so
this cannot accidentally assert a positive off-path observed coordinate. -/
theorem pathHead_noncollider_direction_true (parent : Fin S.count)
    (head : normal.pathHeads parent = true) (noncollider : normal.colliderSeeds parent = false)
    (notSource : parent ≠ pivot.node) : cubeSample graph normal.pathDirection parent = true := by
  rw [pathDirection, LinearSignal.activePathDirection_sample]
  exact (ActivePathInput.nonColliderBits_eq_true_iff graph _ normal.cutPath.nodes pivot.node parent).mpr
    ⟨ActivePathInput.headRows_member head, notSource, noncollider⟩

/-- The complete original fixed mask excludes every such coordinate.
Its actual supported path bit would otherwise be both true and false.
This also covers a selected incoming outcome endpoint. -/
theorem pathHead_noncollider_fixed_free (parent : Fin S.count)
    (head : normal.pathHeads parent = true) (noncollider : normal.colliderSeeds parent = false)
    (notSource : parent ≠ pivot.node) : NodeSet.union query.action query.condition parent = false := by
  apply Bool.eq_false_iff.mpr
  intro fixed
  have zero := normal.pathDirection_fixed parent fixed
  have positive := normal.pathHead_noncollider_direction_true pivot parent head noncollider notSource
  exact Bool.false_ne_true (zero.symm.trans positive)

/-- The real observed basis is free on the whole original evidence
cylinder, with every original reserved root still present in the cube.
It is not support under a reduced exchange-test given set. -/
theorem pathHead_noncollider_basis_supported (parent : Fin S.count)
    (head : normal.pathHeads parent = true) (noncollider : normal.colliderSeeds parent = false)
    (notSource : parent ≠ pivot.node) :
    basisAssignment (pairRootCount graph.binary + S.count) (Fin.natAdd (pairRootCount graph.binary) parent) ∈
      FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count)
        (cubeMask graph (NodeSet.union query.action query.condition)) := by
  apply (basisAssignment_member_iff _ _ _).mpr
  change FiniteProduct.BooleanBlocks.rightBlock (pairRootCount graph.binary) S.count
    (cubeMask graph (NodeSet.union query.action query.condition)) parent = false
  rw [cubeMask, FiniteProduct.BooleanBlocks.rightBlock_join]
  exact normal.pathHead_noncollider_fixed_free pivot parent head noncollider notSource

/-- Every actual internal noncollider head has a distinct real receiving
head, and its full installed observed basis has exactly those two row values.
Its window, receiver, and original arrow are derived, not terminal premises. -/
theorem pathHead_internal_basis_pair (parent : Fin S.count)
    (head : normal.pathHeads parent = true) (noncollider : normal.colliderSeeds parent = false)
    (notSource : parent ≠ pivot.node) (notTarget : parent ≠ normal.outcome) :
    Exists fun child : Fin S.count => parent ≠ child ∧ normal.pathHeads child = true ∧
      normal.forkAbsorbedInteractionRows boundary pivot forest parent = true ∧
      normal.forkAbsorbedInteractionRows boundary pivot forest child = true ∧
      forall row, ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase row).value
        (basisAssignment (pairRootCount graph.binary + S.count) (Fin.natAdd (pairRootCount graph.binary) parent)) =
        Bool.xor (decide (row = parent)) (decide (row = child)) := by
  rcases ActivePathInput.head_unique_input_of_internal normal.cutPath parent head noncollider notSource notTarget with ⟨child, column⟩
  have input := column child
  rw [decide_eq_true rfl] at input
  have declared := LinearSignal.ofActivePath_parent_available normal.cutPath child parent input
  have childHead := ActivePathInput.incomingEdge_head input
  have parentSelected : normal.forkAbsorbedInteractionRows boundary pivot forest parent = true :=
    NodeSet.subset_union_left _ _ _ (normal.head_in_core pivot forest parent head)
  have childSelected : normal.forkAbsorbedInteractionRows boundary pivot forest child = true :=
    NodeSet.subset_union_left _ _ _ (normal.head_in_core pivot forest child childHead)
  refine ⟨child, ?_, childHead, parentSelected, childSelected, ?_⟩
  · intro same
    exact Nat.ne_of_lt (S.directed_earlier declared) (congrArg Fin.val same)
  · intro row
    rw [LinearSignal.rowPhase_observed_basis,
      normal.forkAbsorbedInteraction_head_coefficient boundary pivot forest parent row head noncollider, column row]

/-! ## An incoming outcome endpoint has one row incidence, not two -/

/-- At a selected incoming outcome endpoint, there is no original
outgoing path read and no trace transmission.  Its actual full-cube observed
basis is therefore precisely its own row indicator at every installed row. -/
theorem pathHead_outcome_basis_single (head : normal.pathHeads normal.outcome = true) (row : Fin S.count) :
    ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase row).value
      (basisAssignment (pairRootCount graph.binary + S.count) (Fin.natAdd (pairRootCount graph.binary) normal.outcome)) =
      decide (row = normal.outcome) := by
  have noncollider : normal.colliderSeeds normal.outcome = false := ActivePathInput.colliderRows_target_false normal.cutPath
  rw [LinearSignal.rowPhase_observed_basis,
    normal.forkAbsorbedInteraction_head_coefficient boundary pivot forest normal.outcome row head noncollider,
    ActivePathInput.target_head_parent_absent normal.cutPath head row, Bool.xor_false]

/-- The singleton incoming-outcome basis is supported on the original
query.  Endpoint distinction follows from the real outcome/condition
disjointness, not from a new endpoint-readiness assumption. -/
theorem pathHead_outcome_basis_supported (head : normal.pathHeads normal.outcome = true) :
    basisAssignment (pairRootCount graph.binary + S.count) (Fin.natAdd (pairRootCount graph.binary) normal.outcome) ∈
      FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count)
        (cubeMask graph (NodeSet.union query.action query.condition)) := by
  apply normal.pathHead_noncollider_basis_supported pivot normal.outcome head (ActivePathInput.colliderRows_target_false normal.cutPath)
  intro same
  have free := query.outcome_condition_disjoint normal.outcome normal.outcome_selected
  rw [same, pivot.selected] at free
  cases free

/-! ## Either outcome orientation supplies one actual selected-row incidence -/

/-- No complete all-Small first-contact prefix can retain this queried
outcome.  Whole-route stopping and the actual conditioned hard boundary
proved avoidance of every original outcome, not just the chosen endpoint. -/
theorem pathOutcome_approach_free : normal.forkApproachNodes boundary pivot forest normal.outcome = false := by
  apply Bool.eq_false_iff.mpr
  intro retained
  have absent := normal.forkApproachNodes_outcome_free boundary pivot forest normal.outcome retained
  exact Bool.false_ne_true (absent.symm.trans normal.outcome_selected)

/-- If the outgoing outcome endpoint is not a path head, it is absent
from the complete installed-row union.  It is neither an auxiliary trace
row nor an unvisited conditioner, and it cannot be a retained Small prefix. -/
theorem pathOutcome_nonhead_rows_free (head : normal.pathHeads normal.outcome = false) :
    normal.forkAbsorbedInteractionRows boundary pivot forest normal.outcome = false := by
  have fork : normal.cutPath.forkNodes normal.outcome = true :=
    (normal.cutPath.forkNodes_eq_true_iff normal.outcome).mpr ⟨List.mem_of_getLast? normal.cutPath.finishes, head⟩
  rw [forkAbsorbedInteractionRows, NodeSet.union, normal.forkNodes_core_free pivot forest normal.outcome fork,
    normal.pathOutcome_approach_free boundary pivot forest]
  rfl

/-- The original outgoing outcome input survives both absorptions.  Its
own unselected row does not transmit a new continuation: actual all-Small
outcome avoidance proves that the mandatory-source policy is absent there. -/
theorem forkAbsorbedInteraction_outgoing_outcome_parent_mask (head : normal.pathHeads normal.outcome = false)
    (row : Fin S.count) :
    (normal.forkAbsorbedInteractionSignal boundary pivot forest).parentMask row normal.outcome =
      ActivePathInput.incomingEdge graph
        (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes (.observed normal.outcome) row := by
  have fork : normal.cutPath.forkNodes normal.outcome = true :=
    (normal.cutPath.forkNodes_eq_true_iff normal.outcome).mpr ⟨List.mem_of_getLast? normal.cutPath.finishes, head⟩
  have free := normal.forkNodes_core_free pivot forest normal.outcome fork
  have stopped : normal.forkAbsorptionSuccessor boundary pivot forest normal.outcome = none := by
    simp only [forkAbsorptionSuccessor, free, normal.pathOutcome_approach_free boundary pivot forest,
      Bool.false_eq_true, if_false]
  have original := normal.activationInteraction_fork_parent_mask pivot forest normal.outcome row fork
  cases receiver : normal.smallInteractionRows pivot forest row with
  | true =>
      simp only [forkAbsorbedInteractionSignal, LinearSignal.absorbSuccessor, receiver, if_true,
        original, stopped, reduceCtorEq, decide_false, Bool.xor_false]
  | false =>
      have absent : ActivePathInput.incomingEdge graph
          (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes (.observed normal.outcome) row = false := by
        apply Bool.eq_false_iff.mpr
        intro read
        have present := normal.head_in_core pivot forest row (ActivePathInput.incomingEdge_head read)
        exact Bool.false_ne_true (receiver.symm.trans present)
      simp only [forkAbsorbedInteractionSignal, LinearSignal.absorbSuccessor, receiver, Bool.false_eq_true,
        if_false, stopped, reduceCtorEq, decide_false, absent]

/-- Every outcome orientation supplies exactly one selected-row basis
incidence at a genuinely retained head.  Incoming endpoints use their own
row; omitted outgoing endpoints use their derived unique receiving head.
The selected-row guard is essential: an omitted endpoint has no own row.
This is the actual original outcome coordinate, not an added switching bit. -/
theorem pathOutcome_selected_basis_single :
    Exists fun receiver : Fin S.count => normal.pathHeads receiver = true ∧
      normal.forkAbsorbedInteractionRows boundary pivot forest receiver = true ∧
      forall row, (if normal.forkAbsorbedInteractionRows boundary pivot forest row then
        ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase row).value
          (basisAssignment (pairRootCount graph.binary + S.count) (Fin.natAdd (pairRootCount graph.binary) normal.outcome))
        else false) = decide (row = receiver) := by
  cases head : normal.pathHeads normal.outcome with
  | true =>
      have selected : normal.forkAbsorbedInteractionRows boundary pivot forest normal.outcome = true :=
        NodeSet.subset_union_left _ _ _ (normal.head_in_core pivot forest normal.outcome head)
      refine ⟨normal.outcome, head, selected, ?_⟩
      intro row
      rw [normal.pathHead_outcome_basis_single boundary pivot forest head row]
      by_cases same : row = normal.outcome
      · subst row
        simp only [selected, if_true]
      · rw [decide_eq_false same]
        exact ite_self false
  | false =>
      have distinct : pivot.node ≠ normal.outcome := by
        intro same
        have free := query.outcome_condition_disjoint normal.outcome normal.outcome_selected
        rw [← same, pivot.selected] at free
        cases free
      rcases ActivePathInput.target_nonhead_unique_input normal.cutPath distinct head with ⟨receiver, column⟩
      have input := column receiver
      rw [decide_eq_true rfl] at input
      have receiverHead := ActivePathInput.incomingEdge_head input
      have selected : normal.forkAbsorbedInteractionRows boundary pivot forest receiver = true :=
        NodeSet.subset_union_left _ _ _ (normal.head_in_core pivot forest receiver receiverHead)
      have different : normal.outcome ≠ receiver := by
        intro same
        have ordered := S.directed_earlier (LinearSignal.ofActivePath_parent_available normal.cutPath receiver normal.outcome input)
        exact Nat.ne_of_lt ordered (congrArg Fin.val same)
      have coefficient (row : Fin S.count) :
          ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase row).value
            (basisAssignment (pairRootCount graph.binary + S.count) (Fin.natAdd (pairRootCount graph.binary) normal.outcome)) =
          Bool.xor (decide (row = normal.outcome)) (decide (row = receiver)) := by
        rw [LinearSignal.rowPhase_observed_basis, LinearSignal.observedRowCoefficient,
          normal.forkAbsorbedInteraction_outgoing_outcome_parent_mask boundary pivot forest head row]
        cases read : ActivePathInput.incomingEdge graph
            (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes (.observed normal.outcome) row with
        | false =>
            rw [Bool.and_false]
            have zero : decide (row = receiver) = false := (column row).symm.trans read
            rw [zero]
        | true =>
            have declared := LinearSignal.ofActivePath_parent_available normal.cutPath row normal.outcome read
            rw [declared, Bool.true_and]
            exact congrArg (Bool.xor (decide (row = normal.outcome))) (read.symm.trans (column row))
      refine ⟨receiver, receiverHead, selected, ?_⟩
      intro row
      rw [coefficient row]
      by_cases atOutcome : row = normal.outcome
      · subst row
        simp only [normal.pathOutcome_nonhead_rows_free boundary pivot forest head, Bool.false_eq_true, if_false,
          decide_eq_false different]
      · rw [decide_eq_false atOutcome, Bool.false_xor]
        by_cases atReceiver : row = receiver
        · subst row
          simp only [selected, if_true]
        · rw [decide_eq_false atReceiver]
          exact ite_self false

/-- The original queried outcome basis is supported in either endpoint
orientation.  Actual full-query direction support proves its freedom;
neither an endpoint-head flag nor a reduced given set is required. -/
theorem pathOutcome_basis_supported :
    basisAssignment (pairRootCount graph.binary + S.count) (Fin.natAdd (pairRootCount graph.binary) normal.outcome) ∈
      FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count)
        (cubeMask graph (NodeSet.union query.action query.condition)) := by
  apply (basisAssignment_member_iff _ _ _).mpr
  change FiniteProduct.BooleanBlocks.rightBlock (pairRootCount graph.binary) S.count
    (cubeMask graph (NodeSet.union query.action query.condition)) normal.outcome = false
  rw [cubeMask, FiniteProduct.BooleanBlocks.rightBlock_join]
  apply Bool.eq_false_iff.mpr
  intro fixed
  have zero := normal.pathDirection_fixed normal.outcome fixed
  have positive := normal.pathDirection_outcome_bit pivot.selected
  exact Bool.false_ne_true (zero.symm.trans positive)

end ConditionalBackdoorPathNormalForm

end Causality
end Thesis
