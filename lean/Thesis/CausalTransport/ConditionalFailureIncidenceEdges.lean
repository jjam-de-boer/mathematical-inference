import Thesis.CausalTransport.ConditionalFailureIncidenceDirection

namespace Thesis
namespace Causality

open PathSpecification Probability FiniteBooleanInteraction
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S} {query : ConditionalKernelQuery S}

/-!
# Proved local columns are edges of the actual conditional incidence graph

The connection-to-countermodel constructor uses a finite relation which
checks support, outcome evenness and every actual selected row.  The local
path, fork, activation and approach theorems must therefore supply that real
relation, not just an independent picture of a two-entry column.

Here all five connecting families are recognized by the actual test.  Used
original roots keep their genuine two children; internal noncollider heads
keep their own/receiving-head pair; trace transmitters keep their own/shared
successor pair; internal forks have the retained or unretained guarded pair;
and proper mandatory approaches keep their own/actual-successor pair.

The free-coordinate and outcome-even guards are proved from the original
query and actual path/trace/approach geometry.  The observed outcome endpoint
is deliberately excluded from correction columns: its singleton starting
incidence is handled by the separate direction constructor.  Conditioning
an original observed child never fixes that child's independent pair root.

The relation is symmetric because these are incidences, although each
underlying causal arrow is still its original directed arrow.  These are
graph-facing lemmas for arbitrary such actual local data, not new terminal
readiness flags and not yet a proof of global outcome-to-Small connectivity.
-/

namespace ConditionalBackdoorPathNormalForm

variable {w : HedgeWitness graph query.jointNumerator}
    (boundary : ConditionedSmallFlowBoundary w) (pivot : RetainedConditionalPivot query)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (forest : ConditionalCutColliderActivationForest query pivot.node)

/-- Actual two-row incidence is undirected.  This does not reverse a causal
arrow or modify the installation's guarded local input functions. -/
theorem forkPairIncidence_swap (left right : Fin S.count) :
    normal.forkPairIncidence boundary pivot forest left right =
      normal.forkPairIncidence boundary pivot forest right left :=
  LinearSignal.pairIncidence_swap _ _ _ _ left right

-- This wrapper retains literal observed-coordinate offsets.  Its premises
-- are proved by the local families below; the whole guarded column, not just
-- positive endpoint entries, is checked by the executable incidence test.
private theorem observed_column_edge (coordinate left right : Fin S.count)
    (leftSelected : normal.forkAbsorbedInteractionRows boundary pivot forest left = true)
    (rightSelected : normal.forkAbsorbedInteractionRows boundary pivot forest right = true)
    (different : left ≠ right)
    (free : NodeSet.union query.action query.condition coordinate = false)
    (notOutcome : coordinate ≠ normal.outcome)
    (column : forall row, (normal.forkAbsorbedInteractionSignal boundary pivot forest).selectedRowValue
      (normal.forkAbsorbedInteractionRows boundary pivot forest) row
      (basisAssignment _ (Fin.natAdd (pairRootCount graph.binary) coordinate)) =
        Bool.xor (decide (row = left)) (decide (row = right))) :
    normal.forkPairIncidence boundary pivot forest left right = true := by
  apply LinearSignal.pairIncidence_of_column _ _ _ _ left right
    (Fin.natAdd (pairRootCount graph.binary) coordinate) leftSelected rightSelected different
  · change FiniteProduct.BooleanBlocks.rightBlock _ _
      (cubeMask graph (NodeSet.union query.action query.condition)) coordinate = false
    rw [cubeMask, FiniteProduct.BooleanBlocks.rightBlock_join]
    exact free
  · change FiniteProduct.BooleanBlocks.rightBlock _ _
      (cubeMask graph (NodeSet.singleton normal.outcome)) coordinate = false
    rw [cubeMask, FiniteProduct.BooleanBlocks.rightBlock_join]
    apply Bool.eq_false_iff.mpr
    intro selected
    exact notOutcome ((NodeSet.singleton_eq_true_iff normal.outcome coordinate).mp selected)
  · exact column

/-! ## Original root, ordinary head and actual trace edges -/

/-- Every genuinely used original pair-root column passes the actual
complete row test.  Its two distinct children are selected heads, and the
unchanged environment coordinate is free and outcome-even even if a child
is an original conditioner. -/
theorem originalRoot_incidence_edge (root : Fin (pairRootCount graph.binary))
    (used : ActivePathInput.pairUsed graph normal.cutPath.nodes root = true) :
    normal.forkPairIncidence boundary pivot forest
      ((pairRoots graph.binary).get root).1 ((pairRoots graph.binary).get root).2 = true := by
  have core := normal.originalRoot_children_in_core pivot forest root used
  have leftSelected := NodeSet.subset_union_left _ (normal.forkApproachNodes boundary pivot forest) _ core.1
  have rightSelected := NodeSet.subset_union_left _ (normal.forkApproachNodes boundary pivot forest) _ core.2
  have different : ((pairRoots graph.binary).get root).1 ≠ ((pairRoots graph.binary).get root).2 := by
    intro same
    have ordered := (pairRoots_get_spec graph.binary root).1
    rw [same] at ordered
    exact Nat.lt_irrefl _ ordered
  apply LinearSignal.pairIncidence_of_column _ _ _ _ _ _ (root.castAdd S.count) leftSelected rightSelected different
  · change FiniteProduct.BooleanBlocks.leftBlock _ _
      (cubeMask graph (NodeSet.union query.action query.condition)) root = false
    rw [cubeMask, FiniteProduct.BooleanBlocks.leftBlock_join]
  · change FiniteProduct.BooleanBlocks.leftBlock _ _
      (cubeMask graph (NodeSet.singleton normal.outcome)) root = false
    rw [cubeMask, FiniteProduct.BooleanBlocks.leftBlock_join]
  · exact LinearSignal.selectedRowValue_pair_of_rows _ _ _ _ _ leftSelected rightSelected
      (normal.originalRoot_basis_pair boundary pivot forest root used)

/-- Every actual internal noncollider head has an actual incidence edge
to its unique receiving head.  The receiver, support and complete installed
column are all derived; no receiver is an additional terminal field. -/
theorem pathHead_internal_incidence_edge (parent : Fin S.count)
    (head : normal.pathHeads parent = true) (noncollider : normal.colliderSeeds parent = false)
    (notSource : parent ≠ pivot.node) (notOutcome : parent ≠ normal.outcome) :
    Exists fun child : Fin S.count => normal.pathHeads child = true ∧
      normal.forkPairIncidence boundary pivot forest parent child = true := by
  rcases normal.pathHead_internal_basis_pair boundary pivot forest parent head noncollider notSource notOutcome with
    ⟨child, different, childHead, parentSelected, childSelected, column⟩
  refine ⟨child, childHead, normal.observed_column_edge boundary pivot forest parent parent child
    parentSelected childSelected different
    (normal.pathHead_noncollider_fixed_free pivot parent head noncollider notSource) notOutcome ?_⟩
  exact LinearSignal.selectedRowValue_pair_of_rows _ _ _ _ _ parentSelected childSelected column

/-- A specified genuine outgoing input of a path head identifies its
actual incidence edge.  Outgoing adjacency itself excludes a collider and
both incoming endpoints, so a literal path walk supplies no separate
noncollider, internality or receiver-choice flags. -/
theorem pathHead_incidence_edge_of_input {parent child : Fin S.count}
    (head : normal.pathHeads parent = true)
    (input : ActivePathInput.incomingEdge graph
      (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node))
        normal.cutPath.nodes (.observed parent) child = true) :
    normal.forkPairIncidence boundary pivot forest parent child = true := by
  have noncollider := ActivePathInput.incoming_observed_parent_not_collider normal.cutPath parent child input
  have notSource : parent ≠ pivot.node := by
    intro same
    subst parent
    have absent := ActivePathInput.source_head_parent_absent normal.cutPath head child
    exact Bool.false_ne_true (absent.symm.trans input)
  have notOutcome : parent ≠ normal.outcome := by
    intro same
    subst parent
    have absent := ActivePathInput.target_head_parent_absent normal.cutPath head child
    exact Bool.false_ne_true (absent.symm.trans input)
  rcases ActivePathInput.head_unique_input_of_internal normal.cutPath parent head noncollider notSource notOutcome with
    ⟨receiver, column⟩
  have same : child = receiver := of_decide_eq_true ((column child).symm.trans input)
  subst receiver
  have childHead := ActivePathInput.incomingEdge_head input
  have parentSelected : normal.forkAbsorbedInteractionRows boundary pivot forest parent = true :=
    NodeSet.subset_union_left _ _ parent (NodeSet.subset_union_left _ _ parent (NodeSet.subset_union_left _ _ parent head))
  have childSelected : normal.forkAbsorbedInteractionRows boundary pivot forest child = true :=
    NodeSet.subset_union_left _ _ child (NodeSet.subset_union_left _ _ child (NodeSet.subset_union_left _ _ child childHead))
  have different : parent ≠ child := fun equal =>
    Nat.ne_of_lt (S.directed_earlier (LinearSignal.ofActivePath_parent_available normal.cutPath child parent input))
      (congrArg Fin.val equal)
  apply normal.observed_column_edge boundary pivot forest parent parent child parentSelected childSelected different
    (normal.pathHead_noncollider_fixed_free pivot parent head noncollider notSource) notOutcome
  apply LinearSignal.selectedRowValue_pair_of_rows _ _ _ _ _ parentSelected childSelected
  intro row
  rw [LinearSignal.rowPhase_observed_basis,
    normal.forkAbsorbedInteraction_head_coefficient boundary pivot forest parent row head noncollider, column row]

/-- No selected activation-trace coordinate is the original outcome.
Actual trace/path intersection would classify that endpoint as an internal
collider, contrary to the literal endpoint exclusion theorem. -/
theorem activationTrace_not_outcome (parent : Fin S.count)
    (selected : normal.activationTraceNodes pivot forest parent = true) : parent ≠ normal.outcome := by
  intro same
  subst parent
  have collider := (normal.activationTraceNodes_intersection_iff_collider pivot forest normal.outcome
    (List.mem_of_getLast? normal.cutPath.finishes)).mp selected
  have absent := ActivePathInput.colliderRows_target_false normal.cutPath
  change normal.colliderSeeds normal.outcome = false at absent
  exact Bool.false_ne_true (absent.symm.trans collider)

/-- A real transmitting trace supplies an edge of the actual graph.
The common successor may belong to merged branches or Small; neither
overlap creates a third incidence or removes the original fixed-set guard. -/
theorem activationTrace_incidence_edge {parent next : Fin S.count}
    (selected : normal.activationTraceNodes pivot forest parent = true)
    (edge : normal.activationTraceSuccessor pivot forest parent = some next) :
    normal.forkPairIncidence boundary pivot forest parent next = true := by
  have rows := normal.activationTrace_pair_rows_selected boundary pivot forest selected edge
  have declared := (childWellFormed_edge _ _ (normal.activationTraceSuccessor_wellFormed pivot forest) edge).2.2
  have different : parent ≠ next := fun same =>
    Nat.ne_of_lt (S.directed_earlier declared) (congrArg Fin.val same)
  apply normal.observed_column_edge boundary pivot forest parent parent next rows.1 rows.2 different
    (normal.activationTrace_transmitter_fixed_free pivot forest selected edge)
    (normal.activationTrace_not_outcome pivot forest parent selected)
  exact LinearSignal.selectedRowValue_pair_of_rows _ _ _ _ _ rows.1 rows.2
    (normal.activationTrace_basis_pair boundary pivot forest selected edge)

/-! ## Retained and unretained fork alternatives -/

/-- A retained fork's true own row and following head are joined by a
tested pair edge.  Whole actual boundary-route avoidance excludes the
original outcome, rather than asking for an independent orientation flag. -/
theorem retainedFork_incidence_edge (parent : Fin S.count)
    (fork : normal.cutPath.forkNodes parent = true)
    (retained : normal.forkApproachNodes boundary pivot forest parent = true) :
    Exists fun next : Fin S.count => normal.pathHeads next = true ∧
      normal.forkPairIncidence boundary pivot forest parent next = true := by
  rcases normal.retainedFork_selected_basis_pair boundary pivot forest parent fork retained with
    ⟨next, different, head, parentSelected, nextSelected, column⟩
  have notOutcome : parent ≠ normal.outcome := by
    intro same
    have free := normal.forkApproachNodes_outcome_free boundary pivot forest parent retained
    rw [same, normal.outcome_selected] at free
    cases free
  exact ⟨next, head, normal.observed_column_edge boundary pivot forest parent parent next
    parentSelected nextSelected different (normal.fork_basis_fixed_free pivot parent fork) notOutcome column⟩

/-- An unretained internal fork joins its two original receiving heads.
Its own raw bit is not a third incidence because that actual row is absent
from the installed selection, as proved before this guarded column test. -/
theorem unretainedFork_incidence_edge (parent : Fin S.count)
    (fork : normal.cutPath.forkNodes parent = true)
    (unretained : normal.forkApproachNodes boundary pivot forest parent = false)
    (notOutcome : parent ≠ normal.outcome) :
    Exists fun previous : Fin S.count => Exists fun next : Fin S.count =>
      normal.pathHeads previous = true ∧ normal.pathHeads next = true ∧
        normal.forkPairIncidence boundary pivot forest previous next = true := by
  rcases normal.unretainedFork_selected_basis_pair boundary pivot forest parent fork unretained notOutcome with
    ⟨previous, next, different, previousHead, nextHead, previousSelected, nextSelected, column⟩
  exact ⟨previous, next, previousHead, nextHead, normal.observed_column_edge boundary pivot forest parent previous next
    previousSelected nextSelected different (normal.fork_basis_fixed_free pivot parent fork) notOutcome column⟩

/-! ## Literal windows for normalized-head walks -/

-- An internal occurrence cannot be the endpoint.  The suffix's literal
-- last element is still the whole path's endpoint, and nodup excludes that
-- element from being its preceding internal middle.  No empty-list classical
-- equivalence or endpoint-choice argument is needed.
private theorem window_not_outcome (parent : Fin S.count) (previous next : SeparationNode S)
    (before after : List (SeparationNode S))
    (window : normal.cutPath.nodes = before ++ previous :: .observed parent :: next :: after) : parent ≠ normal.outcome := by
  have unique := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_append.mp (window ▸ normal.cutPath.simple)).2.1).2).1
  have finishes := normal.cutPath.finishes
  rw [window, List.getLast?_append, List.getLast?_cons_cons, List.getLast?_cons_cons,
    List.getLast?_cons, Option.some_or] at finishes
  have member : .observed normal.outcome ∈ next :: after :=
    List.mem_of_getLast? (List.getLast?_cons.trans finishes)
  intro same
  rw [← same] at member
  exact unique member

/-- A specified unretained fork window joins its literal preceding and
following heads.  Its internality is supplied by the actual list window,
and no new outcome-exclusion or receiver-selection field is required. -/
theorem unretainedFork_window_incidence_edge (parent previous next : Fin S.count)
    (before after : List (SeparationNode S))
    (window : normal.cutPath.nodes = before ++ .observed previous :: .observed parent :: .observed next :: after)
    (fork : normal.cutPath.forkNodes parent = true)
    (unretained : normal.forkApproachNodes boundary pivot forest parent = false) :
    normal.forkPairIncidence boundary pivot forest previous next = true := by
  have pair := normal.unretainedFork_selected_basis_pair_of_window boundary pivot forest
    parent previous next before after window fork unretained
  exact normal.observed_column_edge boundary pivot forest parent previous next pair.2.2.2.1 pair.2.2.2.2.1 pair.1
    (normal.fork_basis_fixed_free pivot parent fork)
    (normal.window_not_outcome pivot parent _ _ before after window) pair.2.2.2.2.2

/-- At a specified retained fork window, the actual own row connects to
the literal following head.  The preceding head was the canceled receiver;
it is not silently kept as a crossing edge through this contact barrier. -/
theorem retainedFork_window_incidence_edge (parent previous next : Fin S.count)
    (before after : List (SeparationNode S))
    (window : normal.cutPath.nodes = before ++ .observed previous :: .observed parent :: .observed next :: after)
    (fork : normal.cutPath.forkNodes parent = true)
    (retained : normal.forkApproachNodes boundary pivot forest parent = true) :
    normal.forkPairIncidence boundary pivot forest parent next = true := by
  have pair := normal.retainedFork_selected_basis_pair_of_window boundary pivot forest
    parent previous next before after window fork retained
  exact normal.observed_column_edge boundary pivot forest parent parent next pair.2.2.1 pair.2.2.2.1 pair.1
    (normal.fork_basis_fixed_free pivot parent fork)
    (normal.window_not_outcome pivot parent _ _ before after window) pair.2.2.2.2

/-- Each literal fork bridge either remains a genuine preceding/following
edge or ends at a true retained approach contact from its following head.
This constructive alternative records the real source-side cancellation;
the retained case must not be replaced by an invented crossing edge. -/
theorem fork_window_incidence_or_contact (parent previous next : Fin S.count)
    (before after : List (SeparationNode S))
    (window : normal.cutPath.nodes = before ++ .observed previous :: .observed parent :: .observed next :: after)
    (fork : normal.cutPath.forkNodes parent = true) :
    normal.forkPairIncidence boundary pivot forest previous next = true ∨
      (normal.forkApproachNodes boundary pivot forest parent = true ∧
        normal.forkPairIncidence boundary pivot forest parent next = true) := by
  cases retained : normal.forkApproachNodes boundary pivot forest parent with
  | false => exact Or.inl (normal.unretainedFork_window_incidence_edge boundary pivot forest parent previous next before after window fork retained)
  | true => exact Or.inr ⟨rfl, normal.retainedFork_window_incidence_edge boundary pivot forest parent previous next before after window fork retained⟩

/-- A literal latent window joins its two actual observed neighbours by
their original reserved root.  Either expanded label chooses the same real
coordinate; adjacency, simplicity and original incidence identify both
receivers without installing a new globally readable switching bit. -/
theorem latent_window_incidence_edge (previous next left right : Fin S.count)
    (before after : List (SeparationNode S))
    (window : normal.cutPath.nodes = before ++ .observed previous :: .latentPair left right :: .observed next :: after) :
    normal.forkPairIncidence boundary pivot forest previous next = true := by
  have member : .latentPair left right ∈ normal.cutPath.nodes := by
    rw [window]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl))))
  let root := normal.cutPath.pairRootOfLatent left right member
  have rootAt : ActivePathInput.rootAt graph root (.latentPair left right) = true := by
    rw [ActivePathInput.rootAt_latent_eq_index normal.cutPath left right member root]
    exact decide_eq_true rfl
  have first := (Consecutive.pair_of_append before (.observed next :: after) (.observed previous) (.latentPair left right)
    (window ▸ normal.cutPath.adjacent)).symm
  have second := Consecutive.pair_of_append (relation := Adjacent graph
    (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node))) (before ++ [.observed previous]) after
      (.latentPair left right) (.observed next) (by simpa only [List.append_assoc, List.singleton_append] using window ▸ normal.cutPath.adjacent)
  have incoming (child : Fin S.count) (neighbor : child = previous ∨ child = next)
      (adjacent : Adjacent graph (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node))
        (.latentPair left right) (.observed child)) :
      ActivePathInput.incomingEdge graph
        (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes (.latentPair left right) child = true := by
    apply Bool.and_eq_true_iff.mpr
    constructor
    · rw [ActivePathInput.stepOnPath_symm]
      apply (ActivePathInput.stepOnPath_internal_window normal.cutPath.simple before after _ _ _ _ window).mpr
      exact neighbor.elim (fun same => Or.inl (congrArg SeparationNode.observed same))
        (fun same => Or.inr (congrArg SeparationNode.observed same))
    · rcases adjacent with forward | impossible
      · exact forward
      · cases impossible
  have previousRead := incoming previous (Or.inl rfl) first
  have nextRead := incoming next (Or.inr rfl) second
  have previousParts := Bool.and_eq_true_iff.mp
    ((ActivePathInput.pairUsed_incident_iff_incoming normal.cutPath root previous).mpr ⟨_, rootAt, previousRead⟩)
  have nextParts := Bool.and_eq_true_iff.mp
    ((ActivePathInput.pairUsed_incident_iff_incoming normal.cutPath root next).mpr ⟨_, rootAt, nextRead⟩)
  have different : previous ≠ next := by
    have unique := (List.nodup_cons.mp (List.nodup_append.mp (window ▸ normal.cutPath.simple)).2.1).1
    intro same
    apply unique
    rw [same]
    exact List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl))
  have edge := normal.originalRoot_incidence_edge boundary pivot forest root previousParts.1
  rcases (pairRootIncident_iff graph.binary root previous).mp previousParts.2 with previousLeft | previousRight
  · rcases (pairRootIncident_iff graph.binary root next).mp nextParts.2 with nextLeft | nextRight
    · exact False.elim (different (previousLeft.trans nextLeft.symm))
    · rw [previousLeft, nextRight]; exact edge
  · rcases (pairRootIncident_iff graph.binary root next).mp nextParts.2 with nextLeft | nextRight
    · rw [previousRight, nextLeft, normal.forkPairIncidence_swap boundary pivot forest]; exact edge
    · exact False.elim (different (previousRight.trans nextRight.symm))

/-! ## Proper mandatory approach edges -/

/-- Every actual proper mandatory-approach edge is a tested pair edge.
Noncontact excludes original conditioning, retained-prefix geometry excludes
all original outcomes, and well-formedness retains both receiving rows. -/
theorem forkApproach_incidence_edge {parent next : Fin S.count}
    (retained : normal.forkApproachNodes boundary pivot forest parent = true)
    (noncontact : normal.forkAbsorptionTargets pivot forest parent = false)
    (edge : normal.forkAbsorptionSuccessor boundary pivot forest parent = some next) :
    normal.forkPairIncidence boundary pivot forest parent next = true := by
  have rows := childWellFormed_edge _ _ (normal.forkAbsorptionSuccessor_wellFormed boundary pivot forest) edge
  have condition : query.condition parent = false := by
    apply Bool.eq_false_iff.mpr
    intro selected
    have core : normal.smallInteractionRows pivot forest parent = true := NodeSet.subset_union_right _ _ parent selected
    have target : normal.forkAbsorptionTargets pivot forest parent = true := NodeSet.subset_union_left _ _ parent core
    exact Bool.false_ne_true (noncontact.symm.trans target)
  have free : NodeSet.union query.action query.condition parent = false :=
    Bool.or_eq_false_iff.mpr ⟨normal.forkAbsorbedInteraction_action_free boundary pivot forest parent rows.1, condition⟩
  have notOutcome : parent ≠ normal.outcome := by
    intro same
    have absent := normal.forkApproachNodes_outcome_free boundary pivot forest parent retained
    rw [same, normal.outcome_selected] at absent
    cases absent
  have different : parent ≠ next := fun same =>
    Nat.ne_of_lt (S.directed_earlier rows.2.2) (congrArg Fin.val same)
  apply normal.observed_column_edge boundary pivot forest parent parent next rows.1 rows.2.1 different free notOutcome
  exact LinearSignal.selectedRowValue_pair_of_rows _ _ _ _ _ rows.1 rows.2.1
    (normal.forkAbsorbedInteraction_noncontact_basis_pair boundary pivot forest noncontact edge)

end ConditionalBackdoorPathNormalForm
end Causality
end Thesis
