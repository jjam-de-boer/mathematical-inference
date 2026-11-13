import Thesis.CausalTransport.ConditionalFailurePathIncidence

namespace Thesis
namespace Causality

open PathSpecification Probability FiniteBooleanInteraction
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S} {query : ConditionalKernelQuery S}

/-!
# Selected-row fork columns, with the omitted own row accounted for

The actual retained-fork basis already has an own-row/outcome-side-head
pair.  A fork not met by any complete Small-source prefix must instead keep
its two original receiving heads.  Its own raw row phase still contains its
own bit, but that row is not in the installed union.  Ignoring this selected
row guard would incorrectly give an unretained fork a third incidence.

Here the complete original input column is preserved at an unretained fork,
and its selected-row coefficient is exactly the original path-parent mask.
The general internal-window theorem then gives the two genuine heads.  For
a retained fork the own row is truly selected, the preceding read is canceled,
and the following head remains selected.  Both cases are proved on the actual
full cube, not on a separately proposed sparse matrix.

Every fork basis fixes the complete original action/condition selection.
For an internal fork it also leaves the chosen outcome character unchanged.
This supplies actual supported, outcome-even pair columns for the finite
incidence graph.  Connectivity from the outcome's starting row to Small,
and hence universal conditional completeness, are not assumed or proved here.
-/

namespace ConditionalBackdoorPathNormalForm

variable {w : HedgeWitness graph query.jointNumerator}
    (boundary : ConditionedSmallFlowBoundary w) (pivot : RetainedConditionalPivot query)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (forest : ConditionalCutColliderActivationForest query pivot.node)

private theorem head_selected (row : Fin S.count) (head : normal.pathHeads row = true) :
    normal.forkAbsorbedInteractionRows boundary pivot forest row = true :=
  NodeSet.subset_union_left _ _ row (NodeSet.subset_union_left _ _ row (NodeSet.subset_union_left _ _ row head))

/-- Actual fork coordinates are free on the complete original fixed
selection.  A fixed bit would contradict its proved true supported path bit. -/
theorem fork_basis_fixed_free (parent : Fin S.count) (fork : normal.cutPath.forkNodes parent = true) :
    NodeSet.union query.action query.condition parent = false := by
  apply Bool.eq_false_iff.mpr
  intro fixed
  have zero := normal.pathDirection_fixed parent fixed
  have positive := normal.forkNodes_direction_true pivot parent fork
  exact Bool.false_ne_true (zero.symm.trans positive)

/-- No original reserved input is removed when this observed basis is
used.  Its literal coordinate offset and real original cylinder are retained. -/
theorem fork_basis_supported (parent : Fin S.count) (fork : normal.cutPath.forkNodes parent = true) :
    basisAssignment (pairRootCount graph.binary + S.count) (Fin.natAdd (pairRootCount graph.binary) parent) ∈
      FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count)
        (cubeMask graph (NodeSet.union query.action query.condition)) := by
  apply (basisAssignment_member_iff _ _ _).mpr
  change FiniteProduct.BooleanBlocks.rightBlock (pairRootCount graph.binary) S.count
    (cubeMask graph (NodeSet.union query.action query.condition)) parent = false
  rw [cubeMask, FiniteProduct.BooleanBlocks.rightBlock_join]
  exact normal.fork_basis_fixed_free pivot parent fork

/-- An internal fork's observed basis does not flip the chosen outcome
character.  The outcome endpoint is classified separately by the unified
singleton-incidence theorem and must not be offered as a pair correction. -/
theorem fork_basis_outcome_even (parent : Fin S.count) (notTarget : parent ≠ normal.outcome) :
    (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value
      (basisAssignment (pairRootCount graph.binary + S.count) (Fin.natAdd (pairRootCount graph.binary) parent)) = false := by
  rw [maskPhase_basis]
  change FiniteProduct.BooleanBlocks.rightBlock (pairRootCount graph.binary) S.count
    (cubeMask graph (NodeSet.singleton normal.outcome)) parent = false
  rw [cubeMask, FiniteProduct.BooleanBlocks.rightBlock_join]
  apply Bool.eq_false_iff.mpr
  intro selected
  exact notTarget ((NodeSet.singleton_eq_true_iff normal.outcome parent).mp selected)

/-! ## An unretained fork keeps only the original two receiving rows -/

/-- An omitted fork outside all actual approach prefixes has no installed
own row.  It is also outside the completed core by the actual fork classifier. -/
theorem unretainedFork_rows_free (parent : Fin S.count)
    (fork : normal.cutPath.forkNodes parent = true)
    (unretained : normal.forkApproachNodes boundary pivot forest parent = false) :
    normal.forkAbsorbedInteractionRows boundary pivot forest parent = false := by
  rw [forkAbsorbedInteractionRows, NodeSet.union, normal.forkNodes_core_free pivot forest parent fork, unretained]
  rfl

/-- No mandatory-source continuation exists at an unretained omitted
vertex.  Its original outgoing column is therefore not partially canceled. -/
theorem unretainedFork_successor_none (parent : Fin S.count)
    (fork : normal.cutPath.forkNodes parent = true)
    (unretained : normal.forkApproachNodes boundary pivot forest parent = false) :
    normal.forkAbsorptionSuccessor boundary pivot forest parent = none := by
  simp only [forkAbsorptionSuccessor, normal.forkNodes_core_free pivot forest parent fork,
    unretained, Bool.false_eq_true, if_false]

/-- Both absorption layers preserve every original parent entry at this
unretained fork, including all zero entries at rows outside the core. -/
theorem forkAbsorbedInteraction_unretainedFork_parent_mask (parent row : Fin S.count)
    (fork : normal.cutPath.forkNodes parent = true)
    (unretained : normal.forkApproachNodes boundary pivot forest parent = false) :
    (normal.forkAbsorbedInteractionSignal boundary pivot forest).parentMask row parent =
      ActivePathInput.incomingEdge graph
        (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes (.observed parent) row := by
  have stopped := normal.unretainedFork_successor_none boundary pivot forest parent fork unretained
  have original := normal.activationInteraction_fork_parent_mask pivot forest parent row fork
  cases core : normal.smallInteractionRows pivot forest row with
  | true =>
      simp only [forkAbsorbedInteractionSignal, LinearSignal.absorbSuccessor, core, if_true,
        original, stopped, reduceCtorEq, decide_false, Bool.xor_false]
  | false =>
      have absent : ActivePathInput.incomingEdge graph
          (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes (.observed parent) row = false := by
        apply Bool.eq_false_iff.mpr
        intro read
        have head := ActivePathInput.incomingEdge_head read
        have selected : normal.smallInteractionRows pivot forest row = true :=
          NodeSet.subset_union_left _ _ row (NodeSet.subset_union_left _ _ row head)
        exact Bool.false_ne_true (core.symm.trans selected)
      simp only [forkAbsorbedInteractionSignal, LinearSignal.absorbSuccessor, core,
        Bool.false_eq_true, if_false, stopped, reduceCtorEq, decide_false, absent]

/-- Selection deletes the unretained own bit, not either original head
read.  This exact guarded coefficient is valid for outgoing endpoints too;
only the subsequent internal-window pair theorem excludes the outcome. -/
theorem unretainedFork_selected_coefficient (parent row : Fin S.count)
    (fork : normal.cutPath.forkNodes parent = true)
    (unretained : normal.forkApproachNodes boundary pivot forest parent = false) :
    (if normal.forkAbsorbedInteractionRows boundary pivot forest row then
      (normal.forkAbsorbedInteractionSignal boundary pivot forest).observedRowCoefficient row parent else false) =
      ActivePathInput.incomingEdge graph
        (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes (.observed parent) row := by
  cases selected : normal.forkAbsorbedInteractionRows boundary pivot forest row with
  | true =>
      have different : row ≠ parent := by
        intro same
        subst row
        exact Bool.false_ne_true ((normal.unretainedFork_rows_free boundary pivot forest parent fork unretained).symm.trans selected)
      simp only [if_true, LinearSignal.observedRowCoefficient,
        normal.forkAbsorbedInteraction_unretainedFork_parent_mask boundary pivot forest parent row fork unretained,
        decide_eq_false different, Bool.false_xor]
      cases read : ActivePathInput.incomingEdge graph
          (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes (.observed parent) row with
      | false => rw [Bool.and_false]
      | true => rw [LinearSignal.ofActivePath_parent_available normal.cutPath row parent read, Bool.true_and]
  | false =>
      have absent : ActivePathInput.incomingEdge graph
          (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes (.observed parent) row = false := by
        apply Bool.eq_false_iff.mpr
        intro read
        exact Bool.false_ne_true (selected.symm.trans (normal.head_selected boundary pivot forest row (ActivePathInput.incomingEdge_head read)))
      simp only [Bool.false_eq_true, if_false, absent]

/-- At a specified literal internal window, the complete selected-row
basis of an unretained fork is exactly its two displayed original heads.
Simplicity proves distinctness; neither receiver is selected independently. -/
theorem unretainedFork_selected_basis_pair_of_window (parent previous next : Fin S.count)
    (before after : List (SeparationNode S))
    (window : normal.cutPath.nodes = before ++ .observed previous :: .observed parent :: .observed next :: after)
    (fork : normal.cutPath.forkNodes parent = true)
    (unretained : normal.forkApproachNodes boundary pivot forest parent = false) :
    previous ≠ next ∧ normal.pathHeads previous = true ∧ normal.pathHeads next = true ∧
      normal.forkAbsorbedInteractionRows boundary pivot forest previous = true ∧
      normal.forkAbsorbedInteractionRows boundary pivot forest next = true ∧
      forall row, (if normal.forkAbsorbedInteractionRows boundary pivot forest row then
        ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase row).value
          (basisAssignment (pairRootCount graph.binary + S.count) (Fin.natAdd (pairRootCount graph.binary) parent)) else false) =
        Bool.xor (decide (row = previous)) (decide (row = next)) := by
  have inputs := normal.cutPath.forkNodes_internal_inputs parent previous next before after window fork
  have different := normal.cutPath.fork_internal_neighbors_distinct parent previous next before after window
  have previousHead := ActivePathInput.incomingEdge_head inputs.1
  have nextHead := ActivePathInput.incomingEdge_head inputs.2
  refine ⟨different, previousHead, nextHead,
    normal.head_selected boundary pivot forest previous previousHead,
    normal.head_selected boundary pivot forest next nextHead, ?_⟩
  intro row
  rw [LinearSignal.rowPhase_observed_basis,
    normal.unretainedFork_selected_coefficient boundary pivot forest parent row fork unretained]
  have classified := normal.cutPath.forkNodes_internal_input_iff parent previous next row before after window fork
  by_cases atPrevious : row = previous
  · subst row
    rw [decide_eq_true rfl, decide_eq_false different]
    exact classified.mpr (Or.inl rfl)
  · by_cases atNext : row = next
    · subst row
      rw [decide_eq_false atPrevious, decide_eq_true rfl]
      exact classified.mpr (Or.inr rfl)
    · rw [decide_eq_false atPrevious, decide_eq_false atNext]
      apply Bool.eq_false_iff.mpr
      intro read
      rcases classified.mp read with same | same
      · exact atPrevious same
      · exact atNext same

/-- The complete selected-row basis of an unretained internal fork is
its two genuine original heads.  Membership, endpoint exclusion and
outgoing adjacency derive the literal window before applying its column. -/
theorem unretainedFork_selected_basis_pair (parent : Fin S.count)
    (fork : normal.cutPath.forkNodes parent = true)
    (unretained : normal.forkApproachNodes boundary pivot forest parent = false)
    (notTarget : parent ≠ normal.outcome) :
    Exists fun previous : Fin S.count => Exists fun next : Fin S.count =>
      previous ≠ next ∧ normal.pathHeads previous = true ∧ normal.pathHeads next = true ∧
      normal.forkAbsorbedInteractionRows boundary pivot forest previous = true ∧
      normal.forkAbsorbedInteractionRows boundary pivot forest next = true ∧
      forall row, (if normal.forkAbsorbedInteractionRows boundary pivot forest row then
        ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase row).value
          (basisAssignment (pairRootCount graph.binary + S.count) (Fin.natAdd (pairRootCount graph.binary) parent)) else false) =
        Bool.xor (decide (row = previous)) (decide (row = next)) := by
  rcases normal.internalFork_observed_window pivot parent fork notTarget with ⟨before, after, previous, next, window⟩
  exact ⟨previous, next, normal.unretainedFork_selected_basis_pair_of_window boundary pivot forest
    parent previous next before after window fork unretained⟩

/-! ## A retained fork selects its own row and the outcome-side head -/

/-- The retained-fork pair at a specified actual internal window keeps
its true own row and the following head, not an existentially named receiver.
Both rows survive the union and every unselected row entry is zero. -/
theorem retainedFork_selected_basis_pair_of_window (parent previous next : Fin S.count)
    (before after : List (SeparationNode S))
    (window : normal.cutPath.nodes = before ++ .observed previous :: .observed parent :: .observed next :: after)
    (fork : normal.cutPath.forkNodes parent = true)
    (retained : normal.forkApproachNodes boundary pivot forest parent = true) :
    parent ≠ next ∧ normal.pathHeads next = true ∧
      normal.forkAbsorbedInteractionRows boundary pivot forest parent = true ∧
      normal.forkAbsorbedInteractionRows boundary pivot forest next = true ∧
      forall row, (if normal.forkAbsorbedInteractionRows boundary pivot forest row then
        ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase row).value
          (basisAssignment (pairRootCount graph.binary + S.count) (Fin.natAdd (pairRootCount graph.binary) parent)) else false) =
        Bool.xor (decide (row = parent)) (decide (row = next)) := by
  have input := (normal.cutPath.forkNodes_internal_inputs parent previous next before after window fork).2
  have nextHead := ActivePathInput.incomingEdge_head input
  have parentSelected : normal.forkAbsorbedInteractionRows boundary pivot forest parent = true :=
    NodeSet.subset_union_right _ _ parent retained
  have nextSelected := normal.head_selected boundary pivot forest next nextHead
  refine ⟨?_, nextHead, parentSelected, nextSelected, ?_⟩
  · intro same
    exact Nat.ne_of_lt (S.directed_earlier (LinearSignal.ofActivePath_parent_available normal.cutPath next parent input))
      (congrArg Fin.val same)
  · intro row
    rw [LinearSignal.rowPhase_observed_basis,
      normal.forkAbsorbedInteraction_fork_column_pair boundary pivot forest parent previous next row before after window retained fork]
    by_cases atParent : row = parent
    · subst row
      simp only [parentSelected, if_true]
    · by_cases atNext : row = next
      · subst row
        simp only [nextSelected, if_true]
      · rw [decide_eq_false atParent, decide_eq_false atNext]
        exact ite_self false

/-- Every retained fork supplies that guarded own/following-head pair.
Its internal window is derived from the actual complete-prefix geometry;
the original public existential interface remains unchanged. -/
theorem retainedFork_selected_basis_pair (parent : Fin S.count)
    (fork : normal.cutPath.forkNodes parent = true)
    (retained : normal.forkApproachNodes boundary pivot forest parent = true) :
    Exists fun next : Fin S.count => parent ≠ next ∧ normal.pathHeads next = true ∧
      normal.forkAbsorbedInteractionRows boundary pivot forest parent = true ∧
      normal.forkAbsorbedInteractionRows boundary pivot forest next = true ∧
      forall row, (if normal.forkAbsorbedInteractionRows boundary pivot forest row then
        ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase row).value
          (basisAssignment (pairRootCount graph.binary + S.count) (Fin.natAdd (pairRootCount graph.binary) parent)) else false) =
        Bool.xor (decide (row = parent)) (decide (row = next)) := by
  rcases normal.retainedFork_internal_window boundary pivot forest parent retained fork with ⟨before, after, previous, next, window⟩
  exact ⟨next, normal.retainedFork_selected_basis_pair_of_window boundary pivot forest
    parent previous next before after window fork retained⟩

end ConditionalBackdoorPathNormalForm

end Causality
end Thesis
