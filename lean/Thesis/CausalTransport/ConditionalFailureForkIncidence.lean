import Thesis.CausalTransport.ActivePathForkOrientation
import Thesis.CausalTransport.ConditionalFailureForkApproach

namespace Thesis
namespace Causality

open PathSpecification Probability FiniteBooleanInteraction
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S} {query : ConditionalKernelQuery S}

/-!
# Retained forks have actual own-row/outcome-side-head column incidences

The global supported-direction argument needs genuine two-row input columns,
not merely conservation of their total parity.  Ordinary proper approaches
already have their own-row/successor pair.  A retained normalized fork needs
more care: its original observed bit feeds two heads, and selecting its own
row without canceling the correct side would create a third incidence.

Here every retained fork is proved internal.  The incoming-cut source is a
head, while every complete conditioned boundary path avoids all original
outcomes.  Its actual stopped prefixes inherit that whole-route avoidance,
so the outgoing outcome endpoint cannot be retained as a transmitting fork.
The two actual neighbours are observed, because a fork's neighbouring arrows
point outward and an observed-to-latent arrow is impossible.

The path-order scan cancels the preceding, source-side head.  Activation
fusion preserves both original fork reads because actual path/trace overlap
contains only colliders.  The new parent mask retains precisely the following,
outcome-side head's read; the observed column is consequently the fork's own
row XOR that head.  The actual full-cube basis test has exactly those two row
values.  These are derived facts for every retained fork, not additional
column, window or direction-readiness premises.

This supplies the fork part of the incidence graph.  Connecting the outcome
side to an original Small source, constructing its supported direction, and
proving all outside-Small rows even remain the universal completeness work.
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

private theorem receives_condition : NodeSet.Subset query.condition (normal.forkAbsorptionTargets pivot forest) :=
  fun node selected => NodeSet.subset_union_left _ _ node (NodeSet.subset_union_right _ _ node selected)

/-! ## Retained forks cannot be conditioned or observed endpoints -/

/-- Every omitted normalized vertex really has a true original direction
bit.  Its actual outgoing input excludes a collider, while the source-head
theorem excludes the fixed incoming-cut pivot. -/
theorem forkNodes_direction_true (parent : Fin S.count) (fork : normal.cutPath.forkNodes parent = true) :
    cubeSample graph normal.pathDirection parent = true := by
  have parts := (normal.cutPath.forkNodes_eq_true_iff parent).mp fork
  have different : parent ≠ pivot.node := by
    intro same
    have head := (normal.pathDirection_source_odd pivot.selected).1
    rw [same] at parts
    exact Bool.false_ne_true (parts.2.symm.trans head)
  cases exit : normal.cutPath.forkSuccessor (normal.endpoints_ne pivot) parent with
  | none =>
      have present := normal.cutPath.forkSuccessor_isSome (normal.endpoints_ne pivot) parent fork
      rw [exit] at present
      cases present
  | some child =>
      have input := (normal.cutPath.forkSuccessor_edge (normal.endpoints_ne pivot) exit).2
      have noncollider := ActivePathInput.incoming_observed_parent_not_collider normal.cutPath parent child input
      rw [pathDirection, LinearSignal.activePathDirection_sample]
      exact (ActivePathInput.nonColliderBits_eq_true_iff graph _ normal.cutPath.nodes pivot.node parent).mpr
        ⟨parts.1, different, noncollider⟩

/-- An actual omitted vertex is outside the completed core.  Heads and
real traces are excluded by their proved classifiers/intersection; original
conditioning is excluded by its true supported direction coordinate. -/
theorem forkNodes_core_free (parent : Fin S.count) (fork : normal.cutPath.forkNodes parent = true) :
    normal.smallInteractionRows pivot forest parent = false := by
  have head := ((normal.cutPath.forkNodes_eq_true_iff parent).mp fork).2
  have trace := normal.forkNodes_activationTrace_free pivot forest parent fork
  have condition : query.condition parent = false := by
    cases selected : query.condition parent with
    | false => rfl
    | true =>
        have zero := normal.pathDirection_fixed parent (NodeSet.subset_union_right query.action query.condition parent selected)
        have positive := normal.forkNodes_direction_true pivot parent fork
        rw [zero] at positive
        cases positive
  simp only [smallInteractionRows, activationInteractionRows, pathHeads, NodeSet.union,
    head, trace, condition, Bool.false_or]

/-- Every retained approach vertex avoids every original queried outcome.
The actual prefix is a subset of a complete conditioned boundary path, so
the outcome endpoint is excluded by whole-route stopping and disjointness. -/
theorem forkApproachNodes_outcome_free (parent : Fin S.count)
    (retained : normal.forkApproachNodes boundary pivot forest parent = true) : query.outcome parent = false := by
  rcases (boundary.absorbingNodes_eq_true_iff (normal.forkAbsorptionTargets pivot forest)
    (normal.receives_condition pivot forest) parent).mp retained with ⟨source, inside, visited⟩
  have original := boundary.interactionStopPath_subset_boundary (normal.forkAbsorptionTargets pivot forest)
    (normal.receives_condition pivot forest) source inside parent visited
  exact (FirstConditionedSmallApproach.ofBoundary boundary source inside).outcome_free parent original

/-- Every actually retained fork has a genuine internal observed window.
No internal-window field is assumed: source and outcome exclusion, actual
membership, activity, and the impossible observed-to-latent edge derive it. -/
theorem retainedFork_internal_window (parent : Fin S.count)
    (retained : normal.forkApproachNodes boundary pivot forest parent = true)
    (fork : normal.cutPath.forkNodes parent = true) :
    Exists fun before : List (SeparationNode S) => Exists fun after : List (SeparationNode S) =>
      Exists fun previous : Fin S.count => Exists fun next : Fin S.count =>
        normal.cutPath.nodes = before ++ .observed previous :: .observed parent :: .observed next :: after := by
  have parts := (normal.cutPath.forkNodes_eq_true_iff parent).mp fork
  have notSource : parent ≠ pivot.node := by
    intro same
    have head := (normal.pathDirection_source_odd pivot.selected).1
    rw [same] at parts
    exact Bool.false_ne_true (parts.2.symm.trans head)
  have notTarget : parent ≠ normal.outcome := by
    intro same
    have free := normal.forkApproachNodes_outcome_free boundary pivot forest parent retained
    rw [same, normal.outcome_selected] at free
    cases free
  rcases exists_internal_neighbors_of_mem normal.cutPath.starts normal.cutPath.finishes parts.1
    (fun same => notSource (SeparationNode.observed.inj same))
    (fun same => notTarget (SeparationNode.observed.inj same)) with ⟨before, previous, next, after, window⟩
  have previousStep : ActivePathInput.stepOnPath (.observed parent) previous normal.cutPath.nodes = true := by
    rw [ActivePathInput.stepOnPath_symm]
    exact (ActivePathInput.stepOnPath_internal_window normal.cutPath.simple before after _ _ _ _ window).mpr (Or.inl rfl)
  have nextStep : ActivePathInput.stepOnPath (.observed parent) next normal.cutPath.nodes = true := by
    rw [ActivePathInput.stepOnPath_symm]
    exact (ActivePathInput.stepOnPath_internal_window normal.cutPath.simple before after _ _ _ _ window).mpr (Or.inr rfl)
  have previousEdge := normal.cutPath.forkNodes_outgoing_step parent previous fork previousStep
  have nextEdge := normal.cutPath.forkNodes_outgoing_step parent next fork nextStep
  cases previous with
  | latentPair _ _ => cases previousEdge
  | observed previous =>
      cases next with
      | latentPair _ _ => cases nextEdge
      | observed next => exact ⟨before, after, previous, next, window⟩

/-! ## The computed policy cancels only the source-side receiver -/

/-- At an actual internal retained fork, the core-first policy really
takes the preceding head.  Core omission was derived above, and retained
membership enables the path-order exit rather than an off-domain fallback. -/
theorem forkAbsorptionSuccessor_source_side (parent previous next : Fin S.count)
    (before after : List (SeparationNode S))
    (window : normal.cutPath.nodes = before ++ .observed previous :: .observed parent :: .observed next :: after)
    (retained : normal.forkApproachNodes boundary pivot forest parent = true)
    (fork : normal.cutPath.forkNodes parent = true) :
    normal.forkAbsorptionSuccessor boundary pivot forest parent = some previous := by
  have outside := normal.forkNodes_core_free pivot forest parent fork
  simp only [forkAbsorptionSuccessor, outside, retained, fork, Bool.false_eq_true, if_false, if_true]
  exact normal.cutPath.forkSuccessor_internal_window (normal.endpoints_ne pivot) parent previous next before after window fork

/-- Activation fusion leaves a fork's complete original observed column
unchanged, including its zero entries.  Its actual trace successor is absent;
an unselected head cannot hide a true original path input. -/
theorem activationInteraction_fork_parent_mask (parent child : Fin S.count)
    (fork : normal.cutPath.forkNodes parent = true) :
    (normal.activationInteractionSignal pivot forest).parentMask child parent =
      ActivePathInput.incomingEdge graph (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node))
        normal.cutPath.nodes (.observed parent) child := by
  have stopped : normal.activationTraceSuccessor pivot forest parent = none :=
    restrictChild_of_false (normal.forkNodes_activationTrace_free pivot forest parent fork)
  cases head : normal.pathHeads child with
  | true =>
      simp only [activationInteractionSignal, LinearSignal.absorbSuccessor, head, if_true,
        stopped, reduceCtorEq, decide_false, Bool.xor_false, LinearSignal.ofActivePath]
  | false =>
      have absent : ActivePathInput.incomingEdge graph
          (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes (.observed parent) child = false := by
        apply Bool.eq_false_iff.mpr
        intro read
        exact Bool.false_ne_true (head.symm.trans (ActivePathInput.incomingEdge_head read))
      simp only [activationInteractionSignal, LinearSignal.absorbSuccessor, head, Bool.false_eq_true,
        if_false, stopped, reduceCtorEq, decide_false, absent]

private theorem heads_in_core (child : Fin S.count)
    (head : ActivePathInput.headRows graph
      (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes child = true) :
    normal.smallInteractionRows pivot forest child = true :=
  NodeSet.subset_union_left _ _ child (NodeSet.subset_union_left _ _ child head)

/-- After source-side cancellation, the retained internal fork's parent
mask reads it at precisely the following, outcome-side head.  Every other
row's entry is zero; a fork is not duplicated across an unrelated third row. -/
theorem forkAbsorbedInteraction_outcome_side_mask (parent previous next row : Fin S.count)
    (before after : List (SeparationNode S))
    (window : normal.cutPath.nodes = before ++ .observed previous :: .observed parent :: .observed next :: after)
    (retained : normal.forkApproachNodes boundary pivot forest parent = true)
    (fork : normal.cutPath.forkNodes parent = true) :
    (normal.forkAbsorbedInteractionSignal boundary pivot forest).parentMask row parent = decide (row = next) := by
  have inputs := normal.cutPath.forkNodes_internal_inputs parent previous next before after window fork
  have different := normal.cutPath.fork_internal_neighbors_distinct parent previous next before after window
  have exit := normal.forkAbsorptionSuccessor_source_side boundary pivot forest parent previous next before after window retained fork
  have original := normal.activationInteraction_fork_parent_mask pivot forest parent row fork
  by_cases atPrevious : row = previous
  · subst row
    have core := normal.heads_in_core pivot forest previous (ActivePathInput.incomingEdge_head inputs.1)
    have chosen := normal.forkInput_in_activationInteraction pivot forest fork inputs.1
    simp only [forkAbsorbedInteractionSignal, LinearSignal.absorbSuccessor, core, if_true,
      chosen, exit, decide_true, Bool.xor_self, decide_eq_false different]
  · by_cases atNext : row = next
    · subst row
      have core := normal.heads_in_core pivot forest next (ActivePathInput.incomingEdge_head inputs.2)
      have remaining := normal.forkInput_in_activationInteraction pivot forest fork inputs.2
      simp only [forkAbsorbedInteractionSignal, LinearSignal.absorbSuccessor, core, if_true,
        remaining, exit, Option.some.injEq, decide_eq_false different, Bool.xor_false, decide_true]
    · have noRead : ActivePathInput.incomingEdge graph
          (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes (.observed parent) row = false := by
        apply Bool.eq_false_iff.mpr
        intro read
        rcases (normal.cutPath.forkNodes_internal_input_iff parent previous next row before after window fork).mp read with same | same
        · exact atPrevious same
        · exact atNext same
      have previousDifferent : previous ≠ row := fun same => atPrevious same.symm
      simp only [forkAbsorbedInteractionSignal, LinearSignal.absorbSuccessor, original,
        noRead, exit, Option.some.injEq, decide_eq_false previousDifferent, Bool.xor_self,
        ite_self, decide_eq_false atNext]

/-- The fork's observed column is its own row XOR the following head.
Both the actual original-parent read and the installed declared-edge guard
are accounted for; this is not a guessed sparse linear representation. -/
theorem forkAbsorbedInteraction_fork_column_pair (parent previous next row : Fin S.count)
    (before after : List (SeparationNode S))
    (window : normal.cutPath.nodes = before ++ .observed previous :: .observed parent :: .observed next :: after)
    (retained : normal.forkApproachNodes boundary pivot forest parent = true)
    (fork : normal.cutPath.forkNodes parent = true) :
    (normal.forkAbsorbedInteractionSignal boundary pivot forest).observedRowCoefficient row parent =
      Bool.xor (decide (row = parent)) (decide (row = next)) := by
  rw [LinearSignal.observedRowCoefficient,
    normal.forkAbsorbedInteraction_outcome_side_mask boundary pivot forest parent previous next row before after window retained fork]
  by_cases atNext : row = next
  · subst row
    have declared := LinearSignal.ofActivePath_parent_available normal.cutPath next parent
      (normal.cutPath.forkNodes_internal_inputs parent previous next before after window fork).2
    rw [declared, Bool.true_and]
  · rw [decide_eq_false atNext, Bool.and_false]

/-- Every retained fork has an actual outcome-side neighbour and the
corresponding two-row basis incidence on the full original cube.  Its
window and orientation are derived, not supplied to a terminal caller.
The existential is a theorem in Prop; later data scans need no choice. -/
theorem retainedFork_basis_pair (parent : Fin S.count)
    (retained : normal.forkApproachNodes boundary pivot forest parent = true)
    (fork : normal.cutPath.forkNodes parent = true) :
    Exists fun next : Fin S.count => forall row : Fin S.count,
      ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase row).value
        (basisAssignment (pairRootCount graph.binary + S.count) (Fin.natAdd (pairRootCount graph.binary) parent)) =
        Bool.xor (decide (row = parent)) (decide (row = next)) := by
  rcases normal.retainedFork_internal_window boundary pivot forest parent retained fork with ⟨before, after, previous, next, window⟩
  refine ⟨next, ?_⟩
  intro row
  rw [LinearSignal.rowPhase_observed_basis]
  exact normal.forkAbsorbedInteraction_fork_column_pair boundary pivot forest parent previous next row before after window retained fork

end ConditionalBackdoorPathNormalForm

end Causality
end Thesis
