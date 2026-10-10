import Thesis.CausalTransport.ActivePathHeadBridges
import Thesis.CausalTransport.ConditionalFailureFirstContact

namespace Thesis
namespace Causality

open PathSpecification Probability FiniteBooleanInteraction
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S} {query : ConditionalKernelQuery S}

/-!
# Walk backward from the actual outcome incidence to a genuine Small contact

The original normalized path orders its incoming head rows.  Successive heads
have an actual observed-input bridge, an original latent-root bridge, or an
omitted observed fork between them.  The first two are genuine edges of the
installed incidence graph.  An unretained fork is also a crossing pair edge;
a retained fork instead connects its own row to the following head.  That row
is a real mandatory approach contact, so the backward walk finishes there
rather than inventing a crossing edge to the canceled preceding receiver.

The literal original outcome basis has just one selected receiver.  Depending
on endpoint orientation, that row is either the outcome's own incoming head
or its actual outgoing neighbour.  In both cases it is the last projected head.
Structural backward recursion therefore proves the required dichotomy: the
outcome reaches a genuine retained-fork contact and hence Small, or every
normalized head is connected to it.  No connectivity flag is supplied.

For a genuine first-conditioned Small approach, the already-proved first
combined contact closes the latter branch as well.  The complete finite Small
search succeeds at the original observed-count bound; its existing constructive
direction and semantic constructor then give positive original-query
countermodels.  Arbitrary retained pivots are not asserted to suffice.
-/

namespace ConditionalBackdoorPathNormalForm

variable {w : HedgeWitness graph query.jointNumerator}
    (boundary : ConditionedSmallFlowBoundary w) (pivot : RetainedConditionalPivot query)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (forest : ConditionalCutColliderActivationForest query pivot.node)

/-- Every literal successive-head bridge is either a real incidence
edge or an actual retained-fork contact reached from its following head.
The exact original windows identify the installed coordinates, rather than
merely asserting connectivity in an auxiliary contracted graph. -/
theorem headBridge_incidence_or_contact (left right : Fin S.count)
    (bridge : ActivePathInput.HeadBridge graph
      (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node))
        normal.cutPath.nodes left right) :
    normal.forkPairIncidence boundary pivot forest left right = true ∨
      (Exists fun contact => normal.forkApproachNodes boundary pivot forest contact = true ∧
        normal.forkPairIncidence boundary pivot forest contact right = true) := by
  rcases bridge with ⟨leftHead, rightHead, direct | latent | fork⟩
  · rcases direct with ⟨before, after, window⟩
    have adjacent := Consecutive.pair_of_append before after _ _ (window ▸ normal.cutPath.adjacent)
    have step : ActivePathInput.stepOnPath (.observed left) (.observed right) normal.cutPath.nodes = true :=
      (ActivePathInput.stepOnPath_eq_true_iff _ _ _).mpr ⟨before, after, Or.inl window⟩
    apply Or.inl
    rcases adjacent with forward | backward
    · exact normal.pathHead_incidence_edge_of_input boundary pivot forest leftHead
        (Bool.and_eq_true_iff.mpr ⟨step, forward⟩)
    · have reverseStep := (ActivePathInput.stepOnPath_symm _ _ _).trans step
      exact (normal.forkPairIncidence_swap boundary pivot forest left right).trans
        (normal.pathHead_incidence_edge_of_input boundary pivot forest rightHead
          (Bool.and_eq_true_iff.mpr ⟨reverseStep, backward⟩))
  · rcases latent with ⟨before, after, rootLeft, rootRight, window⟩
    exact Or.inl (normal.latent_window_incidence_edge boundary pivot forest left right rootLeft rootRight before after window)
  · rcases fork with ⟨before, after, parent, window, noHead⟩
    have actualFork : normal.cutPath.forkNodes parent = true :=
      (normal.cutPath.forkNodes_eq_true_iff parent).mpr ⟨by
        rw [window]
        exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl)))), noHead⟩
    rcases normal.fork_window_incidence_or_contact boundary pivot forest parent left right before after window actualFork with edge | contact
    · exact Or.inl edge
    · exact Or.inr ⟨parent, contact⟩

/-- The actual outcome scan returns a genuine original head.  Its unique
selected-column theorem identifies the returned row; no receiver is chosen
from the propositional existence used in this proof. -/
theorem forkOutcomeIncidenceRow_head :
    normal.pathHeads (normal.forkOutcomeIncidenceRow boundary pivot forest) = true := by
  rcases normal.pathOutcome_selected_basis_single boundary pivot forest with ⟨receiver, head, _selected, column⟩
  have positive := listFirstAny_pred (NodeSet.enumerated S)
    (normal.forkOutcomeIncidenceRowTest boundary pivot forest) (normal.forkOutcomeIncidenceRow_found boundary pivot forest)
  change (if normal.forkAbsorbedInteractionRows boundary pivot forest
      (normal.forkOutcomeIncidenceRow boundary pivot forest) then
    ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase
      (normal.forkOutcomeIncidenceRow boundary pivot forest)).value
      (basisAssignment _ (Fin.natAdd (pairRootCount graph.binary) normal.outcome)) else false) = true at positive
  rw [column (normal.forkOutcomeIncidenceRow boundary pivot forest)] at positive
  have same : normal.forkOutcomeIncidenceRow boundary pivot forest = receiver := of_decide_eq_true positive
  rw [same]
  exact head

-- A positive read of the literal outcome basis identifies the already
-- computed unique receiver.  This is a propositional comparison of two
-- actual finite outputs, not extraction of a new receiver from existence.
private theorem outcome_receiver_eq (row : Fin S.count)
    (positive : (normal.forkAbsorbedInteractionSignal boundary pivot forest).selectedRowValue
      (normal.forkAbsorbedInteractionRows boundary pivot forest) row
      (basisAssignment (pairRootCount graph.binary + S.count) (Fin.natAdd (pairRootCount graph.binary) normal.outcome)) = true) :
    row = normal.forkOutcomeIncidenceRow boundary pivot forest := by
  rw [normal.forkOutcomeIncidence_basis_single boundary pivot forest row] at positive
  exact of_decide_eq_true positive

/-- The unique actual outcome receiver is the last head of the original
path-order projection in both endpoint orientations.  An outgoing endpoint
has no selected own row; the literal final observed neighbour receives it.
This identifies the starting point of the backward proof without a new
endpoint orientation, row coverage, or connectivity hypothesis. -/
theorem headNodes_getLast_outcomeIncidenceRow :
    (ActivePathInput.headNodes graph
      (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes).getLast? =
        some (normal.forkOutcomeIncidenceRow boundary pivot forest) := by
  cases head : normal.pathHeads normal.outcome with
  | true =>
      have selected : normal.forkAbsorbedInteractionRows boundary pivot forest normal.outcome = true :=
        NodeSet.subset_union_left _ _ _ (NodeSet.subset_union_left _ _ _ (NodeSet.subset_union_left _ _ _ head))
      have positive : (normal.forkAbsorbedInteractionSignal boundary pivot forest).selectedRowValue
          (normal.forkAbsorbedInteractionRows boundary pivot forest) normal.outcome
          (basisAssignment _ (Fin.natAdd (pairRootCount graph.binary) normal.outcome)) = true := by
        change (if _ then _ else false) = true
        simp only [selected, if_true]
        rw [normal.pathHead_outcome_basis_single boundary pivot forest head, decide_eq_true rfl]
      rw [← normal.outcome_receiver_eq boundary pivot forest normal.outcome positive]
      exact ActivePathInput.headNodes_getLast_of_target_head normal.cutPath head
  | false =>
      have distinct : pivot.node ≠ normal.outcome := by
        intro same
        have free := query.outcome_condition_disjoint normal.outcome normal.outcome_selected
        rw [← same, pivot.selected] at free
        cases free
      rcases ActivePathInput.target_nonhead_unique_input normal.cutPath distinct head with ⟨receiver, column⟩
      have input : ActivePathInput.incomingEdge graph
          (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node)) normal.cutPath.nodes
            (.observed normal.outcome) receiver = true := (column receiver).trans (decide_eq_true rfl)
      have declared := LinearSignal.ofActivePath_parent_available normal.cutPath receiver normal.outcome input
      have different : receiver ≠ normal.outcome := fun same =>
        Nat.ne_of_lt (S.directed_earlier declared) (congrArg Fin.val same.symm)
      have selected : normal.forkAbsorbedInteractionRows boundary pivot forest receiver = true :=
        NodeSet.subset_union_left _ _ _ (NodeSet.subset_union_left _ _ _
          (NodeSet.subset_union_left _ _ _ (ActivePathInput.incomingEdge_head input)))
      have positive : (normal.forkAbsorbedInteractionSignal boundary pivot forest).selectedRowValue
          (normal.forkAbsorbedInteractionRows boundary pivot forest) receiver
          (basisAssignment _ (Fin.natAdd (pairRootCount graph.binary) normal.outcome)) = true := by
        change (if _ then _ else false) = true
        simp only [selected, if_true]
        rw [LinearSignal.rowPhase_observed_basis, LinearSignal.observedRowCoefficient,
          normal.forkAbsorbedInteraction_outgoing_outcome_parent_mask boundary pivot forest head,
          input, declared, decide_eq_false different]
        rfl
      rw [← normal.outcome_receiver_eq boundary pivot forest receiver positive]
      exact ActivePathInput.headNodes_getLast_of_target_input normal.cutPath receiver input

-- Walk from the last head backward.  A retained-fork barrier already gives
-- the real approach contact and therefore a complete Small connection;
-- otherwise reverse the actual symmetric edge and extend the known route.
-- The recursion consumes supplied constructive edge/contact alternatives,
-- never excluded middle on graph reachability or on semantic identifiability.
private theorem heads_connected_or_small_of_bridges : forall nodes : List (Fin S.count),
    Consecutive (fun left right => normal.forkPairIncidence boundary pivot forest left right = true ∨
      (Exists fun contact => normal.forkApproachNodes boundary pivot forest contact = true ∧
        normal.forkPairIncidence boundary pivot forest contact right = true)) nodes ->
    (forall last, nodes.getLast? = some last ->
      FiniteReachability.Reachable (normal.forkPairIncidence boundary pivot forest)
        (normal.forkOutcomeIncidenceRow boundary pivot forest) last) ->
    normal.forkOutcomeReachesSmallTest boundary pivot forest S.count = true ∨
      (forall head, head ∈ nodes -> FiniteReachability.Reachable (normal.forkPairIncidence boundary pivot forest)
        (normal.forkOutcomeIncidenceRow boundary pivot forest) head)
  | [], _bridges, _last => Or.inr (fun _ impossible => False.elim (List.not_mem_nil impossible))
  | [head], _bridges, last => Or.inr (by
      intro row member
      have same : row = head := List.mem_singleton.mp member
      subst row
      exact last head rfl)
  | head :: next :: rest, bridges, last => by
      rcases heads_connected_or_small_of_bridges (next :: rest) bridges.2
        (fun row finish => last row (List.getLast?_cons_cons.trans finish)) with small | tailConnected
      · exact Or.inl small
      · rcases bridges.1 with edge | ⟨contact, retained, edge⟩
        · have reversed := (normal.forkPairIncidence_swap boundary pivot forest next head).trans edge
          have toHead := LinearSignal.pairIncidence_reachable_trans _ _ _ _
            (tailConnected next List.mem_cons_self)
            (FiniteReachability.Reachable.prepend reversed (FiniteReachability.Reachable.refl _ head))
          apply Or.inr
          intro row member
          rcases List.mem_cons.mp member with same | later
          · exact same ▸ toHead
          · exact tailConnected row later
        · have reversed := (normal.forkPairIncidence_swap boundary pivot forest next contact).trans edge
          have toContact := LinearSignal.pairIncidence_reachable_trans _ _ _ _
            (tailConnected next List.mem_cons_self)
            (FiniteReachability.Reachable.prepend reversed (FiniteReachability.Reachable.refl _ contact))
          exact Or.inl (normal.forkOutcomeReachesSmallTest_of_approach_contact boundary pivot forest contact retained toContact)

/-- Universal normalized-head/retained-fork-contact dichotomy for the
actual installed incidence graph.  The outcome's component either already
reaches Small through a genuine retained contact, or contains every original
normalized head.  No finite-search success or readiness flag is assumed. -/
theorem pathHeads_connected_or_forkOutcomeReachesSmallTest :
    (forall head, normal.pathHeads head = true ->
      FiniteReachability.Reachable (normal.forkPairIncidence boundary pivot forest)
        (normal.forkOutcomeIncidenceRow boundary pivot forest) head) ∨
      normal.forkOutcomeReachesSmallTest boundary pivot forest S.count = true := by
  have bridges := Consecutive.mono (normal.headBridge_incidence_or_contact boundary pivot forest)
    _ (ActivePathInput.headNodes_consecutive_bridges normal.cutPath)
  rcases normal.heads_connected_or_small_of_bridges boundary pivot forest _ bridges
    (fun last finish => by
      rw [normal.headNodes_getLast_outcomeIncidenceRow boundary pivot forest] at finish
      have same := Option.some.inj finish
      rw [← same]
      exact FiniteReachability.Reachable.refl _ _) with small | connected
  · exact Or.inr small
  · exact Or.inl (fun head selected => connected head
      ((ActivePathInput.mem_headNodes_iff _ _ _ head).mpr selected))

end ConditionalBackdoorPathNormalForm

namespace FirstConditionedSmallApproach

variable {w : HedgeWitness graph query.jointNumerator}
    (boundary : ConditionedSmallFlowBoundary w) (approach : FirstConditionedSmallApproach w)
    (normal : ConditionalBackdoorPathNormalForm graph query approach.pivot.node)
    (forest : ConditionalCutColliderActivationForest query approach.pivot.node)

/-- A genuine first-conditioned Small approach universally connects the
actual outcome incidence to original Small at the original finite bound.
The backward path theorem supplies the missing connected-head/contact
alternative; the genuine first-contact classification closes its other
branch.  Neither connectivity nor parity is an additional hypothesis. -/
theorem forkOutcomeReachesSmallTest :
    normal.forkOutcomeReachesSmallTest boundary approach.pivot forest S.count = true := by
  rcases normal.pathHeads_connected_or_forkOutcomeReachesSmallTest boundary approach.pivot forest with connected | small
  · exact approach.forkOutcomeReachesSmallTest_of_pathHeads_connected boundary normal forest connected
  · exact small

end FirstConditionedSmallApproach

/-- Positive countermodels for the hard first-conditioned-approach branch,
using the original alphabets, full query and independent reserved roots.
The actual structural connectivity theorem now supplies the finite-search
certificate formerly required by the semantic incidence constructor. -/
noncomputable def conditionalCounterexampleOfFirstConditionedSmallApproach
    {w : HedgeWitness graph query.jointNumerator} (rich : S.ValueRich)
    (boundary : ConditionedSmallFlowBoundary w) (approach : FirstConditionedSmallApproach w)
    (normal : ConditionalBackdoorPathNormalForm graph query approach.pivot.node)
    (forest : ConditionalCutColliderActivationForest query approach.pivot.node) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  conditionalCounterexampleOfForkIncidenceReachability w rich boundary approach.pivot normal forest
    S.count (approach.forkOutcomeReachesSmallTest boundary normal forest)

end Causality
end Thesis
