import Thesis.CausalTransport.ConditionalFailureForkColumns
import Thesis.CausalTransport.HedgeChannelEnvironmentIncidence

namespace Thesis
namespace Causality

open PathSpecification Probability FiniteBooleanInteraction
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S} {query : ConditionalKernelQuery S}

/-!
# Actual outcome-to-Small incidence search supplies the semantic direction

The original outcome basis has exactly one selected incidence, in either
endpoint orientation.  Its receiving row is obtained here by a finite scan
of the actual installed phases, not by selecting the existential receiver
from the proof-level column theorem.

The edge relation is the complete tested original-cube pair incidence of
`HedgeChannelEnvironmentIncidence`.  A second finite scan searches the entire
original Small set for a row reached from that actual starting incidence.
Whenever this bounded search succeeds, the general transport construction
supplies a supported odd-outcome direction with only that Small row odd.
Every actual outside-Small background row is therefore even, and the existing
matching/covariance constructor supplies positive original-alphabet models
for the unchanged conditional query.

This replaces supplied parity-readiness fields by one explicit graph leaf:
prove the actual finite outcome-to-Small search succeeds for each terminal.
No universal success theorem is asserted here.  Neither a bounded example
nor the ability to run the search inhabits published conditional completeness
without that still-required structural connectivity proof.
-/

namespace ConditionalBackdoorPathNormalForm

variable {w : HedgeWitness graph query.jointNumerator}
    (boundary : ConditionedSmallFlowBoundary w) (pivot : RetainedConditionalPivot query)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (forest : ConditionalCutColliderActivationForest query pivot.node)

/-- Scan the actual selected rows for their read of the literal original
outcome basis.  The installed union, including mandatory approach rows,
is used unchanged; the head classifier is not substituted as row coverage. -/
def forkOutcomeIncidenceRowTest (row : Fin S.count) : Bool :=
  (normal.forkAbsorbedInteractionSignal boundary pivot forest).selectedRowValue
    (normal.forkAbsorbedInteractionRows boundary pivot forest) row
    (basisAssignment (pairRootCount graph.binary + S.count) (Fin.natAdd (pairRootCount graph.binary) normal.outcome))

/-- The unified actual singleton column proves that the finite scan
cannot fail.  Its existential is eliminated only inside this proposition. -/
theorem forkOutcomeIncidenceRow_found :
    (NodeSet.enumerated S).any (normal.forkOutcomeIncidenceRowTest boundary pivot forest) = true := by
  rcases normal.pathOutcome_selected_basis_single boundary pivot forest with ⟨receiver, _head, _selected, column⟩
  apply List.any_eq_true.mpr
  refine ⟨receiver, NodeSet.mem_enumerated S receiver, ?_⟩
  change (if _ then _ else false) = true
  rw [column receiver, decide_eq_true rfl]

/-- The receiving row is computed by the successful finite test.  Its
data do not come from an existential receiver or a terminal orientation flag. -/
def forkOutcomeIncidenceRow : Fin S.count :=
  listFirstAny (NodeSet.enumerated S) (normal.forkOutcomeIncidenceRowTest boundary pivot forest)
    (normal.forkOutcomeIncidenceRow_found boundary pivot forest)

/-- The computed receiver is a genuine row of the full installation. -/
theorem forkOutcomeIncidenceRow_selected :
    normal.forkAbsorbedInteractionRows boundary pivot forest
      (normal.forkOutcomeIncidenceRow boundary pivot forest) = true := by
  have positive := listFirstAny_pred (NodeSet.enumerated S)
    (normal.forkOutcomeIncidenceRowTest boundary pivot forest) (normal.forkOutcomeIncidenceRow_found boundary pivot forest)
  change (if normal.forkAbsorbedInteractionRows boundary pivot forest
    (normal.forkOutcomeIncidenceRow boundary pivot forest) then _ else false) = true at positive
  cases chosen : normal.forkAbsorbedInteractionRows boundary pivot forest
      (normal.forkOutcomeIncidenceRow boundary pivot forest) with
  | true => rfl
  | false => simp only [chosen, Bool.false_eq_true, if_false] at positive

/-- The finite receiver has the entire exact singleton column, not merely
one positive entry.  Uniqueness follows from the existing actual column. -/
theorem forkOutcomeIncidence_basis_single (row : Fin S.count) :
    (normal.forkAbsorbedInteractionSignal boundary pivot forest).selectedRowValue
      (normal.forkAbsorbedInteractionRows boundary pivot forest) row
      (basisAssignment (pairRootCount graph.binary + S.count) (Fin.natAdd (pairRootCount graph.binary) normal.outcome)) =
        decide (row = normal.forkOutcomeIncidenceRow boundary pivot forest) := by
  rcases normal.pathOutcome_selected_basis_single boundary pivot forest with ⟨receiver, _head, _selected, column⟩
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
  exact column row

/-- The actual tested pair relation, using the unchanged original fixed
selection and the chosen original outcome character.  In particular fixed
conditioners are not available as correction coordinates. -/
def forkPairIncidence : Fin S.count -> Fin S.count -> Bool :=
  (normal.forkAbsorbedInteractionSignal boundary pivot forest).pairIncidence
    (normal.forkAbsorbedInteractionRows boundary pivot forest)
    (cubeMask graph (NodeSet.union query.action query.condition))
    (cubeMask graph (NodeSet.singleton normal.outcome))

/-- The precise remaining graph search: one actual starting row, actual
tested pair columns, and every original Small row as a possible target.
Fuel is explicit; a successful test does not assert universal connectivity. -/
def forkOutcomeReachesSmallTest (fuel : Nat) : Bool :=
  (NodeSet.members w.small).any (fun target => FiniteReachability.within finBeq
    (NodeSet.enumerated S) (normal.forkPairIncidence boundary pivot forest) fuel
    (normal.forkOutcomeIncidenceRow boundary pivot forest) target)

/-- Compute the first reached Small target from the finite successful
search.  Small is never reduced to the retained pivot or a chosen sink. -/
def forkIncidenceSmallTarget (fuel : Nat)
    (connected : normal.forkOutcomeReachesSmallTest boundary pivot forest fuel = true) : Fin S.count :=
  listFirstAny (NodeSet.members w.small) _ connected

/-- The computed target belongs to the complete original Small set. -/
theorem forkIncidenceSmallTarget_selected (fuel : Nat)
    (connected : normal.forkOutcomeReachesSmallTest boundary pivot forest fuel = true) :
    w.small (normal.forkIncidenceSmallTarget boundary pivot forest fuel connected) = true :=
  (NodeSet.mem_members_iff _ _).mp (listFirstAny_mem (NodeSet.members w.small) _ connected)

/-- The selected target is reached by the actual bounded pair graph. -/
theorem forkIncidenceSmallTarget_reached (fuel : Nat)
    (connected : normal.forkOutcomeReachesSmallTest boundary pivot forest fuel = true) :
    FiniteReachability.within finBeq (NodeSet.enumerated S)
      (normal.forkPairIncidence boundary pivot forest) fuel
      (normal.forkOutcomeIncidenceRow boundary pivot forest)
      (normal.forkIncidenceSmallTarget boundary pivot forest fuel connected) = true :=
  listFirstAny_pred (NodeSet.members w.small) _ connected

/-- A successful actual connection supplies all direction parity fields.
The original outcome basis starts odd and supported; the computed route
cancels its initial row and changes only the reached original Small row. -/
def forkIncidenceReadout (fuel : Nat)
    (connected : normal.forkOutcomeReachesSmallTest boundary pivot forest fuel = true) :
    LinearSignal.IncidenceReadoutDirection (normal.forkAbsorbedInteractionSignal boundary pivot forest)
      (normal.forkAbsorbedInteractionRows boundary pivot forest)
      (cubeMask graph (NodeSet.union query.action query.condition))
      (cubeMask graph (NodeSet.singleton normal.outcome))
      (normal.forkIncidenceSmallTarget boundary pivot forest fuel connected) := by
  let route := LinearSignal.IncidenceTransport.ofReachability
    (normal.forkAbsorbedInteractionSignal boundary pivot forest)
    (normal.forkAbsorbedInteractionRows boundary pivot forest)
    (cubeMask graph (NodeSet.union query.action query.condition))
    (cubeMask graph (NodeSet.singleton normal.outcome))
    (normal.forkIncidenceSmallTarget boundary pivot forest fuel connected) fuel
    (normal.forkOutcomeIncidenceRow boundary pivot forest)
    (normal.forkIncidenceSmallTarget_reached boundary pivot forest fuel connected)
  apply route.finish _ (normal.pathOutcome_basis_supported pivot) _
    (normal.forkOutcomeIncidence_basis_single boundary pivot forest)
  rw [maskPhase_basis]
  change FiniteProduct.BooleanBlocks.rightBlock _ _ (cubeMask graph (NodeSet.singleton normal.outcome)) normal.outcome = true
  rw [cubeMask, FiniteProduct.BooleanBlocks.rightBlock_join]
  exact (NodeSet.singleton_eq_true_iff normal.outcome normal.outcome).mpr rfl

/-- Actual background evenness follows from the reached Small row, not
from a new terminal parity flag.  Every outside-Small row remains selected
in the test and is different from that genuine original Small target. -/
theorem forkIncidenceReadout_background_even (fuel : Nat)
    (connected : normal.forkOutcomeReachesSmallTest boundary pivot forest fuel = true)
    (row : Fin S.count)
    (chosen : normal.forkAbsorbedInteractionBackgroundRows boundary pivot forest row = true) :
    ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase row).value
      (normal.forkIncidenceReadout boundary pivot forest fuel connected).direction = false := by
  apply LinearSignal.IncidenceReadoutDirection.other_row_even _ row (Bool.and_eq_true_iff.mp chosen).1
  intro same
  have outside := normal.forkAbsorbedInteractionBackground_outside_small boundary pivot forest row chosen
  rw [same, normal.forkIncidenceSmallTarget_selected boundary pivot forest fuel connected] at outside
  cases outside

end ConditionalBackdoorPathNormalForm

/-- Assemble the complete matching witness from one true actual finite
connectivity test.  Complete Small oddness is derived by the existing
matching theorem, with no independent direction-readiness arguments. -/
def HedgeChannelEnvironmentInstallation.ConditionalParityWitness.ofForkIncidenceReachability
    (w : HedgeWitness graph query.jointNumerator) (boundary : ConditionedSmallFlowBoundary w)
    (pivot : RetainedConditionalPivot query)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (forest : ConditionalCutColliderActivationForest query pivot.node) (fuel : Nat)
    (connected : normal.forkOutcomeReachesSmallTest boundary pivot forest fuel = true) :
    ConditionalParityWitness w (normal.forkAbsorbedInteractionSignal boundary pivot forest)
      (normal.forkAbsorbedInteractionSignal boundary pivot forest) :=
  .ofForkAbsorbedInteraction w boundary pivot normal forest
    (normal.forkIncidenceReadout boundary pivot forest fuel connected).direction
    (normal.forkIncidenceReadout boundary pivot forest fuel connected).supported
    (normal.forkIncidenceReadout boundary pivot forest fuel connected).outcome_odd
    (normal.forkIncidenceReadout_background_even boundary pivot forest fuel connected)

/-- Positive models on every original observed label, with the unchanged
conditional query gap, whenever the actual outcome-to-Small search succeeds.
Proving that success for all terminals is still the universal graph leaf. -/
noncomputable def conditionalCounterexampleOfForkIncidenceReachability
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (boundary : ConditionedSmallFlowBoundary w) (pivot : RetainedConditionalPivot query)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (forest : ConditionalCutColliderActivationForest query pivot.node) (fuel : Nat)
    (connected : normal.forkOutcomeReachesSmallTest boundary pivot forest fuel = true) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  conditionalCounterexampleOfParity w rich (normal.forkAbsorbedInteractionSignal boundary pivot forest)
    (normal.forkAbsorbedInteractionSignal boundary pivot forest)
    (.ofForkIncidenceReachability w boundary pivot normal forest fuel connected)

end Causality
end Thesis
