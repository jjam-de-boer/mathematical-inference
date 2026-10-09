import Thesis.CausalTransport.HedgeChannelEnvironmentMoments
import Thesis.CausalTransport.HedgeChannelEnvironmentCoefficients

namespace Thesis
namespace Causality
namespace HedgeChannelEnvironmentInstallation

open Probability
open HedgeChannelInstallation
open FiniteBooleanInteraction

/-!
# Full original conditional countermodels from explicit finite parity data

The preceding modules identify the actual installed likelihood and normalized
query response with the homogeneous full-outcome covariance.  This module
uses that identity to build a positive, original-alphabet countermodel pair
from a displayed finite direction and interaction selection.

The witness below carries only graph-facing parity data: an outcome-subset
mask, an odd direction on the unchanged conditioning cylinder, and positive
even background rows whose combined character matches on the *whole*
cylinder.  It assumes neither a positive integral nor a separated semantic
cell.  Local homogeneity, installed coefficient inequalities, the complete
outcome-subset sum, and both changing evidence masses have already been proved.

The resulting constructor compares the actual all-false original query cell
and lifts that same cell to every supplied original label.  It does not
replace the outcome with a selected endpoint, require equal conditioning
masses, or add a globally incident shared switching variable.

Universal conditional completeness still needs to construct this finite
parity witness from every required irreducible active path, including collider
activation branches and intersections with the small forest.  The witness
is an explicit remaining obligation, not an asserted universal instance.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S} {query : ConditionalKernelQuery S}

/-- Actual finite parity data sufficient to separate the full original
conditional query.  The direction and selections are supplied Type-level
data, not representatives extracted from an existential proposition. -/
structure ConditionalParityWitness (w : HedgeWitness G query.jointNumerator) (small background : LinearSignal G) where
  outcomeMask : Cube G
  outcomeMask_member : outcomeMask ∈ outcomeMasks (pairRootCount G.binary + S.count) (cubeMask G query.outcome)
  direction : Cube G
  direction_member : direction ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount G.binary + S.count)
    (cubeMask G (NodeSet.union query.action query.condition))
  small_odd : (LinearSignal.forestPhase small w.small).value direction = true
  outcome_odd : (maskPhase (pairRootCount G.binary + S.count) outcomeMask).value direction = true
  selected : NodeSet S
  selected_outside_small : forall child, selected child = true -> w.small child = false
  selected_avoids_action : forall child, selected child = true -> query.action child = false
  selected_even : forall child, selected child = true -> (LinearSignal.rowPhase background child).value direction = false
  matching : forall point, point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount G.binary + S.count)
      (cubeMask G (NodeSet.union query.action query.condition)) ->
    ((LinearSignal.forestPhase small w.small).xor (maskPhase (pairRootCount G.binary + S.count) outcomeMask)).value point =
      (selectedPhase (pairRootCount G.binary + S.count) S.count selected (LinearSignal.rowPhase background)).value point

namespace ConditionalParityWitness

variable {w : HedgeWitness G query.jointNumerator} {small background : LinearSignal G}

/-- Construct the full parity witness by matching only the free coordinate
directions of the actual installed phases.  Homogeneity proves the required
identity on the entire conditioning cylinder, including all environments.
The small phase's oddness is then derived from that identity, the supplied
odd outcome direction, and the even selected rows; it is not another flag
which an active-path constructor must independently justify.

The remaining fields still concern genuine finite graph data.  This adapter
does not assert their existence for every active path or infer matching from
one favorable sample.  It reduces the universal phase equation to exact
coordinate conservation without reducing any complete likelihood support. -/
def ofBasis (outcomeMask : Cube G)
    (outcomeMask_member : outcomeMask ∈ outcomeMasks (pairRootCount G.binary + S.count) (cubeMask G query.outcome))
    (direction : Cube G)
    (direction_member : direction ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount G.binary + S.count)
      (cubeMask G (NodeSet.union query.action query.condition)))
    (outcome_odd : (maskPhase (pairRootCount G.binary + S.count) outcomeMask).value direction = true)
    (selected : NodeSet S)
    (selected_outside_small : forall child, selected child = true -> w.small child = false)
    (selected_avoids_action : forall child, selected child = true -> query.action child = false)
    (selected_even : forall child, selected child = true -> (LinearSignal.rowPhase background child).value direction = false)
    (basis_matches : forall coordinate, cubeMask G (NodeSet.union query.action query.condition) coordinate = false ->
      ((LinearSignal.forestPhase small w.small).xor (maskPhase (pairRootCount G.binary + S.count) outcomeMask)).value
          (basisAssignment (pairRootCount G.binary + S.count) coordinate) =
        (selectedPhase (pairRootCount G.binary + S.count) S.count selected (LinearSignal.rowPhase background)).value
          (basisAssignment (pairRootCount G.binary + S.count) coordinate)) :
    ConditionalParityWitness w small background := by
  have matching : forall point, point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount G.binary + S.count)
        (cubeMask G (NodeSet.union query.action query.condition)) ->
      ((LinearSignal.forestPhase small w.small).xor (maskPhase (pairRootCount G.binary + S.count) outcomeMask)).value point =
        (selectedPhase (pairRootCount G.binary + S.count) S.count selected (LinearSignal.rowPhase background)).value point :=
    (HomogeneousPhase.agree_on_falseCylinder_iff_basis _ _ _).mpr basis_matches
  have selectedEven := selectedPhase_value_eq_false_of_even (pairRootCount G.binary + S.count) S.count
    selected (LinearSignal.rowPhase background) direction selected_even
  have smallOdd : (LinearSignal.forestPhase small w.small).value direction = true := by
    have combined := matching direction direction_member
    change Bool.xor ((LinearSignal.forestPhase small w.small).value direction)
      ((maskPhase (pairRootCount G.binary + S.count) outcomeMask).value direction) = _ at combined
    rw [outcome_odd, selectedEven] at combined
    cases parity : (LinearSignal.forestPhase small w.small).value direction with
    | false => rw [parity] at combined; cases combined
    | true => rfl
  exact {
    outcomeMask := outcomeMask
    outcomeMask_member := outcomeMask_member
    direction := direction
    direction_member := direction_member
    small_odd := smallOdd
    outcome_odd := outcome_odd
    selected := selected
    selected_outside_small := selected_outside_small
    selected_avoids_action := selected_avoids_action
    selected_even := selected_even
    matching := matching
  }

/-- Construct a parity witness from the actual local graph conservation
equations.  Free observed coordinates balance their own/parent coefficients;
every original reserved root balances its genuine incident contributions.
The supplied outcome mask remains a subset of the full original outcome.

The block embeddings exhaust the actual cube, so these finite equations
prove all the basis tests and hence the *whole* conditioning-cylinder
identity.  No mass comparison or equality at one sample is assumed.  An
arbitrary-path construction must still supply the masks, direction, selected
rows, and these graph conservation proofs; this adapter does not claim their
universal existence. -/
def ofConservation (outcomeMask : Cube G)
    (outcomeMask_member : outcomeMask ∈ outcomeMasks (pairRootCount G.binary + S.count) (cubeMask G query.outcome))
    (direction : Cube G)
    (direction_member : direction ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount G.binary + S.count)
      (cubeMask G (NodeSet.union query.action query.condition)))
    (outcome_odd : (maskPhase (pairRootCount G.binary + S.count) outcomeMask).value direction = true)
    (selected : NodeSet S)
    (selected_outside_small : forall child, selected child = true -> w.small child = false)
    (selected_avoids_action : forall child, selected child = true -> query.action child = false)
    (selected_even : forall child, selected child = true -> (LinearSignal.rowPhase background child).value direction = false)
    (observed_balance : forall coordinate, NodeSet.union query.action query.condition coordinate = false ->
      Bool.xor (LinearSignal.forestObservedCoefficient small w.small coordinate)
          (outcomeMask (Fin.natAdd (pairRootCount G.binary) coordinate)) =
        LinearSignal.selectedObservedCoefficient background selected coordinate)
    (root_balance : forall coordinate,
      Bool.xor (LinearSignal.forestRootCoefficient small w.small coordinate) (outcomeMask (coordinate.castAdd S.count)) =
        LinearSignal.selectedRootCoefficient background selected coordinate) :
    ConditionalParityWitness w small background := by
  apply ofBasis outcomeMask outcomeMask_member direction direction_member outcome_odd selected
    selected_outside_small selected_avoids_action selected_even
  intro coordinate free
  change Bool.xor ((LinearSignal.forestPhase small w.small).value (basisAssignment _ coordinate))
    ((maskPhase _ outcomeMask).value (basisAssignment _ coordinate)) = _
  by_cases earlier : coordinate.val < pairRootCount G.binary
  · let root : Fin (pairRootCount G.binary) := ⟨coordinate.val, earlier⟩
    have embedded : root.castAdd S.count = coordinate := Fin.ext rfl
    rw [← embedded, LinearSignal.forestPhase_root_basis, maskPhase_basis, LinearSignal.selectedPhase_root_basis]
    exact root_balance root
  · let child : Fin S.count := ⟨coordinate.val - pairRootCount G.binary, by
      have bound := coordinate.isLt
      omega⟩
    have embedded : Fin.natAdd (pairRootCount G.binary) child = coordinate := by
      apply Fin.ext
      dsimp only [child, Fin.natAdd]
      omega
    have freeChild : NodeSet.union query.action query.condition child = false := by
      have atChild := free
      rw [← embedded] at atChild
      change FiniteProduct.BooleanBlocks.rightBlock (pairRootCount G.binary) S.count
        (cubeMask G (NodeSet.union query.action query.condition)) child = false at atChild
      unfold cubeMask at atChild
      rw [FiniteProduct.BooleanBlocks.rightBlock_join] at atChild
      exact atChild
    rw [← embedded, LinearSignal.forestPhase_observed_basis, maskPhase_basis, LinearSignal.selectedPhase_observed_basis]
    exact observed_balance child freeChild

/-- The explicit direction and matching selection make the *complete*
original-outcome covariance positive.  Selected free-row amplitudes are
proved positive from the actual tables; other subset covariances remain
nonnegative and cannot cancel this strict contribution. -/
theorem covariance_positive (witness : ConditionalParityWitness w small background) :
    0 < cylinderCovarianceNumerator (pairRootCount G.binary + S.count) S.count
      (cubeMask G (NodeSet.union query.action query.condition)) (cubeMask G query.outcome)
      (backgroundCapacity w) (backgroundAmplitude w) (LinearSignal.rowPhase background)
      (LinearSignal.forestPhase small w.small) := by
  apply cylinderCovarianceNumerator_positive_of_selected_phase
    (pairRootCount G.binary + S.count) S.count
    (cubeMask G (NodeSet.union query.action query.condition)) (cubeMask G query.outcome)
    (backgroundCapacity w) (backgroundAmplitude w) (LinearSignal.rowPhase background)
    (LinearSignal.forestPhase small w.small)
    (backgroundAmplitude_nonneg w) (backgroundAmplitude_lt_capacity w)
    witness.outcomeMask witness.outcomeMask_member witness.direction witness.direction_member
    witness.small_odd witness.outcome_odd witness.selected witness.selected_even
  · intro child selected
    exact backgroundAmplitude_positive_of_free w child
      (witness.selected_outside_small child selected) (witness.selected_avoids_action child selected)
  · exact witness.matching

/-- The positive covariance is the actual normalized model response, after
the installed positive small coefficients are restored.  Both evidence-mass
changes are still present in this complete cross-product response. -/
theorem response_positive (witness : ConditionalParityWitness w small background) :
    0 < signedConditionalResponse w small background query.outcome query.condition :=
  signedConditionalResponse_positive_of_covariance w small background query.outcome query.condition
    witness.covariance_positive

end ConditionalParityWitness

/-! ## The all-false cell is literally a cell of the original query -/

private theorem binary_agreesOn_false (nodes : NodeSet S) (sample : S.binary.Assignment) :
    Kernel.agreesOn (S := S.binary) nodes (fun _ => false) sample = FiniteProduct.falseCylinder S.count nodes sample := by
  apply Bool.eq_iff_iff.mpr
  unfold Kernel.agreesOn
  rw [finAll_eq_true_iff, FiniteProduct.falseCylinder_eq_true_iff]
  constructor
  · intro consistent child selected
    have tested := consistent child
    simp only [selected, if_true] at tested
    exact of_decide_eq_true tested
  · intro consistent child
    cases selected : nodes child with
    | false => simp only [Bool.false_eq_true, if_false]
    | true => simp only [if_true, consistent child selected]; rfl

private theorem false_query_intervention (query : ConditionalKernelQuery S) :
    query.binary.operationKernel.intervention (fun _ => false) = falseActionTarget query.action := rfl

private theorem false_query_numeratorEvent (query : ConditionalKernelQuery S) :
    query.binary.operationKernel.numeratorEvent (fun _ => false) =
      FiniteProduct.falseCylinder S.count (NodeSet.union query.outcome query.condition) := by
  funext sample
  change (Kernel.agreesOn (S := S.binary) query.outcome (fun _ => false) sample &&
    Kernel.agreesOn (S := S.binary) query.condition (fun _ => false) sample) = _
  rw [binary_agreesOn_false, binary_agreesOn_false]
  exact (FiniteProduct.falseCylinder_union S.count query.outcome query.condition sample).symm

private theorem false_query_conditionEvent (query : ConditionalKernelQuery S) :
    query.binary.operationKernel.conditionEvent (fun _ => false) = FiniteProduct.falseCylinder S.count query.condition :=
  funext (fun sample => binary_agreesOn_false query.condition sample)

/-- Build compatible, fully positive original-alphabet models with equal
entire observed laws and different values of the unchanged original
conditional query.  The only supplied separation data are explicit finite
parities; the actual normalized gap, source cell and label lift are proved
internally.  No matched evidence denominator or probability-gap premise is
required, and arbitrary-path existence of the witness is not assumed. -/
noncomputable def conditionalCounterexampleOfParity
    (w : HedgeWitness G query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (small background : LinearSignal G) (witness : ConditionalParityWitness w small background) :
    ConditionalCounterexampleIn (GraphModelClass.positive G) query := by
  apply conditionalCounterexampleOfBackgroundChange (S := S) (G := G) (query := query)
    w rich small.signal background.signal (fun _ => false)
  rw [false_query_intervention, false_query_numeratorEvent, false_query_conditionEvent]
  intro balanced
  have zero : signedConditionalResponse w small background query.outcome query.condition = 0 :=
    Int.sub_eq_zero.mpr balanced
  have positive := witness.response_positive
  rw [zero] at positive
  omega

end HedgeChannelEnvironmentInstallation
end Causality
end Thesis
