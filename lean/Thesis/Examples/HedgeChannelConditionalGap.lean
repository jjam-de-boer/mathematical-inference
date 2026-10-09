import Thesis.CausalTransport.HedgeChannelConditionalGap
import Thesis.Examples.ConditionalCollider

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeChannelConditionalGap

open Probability HedgeChannelInstallation ConditionalColliderRegression

/-!
# An incoming collider channel with unequal conditioning marginals

Reuse the genuine failed query `P(U | do(A), R)` on `U -> R <- A`,
`A <-> R`.  Its small forest is the conditioned `R`, so the default outcome
flow admits no conditioning-marginal balance direction.  Here the small
channel instead reads the declared parent `U`.  Background rows ignore their
parents.  Both SCMs still have their original graph and complete common
observed law, by the general arbitrary-signal installation theorem.

The actual conditioning masses differ.  Nevertheless the two complete
projected changes give a nonzero normalized cell change, which separates
the actual conditional.  All computations below use only eight Boolean
observed assignments and two canonical terms on each side.  No augmented
response-function prior or complete exchange search is evaluated.

The Boolean source pair is kept visible.  The general unequal-denominator
cell lift then constructs a new positive pair on the original three-valued
signature.  Its all-second cell is the explicit recoding of the original
all-false source cell.  Full-label positivity and separation are derived
internally; the existing fixture's older collider countermodel is not used
as the source of this new original-query counterexample.
-/

private def smallSignal : ParentSignal signature :=
  fun child parents => if edge : signature.directed parent child = true then parents parent edge else false

private def backgroundSignal : ParentSignal signature := fun _ _ => false
private def reference : signature.binary.Assignment := fun _ => false
private def target := (binaryConditionalQuery query).operationKernel.intervention reference
private def jointEvent := (binaryConditionalQuery query).operationKernel.numeratorEvent reference
private def conditionEvent := (binaryConditionalQuery query).operationKernel.conditionEvent reference
private def parentMask : NodeSet signature := NodeSet.singleton parent

private instance : DecidableEq (Fin signature.count -> Option (Fin (channelCount witness))) :=
  FiniteProduct.assignmentDecidableEq signature.count (fun _ => Option (Fin (channelCount witness)))
    (fun _ => inferInstance)

private theorem target_at_seed : target witness.actionSeed = some false := by
  change (some false : Option Bool) = some false
  rfl

private theorem common_choices : commonChoicesUnder witness target =
    [backgroundChoice witness NodeSet.empty, backgroundChoice witness parentMask] := by decide +kernel

private theorem small_choices : rightFullChoicesUnder witness target =
    [fullChoice witness witness.small (smallChannel witness) NodeSet.empty,
      fullChoice witness witness.small (smallChannel witness) parentMask] := by decide +kernel

private def commonTerm (sample : signature.binary.Assignment) (mask : NodeSet signature) : Int :=
  ((PairRootChannels.prior graph.binary (channelCount witness)).den : Int) *
    HedgeChannelTable.choiceCoefficient (leftTables witness) target sample (backgroundChoice witness mask) *
    FiniteProbRecord.characterSign (signalPhase mask backgroundSignal sample)

private def smallTerm (sample : signature.binary.Assignment) (mask : NodeSet signature) : Int :=
  ((PairRootChannels.prior graph.binary (channelCount witness)).den : Int) *
    HedgeChannelTable.choiceCoefficient (rightTables witness) target sample
      (fullChoice witness witness.small (smallChannel witness) mask) *
    FiniteProbRecord.characterSign (Bool.xor (signalPhase witness.small smallSignal sample)
      (signalPhase mask backgroundSignal sample))

private def commonProjection (event : Event signature.binary.Assignment) : Int :=
  ((signature.binary.assignmentEnumeration.filter event).map
    (fun sample => commonTerm sample NodeSet.empty + commonTerm sample parentMask)).sum

private def changeProjection (event : Event signature.binary.Assignment) : Int :=
  ((signature.binary.assignmentEnumeration.filter event).map
    (fun sample => smallTerm sample NodeSet.empty + smallTerm sample parentMask)).sum

private theorem castMapSum {α : Type} (values : List α) (term : α -> Nat) :
    (((values.map term).sum : Nat) : Int) = (values.map (fun value => (term value : Int))).sum := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, Int.natCast_add, inductionHypothesis]

/-- Reduce the left mass through its verified complete background support,
not by enumerating private response functions.  The two displayed terms
include the empty background and the unacted outside parent. -/
private theorem commonProjection_eq (event : Event signature.binary.Assignment) :
    (HedgeChannelTable.eventNumerator graph (channelCount witness) (leftTables witness)
      (leftSignals witness rich smallSignal backgroundSignal) target event : Int) = commonProjection event := by
  unfold HedgeChannelTable.eventNumerator commonProjection
  rw [castMapSum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro sample _selected
  have evaluated := (HedgeChannelTable.integratedNumerator_expansion graph (channelCount witness)
    (leftTables witness) (leftSignals witness rich smallSignal backgroundSignal) target sample).trans
      (left_expandedIntegral_common_under witness rich smallSignal backgroundSignal target false
        target_at_seed sample)
  rw [common_choices] at evaluated
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.add_zero] at evaluated
  rw [left_commonTermIntegral_under witness rich smallSignal backgroundSignal target sample NodeSet.empty,
    left_commonTermIntegral_under witness rich smallSignal backgroundSignal target sample parentMask] at evaluated
  exact evaluated

/-- Recover the entire right-minus-left projection from the complete
permitted small-channel support.  Both canonical masks are kept, and each
actual integral is evaluated by the shared-incidence cancellation theorem. -/
private theorem changeProjection_eq (event : Event signature.binary.Assignment) :
    projectedEventChange witness smallSignal backgroundSignal target event = changeProjection event := by
  have parentOutside : NodeSet.Subset parentMask (outside witness.small) := by
    intro node selected
    have same := (NodeSet.singleton_eq_true_iff parent node).mp selected
    subst node
    decide +kernel
  unfold projectedEventChange changeProjection
  rw [small_choices]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.add_zero]
  apply congrArg List.sum
  apply List.map_congr_left
  intro sample _selected
  rw [right_fullTermIntegral_under witness smallSignal backgroundSignal target sample NodeSet.empty
      (by intro node selected; cases selected),
    right_fullTermIntegral_under witness smallSignal backgroundSignal target sample parentMask parentOutside]
  rfl

/-- Literal finite projections of the four verified symbolic sums.  The
conditioning change is genuinely nonzero; it is not discarded before the
normalization test. -/
theorem projected_mass_values :
    commonProjection jointEvent = 1207959552 ∧
    commonProjection conditionEvent = 2147483648 ∧
    changeProjection jointEvent = 18874368 ∧
    changeProjection conditionEvent = 4194304 := by decide +kernel

/-- The actual complete normalized cell change is nonzero even though
the evidence mass changes.  Only the four small projections above are
computed; the probability bridge is supplied by the general theorem. -/
theorem normalized_change_nonzero :
    normalizedCellChange witness rich smallSignal backgroundSignal reference ≠ 0 := by
  change projectedEventChange witness smallSignal backgroundSignal target jointEvent *
      (HedgeChannelTable.eventNumerator graph (channelCount witness) (leftTables witness)
        (leftSignals witness rich smallSignal backgroundSignal) target conditionEvent : Int) -
    (HedgeChannelTable.eventNumerator graph (channelCount witness) (leftTables witness)
      (leftSignals witness rich smallSignal backgroundSignal) target jointEvent : Int) *
      projectedEventChange witness smallSignal backgroundSignal target conditionEvent ≠ 0
  rw [changeProjection_eq, changeProjection_eq, commonProjection_eq, commonProjection_eq,
    projected_mass_values.1, projected_mass_values.2.1,
    projected_mass_values.2.2.1, projected_mass_values.2.2.2]
  decide

/-- The same installed pair really has different conditioning event
probabilities.  Thus this is not an instance of the matched-marginal
construction with its equality proof omitted from the presentation. -/
theorem actual_conditioning_marginals_differ :
    ¬ QProb.Equiv ((leftModel witness rich smallSignal backgroundSignal).interventionalValue target conditionEvent)
      ((rightModel witness smallSignal backgroundSignal).interventionalValue target conditionEvent) := by
  apply HedgeChannelTable.model_interventional_event_not_equiv graph (channelCount witness)
    (leftTables witness) (rightTables witness)
    (leftSignals witness rich smallSignal backgroundSignal) (rightSignals witness smallSignal backgroundSignal)
    (capacities_equal witness) target conditionEvent
  intro same
  have difference := eventNumerator_change witness rich smallSignal backgroundSignal target false
    target_at_seed conditionEvent
  rw [← same, changeProjection_eq, projected_mass_values.2.2.2] at difference
  omega

/-- A genuine positive counterexample for the unchanged node sets on the
Boolean interpretation of the supplied signature.  Complete observational
equality and compatibility of these very models come from the installation,
not from an assumed source countermodel or a changed conditioning query. -/
noncomputable def binary_positive_counterexample :
    ConditionalCounterexampleIn (GraphModelClass.positive graph.binary) (binaryConditionalQuery query) :=
  binaryConditionalCounterexampleOfNormalizedCellChange witness rich smallSignal backgroundSignal reference
    normalized_change_nonzero

theorem binary_query_not_identifiable :
    ¬ (GraphModelClass.positive graph.binary).conditionalIdentifiable (binaryConditionalQuery query) :=
  binary_positive_counterexample.not_identifiable

/-- The normalized channel gap now gives a genuine original-three-label
positive counterexample.  Its fixed known source reference is transported
directly; no search through the installed source-model probabilities runs. -/
noncomputable def original_positive_counterexample :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  conditionalCounterexampleOfNormalizedCellChange witness rich smallSignal backgroundSignal reference
    normalized_change_nonzero

/-- The new full-alphabet pair refutes the unchanged original conditional,
independently of the fixture's older carrier/collider countermodel. -/
theorem original_query_not_identifiable :
    ¬ (GraphModelClass.positive graph).conditionalIdentifiable query :=
  original_positive_counterexample.not_identifiable

/-- Both final evidence probabilities still differ at the transported
original-label cell.  The full-label lift compares each to its own source
mass; it does not equalize or replace the conditioning denominator. -/
theorem original_conditioning_marginals_differ :
    ¬ QProb.Equiv
      ((query.operationKernel.distribution original_positive_counterexample.left rich.second).probVal
        (Kernel.agreesOn query.condition rich.second))
      ((query.operationKernel.distribution original_positive_counterexample.right rich.second).probVal
        (Kernel.agreesOn query.condition rich.second)) := by
  intro same
  have source := QProb.equiv_trans
    (QProb.equiv_symm (ObservedValueRefinement.cellModel_cylinderValue query rich
      (leftModel witness rich smallSignal backgroundSignal) reference query.condition))
    (QProb.equiv_trans same (ObservedValueRefinement.cellModel_cylinderValue query rich
      (rightModel witness smallSignal backgroundSignal) reference query.condition))
  have active : finAny signature.binary.count query.action = true := by decide +kernel
  apply actual_conditioning_marginals_differ
  simpa only [Kernel.distribution, Kernel.hasAction, ConditionalKernelQuery.operationKernel,
    ConditionalKernelQuery.binary, active, if_true] using source

/-- A mixed Boolean reference is sent to bit one at every coordinate, not
only at the conditioner.  This small recoding check protects the arbitrary-
reference case of the general full-alphabet cell transport. -/
theorem mixed_reference_recoding :
    BinaryRecoding.assignment (S := signature)
      (ObservedValueRefinement.cellMask (S := signature)
        (fun node : Fin signature.count => decide (node = parent)))
      (fun node : Fin signature.count => decide (node = parent)) = (fun _ => true) := by
  funext node
  change Bool.xor (decide (node = parent)) (Bool.not (decide (node = parent))) = true
  cases decide (node = parent) <;> rfl

end HedgeChannelConditionalGap
end Examples
end Causality
end Thesis
