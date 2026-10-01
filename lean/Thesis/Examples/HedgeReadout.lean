import Thesis.CausalTransport.HedgeReadout
import Thesis.Examples.KernelFailureExtraction

namespace Thesis
namespace Causality
namespace Examples
namespace HedgePrivateReadout

open Probability
open CurrentKernelFailureExtraction

/-!
# A positive original-outcome countermodel realized by private readout noise

The graph is `X → R → Y` with `X ↔ R`, but no bidirected edge at `Y`.
Corrected joint ID fails on `P(Y | do(X))`.  Its extracted hedge has common
root `R`, which is not the queried outcome.  Merely returning the existing
root-parity countermodel would therefore prove the wrong query.

We add one genuinely private biased source at `Y`, install the same noisy
readout in both positive carrier models, and prove all three countermodel
obligations: compatible positive membership, equality of the complete
observational law, and separation of the original outcome's interventional
kernel.  The signal-to-SCM theorem, not a supplied observed-law premise or a
numerical guess, transports the existing root gap through this real edge.

The construction does not claim unrestricted routing is finished.  It tests
the semantic primitive needed by a finite routed construction, including
the crucial fresh-noise product law and full observational positivity.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def signature := chainSignature 3
def graph := partitionGraph signature (fun node => decide (node.val = 2))
def actionNode : Fin signature.count := ⟨0, by decide⟩
def rootNode : Fin signature.count := ⟨1, by decide⟩
def outcomeNode : Fin signature.count := ⟨2, by decide⟩
def forestHost : NodeSet signature := fun node => decide (node.val < 2)
def rootMask : NodeSet signature := NodeSet.singleton rootNode

def query : JointKernelQuery signature where
  outcome := NodeSet.singleton outcomeNode
  action := NodeSet.singleton actionNode
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => false
  second := fun _ => true
  first_enumerated := by intro _; change false ∈ [false, true]; decide +kernel
  second_enumerated := by intro _; change true ∈ [false, true]; decide +kernel
  different := fun _ => Bool.false_ne_true

private def computedFailure : IdentificationFail signature :=
  match identifyJointKernel graph query with
  | .failed fail => fail
  | _ => ⟨NodeSet.empty, NodeSet.empty⟩

theorem query_failed : identifyJointKernel graph query = .failed ⟨forestHost, rootMask⟩ := by
  have failed : identifyJointKernel graph query = .failed computedFailure := rfl
  have large : computedFailure.remaining = forestHost :=
    (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)
  have small : computedFailure.free = rootMask :=
    (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)
  have coordinates : computedFailure = ⟨forestHost, rootMask⟩ := by
    cases record : computedFailure with
    | mk remaining free =>
        rw [record] at large small
        cases large
        cases small
        rfl
  exact failed.trans (congrArg IdentificationOutcome.failed coordinates)

noncomputable def extraction := identifyJointKernelFailedHedge query query_failed

private theorem root_only (node : Fin signature.count) (selected : extraction.witness.roots node = true) :
    node = rootNode := by
  have smallEqual : extraction.witness.small = rootMask := extraction.small_eq
  have small := ((extraction.witness.small_forest.roots_exact node).mp selected).1
  rw [smallEqual] at small
  exact of_decide_eq_true small

theorem extracted_roots : extraction.witness.roots = rootMask := by
  have selectedRoot : extraction.witness.roots rootNode = true := by
    rw [← root_only extraction.witness.actionRoot extraction.witness.actionRoot_in_roots]
    exact extraction.witness.actionRoot_in_roots
  funext node
  by_cases same : node = rootNode
  · subst node
    rw [selectedRoot]
    simp [rootMask, NodeSet.singleton]
  · cases selected : extraction.witness.roots node with
    | false => simp [rootMask, NodeSet.singleton, same]
    | true => exact False.elim (same (root_only node selected))

theorem outcome_not_a_root : extraction.witness.roots outcomeNode = false := by
  rw [extracted_roots]
  decide +kernel

theorem outcome_kept_child_none : extraction.witness.child outcomeNode = none := by
  have largeEqual : extraction.witness.large = forestHost := extraction.large_eq
  cases selected : extraction.witness.child outcomeNode with
  | none => rfl
  | some child =>
      have selectedOutcome := (extraction.witness.large_forest.child_edge outcomeNode child selected).1
      rw [largeEqual] at selectedOutcome
      have outside : forestHost outcomeNode = false := by decide +kernel
      rw [outside] at selectedOutcome
      contradiction

/-! ## The actual independent source and observable parent readout -/

def noise : FiniteProbRecord Bool := ⟨[(false, 2), (true, 1)], 3, by decide, rfl⟩

theorem noise_positive (bit : Bool) : noise.EventPositive (FiniteProbRecord.singletonEvent bit) := by
  cases bit <;> decide +kernel

theorem noise_bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
    FiniteProbRecord.eventMass noise.atoms id + 1 := by decide +kernel

def parentSignal (parents : signature.ParentValues outcomeNode) : Bool :=
  hedgeIsSecond rich rootNode (parents rootNode (by decide +kernel))

theorem readout_signal_is_root_parity : hedgeReadoutSignal rich outcomeNode false parentSignal =
    hedgeRootParityEvent rich extraction.witness.roots := by
  funext sample
  rw [extracted_roots]
  have members : NodeSet.members rootMask = [rootNode] := by decide +kernel
  simp only [hedgeRootParityEvent, hedgeNodeXor, members, List.foldl_cons, List.foldl_nil,
    Bool.false_xor]
  simp only [hedgeReadoutSignal, parentSignal, Bool.false_xor, Bool.false_eq_true,
    ↓reduceIte]

noncomputable def left :=
  (extraction.witness.largeCarrierDefectParityModel rich).withHedgeReadout rich outcomeNode noise false parentSignal
noncomputable def right :=
  (extraction.witness.smallCarrierDefectParityModel rich).withHedgeReadout rich outcomeNode noise false parentSignal

theorem left_compatible : Compatible left graph :=
  FiniteLatentSCM.withHedgeReadout_compatible _
    (extraction.witness.largeCarrierDefectParityModel_compatible rich) rich outcomeNode noise false parentSignal

theorem right_compatible : Compatible right graph :=
  FiniteLatentSCM.withHedgeReadout_compatible _
    (extraction.witness.smallCarrierDefectParityModel_compatible rich) rich outcomeNode noise false parentSignal

theorem left_positive : ObservationallyPositive left :=
  FiniteLatentSCM.withHedgeReadout_positive _
    (extraction.witness.largeCarrierDefectParityModel_positive rich) rich outcomeNode noise noise_positive
    false parentSignal

theorem right_positive : ObservationallyPositive right :=
  FiniteLatentSCM.withHedgeReadout_positive _
    (extraction.witness.smallCarrierDefectParityModel_positive rich) rich outcomeNode noise noise_positive
    false parentSignal

theorem observationally_equal : ObservationallyEquivalent left right :=
  extraction.witness.carrierDefectParityModels_withHedgeReadout_observationally_equivalent
    rich outcomeNode outcome_kept_child_none noise false parentSignal

theorem original_outcome_signal_separated : Not (QProb.Equiv
    (left.interventionalValue (hedgeDoSecond rich query.action)
      (fun sample => hedgeIsSecond rich outcomeNode (sample outcomeNode)))
    (right.interventionalValue (hedgeDoSecond rich query.action)
      (fun sample => hedgeIsSecond rich outcomeNode (sample outcomeNode)))) := by
  apply FiniteLatentSCM.withHedgeReadout_signal_not_equiv _ _ rich outcomeNode noise false parentSignal
    (extraction.witness.largeCarrierDefectParityModel_otherMechanismsIgnore rich outcomeNode outcome_kept_child_none)
    (extraction.witness.smallCarrierDefectParityModel_otherMechanismsIgnore rich outcomeNode outcome_kept_child_none)
    (hedgeDoSecond rich query.action) (by decide +kernel) 1 (by decide) noise_bias
  rw [readout_signal_is_root_parity]
  exact extraction.witness.carrierDefectParityModels_rootParity_not_equiv_doSecond rich

/-! ## Restore the distributional query, not merely a root event -/

def outcomeEventQuery : InterventionalQuery signature where
  intervention := hedgeDoSecondIntervention rich query.action
  outcomeNodes := query.outcome
  action_outcome_disjoint := by
    rw [hedgeDoSecondIntervention_targets]
    exact query.action_outcome_disjoint
  event := fun sample => hedgeIsSecond rich outcomeNode (sample outcomeNode)
  event_local := by
    intro first second agree
    exact congrArg (hedgeIsSecond rich outcomeNode) (agree outcomeNode (by decide +kernel))

theorem outcomeEventQuery_kernel : outcomeEventQuery.kernelQuery = query := by
  simp only [outcomeEventQuery, InterventionalQuery.kernelQuery, hedgeDoSecondIntervention_targets]

private theorem outcomeEventQuery_value (model : ExactModel signature) :
    outcomeEventQuery.value model = model.interventionalValue (hedgeDoSecond rich query.action)
      (fun sample => hedgeIsSecond rich outcomeNode (sample outcomeNode)) := by
  have active : finAny signature.count query.action = true := by decide +kernel
  simp only [outcomeEventQuery, InterventionalQuery.value, InterventionalQuery.distribution,
    hedgeDoSecondIntervention_targets, active, ↓reduceIte]
  rfl

/-- All countermodel fields refer to the original `Y` query.  The latent
source is genuinely private, and both complete observational laws are
strictly positive; no root-outcome substitution remains in the result. -/
noncomputable def originalCounterexample : CounterexampleIn (GraphModelClass.positive graph) query where
  left := left
  right := right
  left_mem := ⟨left_compatible, left_positive⟩
  right_mem := ⟨right_compatible, right_positive⟩
  observationally_equal := observationally_equal
  query_separated := by
    have separated : Not (QProb.Equiv (outcomeEventQuery.value left) (outcomeEventQuery.value right)) := by
      simpa only [outcomeEventQuery_value] using original_outcome_signal_separated
    have kernel := outcomeEventQuery.not_kernelValueEquivalent_of_not_value left right separated
    simpa only [outcomeEventQuery_kernel] using kernel

theorem original_query_not_identifiable : Not ((GraphModelClass.positive graph).identifiable query) :=
  originalCounterexample.not_identifiable

end HedgePrivateReadout
end Examples
end Causality
end Thesis
