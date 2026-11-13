import Thesis.CausalTransport.HedgeInterventionalProbability
import Thesis.Examples.HedgeInterventionalSupport
import Thesis.Examples.KernelFailureExtraction

namespace Thesis
namespace Causality
namespace Examples

open Probability

/-!
# Weighted defect independence in actual extracted hedge models

The first check retains the existing two-root merging hedge and its original
action.  Every observed event has the same probability in either normalized
defect stratum as in the unconditional large carrier.  No finite count,
balancing vertex, fair-prior replacement, or distribution equation is supplied.

The second fixture has three-value observed alphabets and a composite action
on the first two vertices of a confounded three-node directed chain.  Its
actual corrected-ID failure supplies the hedge.  We intervene with label two,
which is neither distinguished parity label, and test the complete all-two
target.  Both defect slices are positive; their natural masses have a strict
two-to-one bias even though their normalized observed probabilities agree.
This distinguishes the weighted theorem from an incorrect claim that the
unnormalized slice masses themselves coincide.

Neither regression asserts a large/small denominator comparison or the full
completeness theorem.  Both exercise the existing SCMs and their literal prior.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace HedgeWeightedMergedIntervention

open HedgeMergedReadout

/-- The extracted two-root hedge needs no manual balance choice for its
original action.  The comparison holds for arbitrary full-assignment events,
not merely root parity or a particular complete target. -/
theorem original_action_defect_independent (event : Event signature.Assignment) (defect : Bool) :
    QProb.Equiv
      (((extraction.witness.largeCarrierDefectParityModel rich).prior.conditionOn
        (hedgeDefectStratum graph defect) (hedgeDefectPrior_stratum_positive graph defect)).probVal
        (fun unit => event ((extraction.witness.largeCarrierDefectParityModel rich).evalUnder
          (hedgeDoSecond rich query.action) unit)))
      ((extraction.witness.largeCarrierDefectParityModel rich).prior.probVal
        (fun unit => event ((extraction.witness.largeCarrierDefectParityModel rich).evalUnder
          (hedgeDoSecond rich query.action) unit))) :=
  extraction.witness.largeCarrierDefectParityModel_doSecond_conditionOn_probVal_equiv rich event defect

end HedgeWeightedMergedIntervention

namespace HedgeWeightedTernaryIntervention

open CurrentKernelFailureExtraction

/-- Three observed values at each vertex; the third is a real carrier
background label and is not silently collapsed to the two-value bit encoding. -/
def signature : ObservedSignature where
  count := 3
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide (child.val = parent.val + 1)
  directed_earlier := by
    intro parent child edge
    have next := of_decide_eq_true edge
    omega

def graph := partitionGraph signature (fun _ => false)
def balance : Fin signature.count := ⟨0, by decide⟩
def outcome : Fin signature.count := ⟨2, by decide⟩

def query : JointKernelQuery signature where
  outcome := NodeSet.singleton outcome
  action := fun node => decide (node.val < 2)
  action_outcome_disjoint := by
    apply (NodeSet.disjointBool_eq_true_iff _ _).mp
    decide +kernel

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => ⟨0, by decide⟩
  second := fun _ => ⟨1, by decide⟩
  first_enumerated := fun _ => List.mem_finRange _
  second_enumerated := fun _ => List.mem_finRange _
  different := fun _ => (by decide : (⟨0, by decide⟩ : Fin 3) ≠ ⟨1, by decide⟩)

private def computedFailure : IdentificationFail signature :=
  match identifyJointKernel graph query with
  | .failed fail => fail
  | _ => ⟨NodeSet.empty, NodeSet.empty⟩

/-- Alphabet enlargement does not replace the actual algorithmic failure
by a hand-built forest.  Both exact failure coordinates are checked with the
constructive finite node-set equality test. -/
theorem query_failed : identifyJointKernel graph query = .failed ⟨NodeSet.full, query.outcome⟩ := by
  have failed : identifyJointKernel graph query = .failed computedFailure := rfl
  have large : computedFailure.remaining = NodeSet.full :=
    (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)
  have small : computedFailure.free = query.outcome :=
    (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)
  have coordinates : computedFailure = ⟨NodeSet.full, query.outcome⟩ := by
    cases record : computedFailure with
    | mk remaining free =>
        rw [record] at large small
        cases large
        cases small
        rfl
  exact failed.trans (congrArg IdentificationOutcome.failed coordinates)

noncomputable def extraction := identifyJointKernelFailedHedge query query_failed

private theorem balance_inside : extraction.witness.large balance = true := by
  rw [extraction.large_eq]
  rfl

def target : signature.Assignment := fun _ => ⟨2, by decide⟩

/-- Both action coordinates are set to the third label.  The theorem below
therefore exercises arbitrary intervention values, not only `doSecond`. -/
def intervention (node : Fin signature.count) : Option (signature.Value node) :=
  if query.action node then some (target node) else none

private theorem balance_fixed : intervention balance ≠ none := Option.some_ne_none _

private theorem target_consistent : forall node value, intervention node = some value -> target node = value := by
  intro node value fixed
  cases selected : query.action node with
  | false =>
      simp only [intervention, selected, Bool.false_eq_true, if_false] at fixed
      cases fixed
  | true =>
      simp only [intervention, selected, if_true] at fixed
      exact Option.some.inj fixed

def targetEvent : Event signature.Assignment := FiniteProbRecord.singletonEvent target

/-- The inspected target's nonbinary value is genuinely different from
both parity labels, including at the queried outcome. -/
theorem target_outside_parity_labels :
    target outcome ≠ rich.first outcome ∧ target outcome ≠ rich.second outcome := by decide +kernel

/-- Strict positivity in each actual fixed-defect slice uses the general
full-alphabet interventional section, with no root-parity admissibility test. -/
theorem target_slice_positive (defect : Bool) :
    (extraction.witness.largeCarrierDefectParityModel rich).prior.EventPositive
      (fun unit => hedgeDefectStratum graph defect unit &&
        targetEvent ((extraction.witness.largeCarrierDefectParityModel rich).evalUnder intervention unit)) :=
  extraction.witness.largeCarrierDefectParityModel_interventional_target_defect_positive rich
    balance balance_inside intervention balance_fixed target target_consistent defect

/-- Numerators retain the original bias.  In particular this positive event
does not have equal raw masses in the two defect strata. -/
theorem target_slice_mass_ratio :
    FiniteProbRecord.eventMass (extraction.witness.largeCarrierDefectParityModel rich).prior.atoms
        (fun unit => hedgeDefectStratum graph false unit &&
          targetEvent ((extraction.witness.largeCarrierDefectParityModel rich).evalUnder intervention unit)) =
      2 * FiniteProbRecord.eventMass (extraction.witness.largeCarrierDefectParityModel rich).prior.atoms
        (fun unit => hedgeDefectStratum graph true unit &&
          targetEvent ((extraction.witness.largeCarrierDefectParityModel rich).evalUnder intervention unit)) :=
  extraction.witness.largeCarrierDefectParityModel_interventional_eventMass_strata_eq rich
    balance balance_inside intervention balance_fixed targetEvent

theorem target_slice_masses_strictly_differ :
    FiniteProbRecord.eventMass (extraction.witness.largeCarrierDefectParityModel rich).prior.atoms
        (fun unit => hedgeDefectStratum graph true unit &&
          targetEvent ((extraction.witness.largeCarrierDefectParityModel rich).evalUnder intervention unit)) <
      FiniteProbRecord.eventMass (extraction.witness.largeCarrierDefectParityModel rich).prior.atoms
        (fun unit => hedgeDefectStratum graph false unit &&
          targetEvent ((extraction.witness.largeCarrierDefectParityModel rich).evalUnder intervention unit)) := by
  have positive := target_slice_positive true
  change 0 < FiniteProbRecord.eventMass _ _ at positive
  rw [target_slice_mass_ratio]
  omega

/-- After normalization, those differently weighted slices give the same
observed target probability as the original unconditional biased prior. -/
theorem target_probability_defect_independent (defect : Bool) :
    QProb.Equiv
      (((extraction.witness.largeCarrierDefectParityModel rich).prior.conditionOn
        (hedgeDefectStratum graph defect) (hedgeDefectPrior_stratum_positive graph defect)).probVal
        (fun unit => targetEvent ((extraction.witness.largeCarrierDefectParityModel rich).evalUnder intervention unit)))
      ((extraction.witness.largeCarrierDefectParityModel rich).prior.probVal
        (fun unit => targetEvent ((extraction.witness.largeCarrierDefectParityModel rich).evalUnder intervention unit))) :=
  extraction.witness.largeCarrierDefectParityModel_interventional_conditionOn_probVal_equiv rich
    balance balance_inside intervention balance_fixed targetEvent defect

end HedgeWeightedTernaryIntervention
end Examples
end Causality
end Thesis
