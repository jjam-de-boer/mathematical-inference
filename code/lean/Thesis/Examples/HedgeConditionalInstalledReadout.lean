import Thesis.Examples.HedgeConditionalCompensatedReadout

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeConditionalInstalledReentry

open Probability
open HedgeConditionalProtectedReentry
  (signature graph actionNode firstRoot outsideNode internalNode outcomeNode rich)

/-!
# An installed responding conditioner with another root still requiring routing

Reuse the six-vertex, three-value graph from the protected-conditioner example,
but ask `P(Y | do(A), B)` rather than conditioning on the outer-only `C`.
The common roots are still `R,Y`.  `R` reaches the requested numerator through
`R → E → B`, and canonical routing stops at the conditioner `B`.

`B` is an installed small-forest row with an original kept child `Y`; its
value is not protected by mechanism closure.  Moreover, `R` is not in the
numerator `{Y,B}`, so the earlier all-roots-in-numerator conditional
constructor does not apply either.  The queried common root `Y` is unused
by the composed flow.  Omitting its equation makes the actual conditioning
marginals agree by weighted partial-incidence comparison, while the same
positive compensated pair separates the numerator.

The forests are retargeted explicitly without claiming that the failure
extractor chooses these exact subgraphs.  Actual irreducibility and engine
failures are checked separately.  No enumeration of the augmented latent
prior, assumed countermodel, or Boolean-only observed alphabet is used.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def query : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton outcomeNode
  action := NodeSet.singleton actionNode
  condition := NodeSet.singleton internalNode
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  action_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

private theorem roots_reach : forall root, HedgeConditionalProtectedReentry.witness.roots root = true ->
    Exists fun outcome => query.jointNumerator.outcome outcome = true ∧
      DirectedReachableBy signature (fun parent child =>
        mutilatedDirected signature query.action parent child = true) root outcome := by
  intro root selected
  have onlyRoots : forall node : Fin signature.count,
      HedgeConditionalProtectedReentry.witness.roots node = true -> node = firstRoot ∨ node = outcomeNode := by decide +kernel
  refine ⟨outcomeNode, by decide +kernel, ?_⟩
  cases onlyRoots root selected with
  | inl same =>
      subst root
      exact .tail (.tail (.tail (.refl firstRoot)
        (by decide +kernel : mutilatedDirected signature query.action firstRoot outsideNode = true))
        (by decide +kernel : mutilatedDirected signature query.action outsideNode internalNode = true))
        (by decide +kernel : mutilatedDirected signature query.action internalNode outcomeNode = true)
  | inr same => subst root; exact .refl outcomeNode

noncomputable def witness : HedgeWitness graph query.jointNumerator :=
  HedgeConditionalProtectedReentry.witness.retargetQuery query.jointNumerator
    (by decide +kernel) HedgeConditionalProtectedReentry.witness.small_avoids_intervention roots_reach

private theorem allowed : forall node, witness.rootReadoutNodes node = true ->
    witness.small node = true ∨ witness.large node = false := by decide +kernel

private theorem root_in_outcome : witness.roots outcomeNode = true := by decide +kernel

private theorem queried_root_unused : witness.largeOutcomeFlowSuccessor outcomeNode = none :=
  witness.largeOutcomeFlowSuccessor_none_of_root_in_outcome outcomeNode root_in_outcome (by decide +kernel)

private theorem roots_meet_outcome : NodeSet.meetsBool witness.roots query.outcome = true := by decide +kernel

/-- The conditioner is genuinely installed and is not a kept sink.  Its
old outgoing contribution must be compensated at the later outcome row. -/
theorem conditioner_is_installed_responding : witness.small internalNode = true ∧
    witness.smallOutcomeFlowNodes internalNode = true ∧ witness.carrierFlowProtectedNodes internalNode = false ∧
      witness.child internalNode = some outcomeNode := by decide +kernel

/-- The denominator cannot use the protected-coordinate constructor. -/
theorem condition_not_protected : Not (NodeSet.Subset query.condition witness.carrierFlowProtectedNodes) := by
  intro conditionProtected
  have selected := conditionProtected internalNode (by decide +kernel)
  rw [conditioner_is_installed_responding.2.2.1] at selected
  cases selected

/-- Root contact is strictly weaker than covering every common root with
the numerator: `R` is still transported along a genuine outside route. -/
theorem roots_not_subset_numerator : Not (NodeSet.Subset witness.roots query.jointNumerator.outcome) := by
  intro covered
  have selected := covered firstRoot (by decide +kernel)
  have omitted : query.jointNumerator.outcome firstRoot = false := by decide +kernel
  rw [omitted] at selected
  cases selected

noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  witness.positiveConditionalCounterexampleOfCarrierFlowOfRootsMeetOutcome rich allowed roots_meet_outcome

/-- Full conditioning-kernel equality in these exact counterexample
endpoints, not merely in the original unmodified carrier pair. -/
theorem denominator_matches : query.jointDenominator.ValueEquivalent counterexample.left counterexample.right :=
  witness.carrierDefectParityModels_carrierFlowReadoutPlan_valueEquivalent_of_rootOmitted rich
    (fun _node => FiniteProbRecord.biasedFlip 1 1 (by decide)) outcomeNode root_in_outcome queried_root_unused
    query.jointDenominator (by decide +kernel)

theorem query_not_identifiable : Not ((GraphModelClass.positive graph).conditionalIdentifiable query) :=
  counterexample.not_identifiable

/-- The same installed-coordinate comparison also exercises the empty-
action observational branch of the joint-kernel theorem. -/
def observationalConditioner : JointKernelQuery signature where
  outcome := query.condition
  action := NodeSet.empty
  action_outcome_disjoint := (NodeSet.disjointBool_eq_true_iff _ _).mp (by decide +kernel)

theorem observational_conditioner_matches : observationalConditioner.ValueEquivalent counterexample.left counterexample.right :=
  witness.carrierDefectParityModels_carrierFlowReadoutPlan_valueEquivalent_of_rootOmitted rich
    (fun _node => FiniteProbRecord.biasedFlip 1 1 (by decide)) outcomeNode root_in_outcome queried_root_unused
    observationalConditioner (by decide +kernel)

private def failed (result : IdentificationOutcome signature) : Bool :=
  match result with
  | .failed _ => true
  | _ => false

theorem no_exchange : (conditionalExchangeStep? graph query).isNone = true := by decide +kernel

theorem joint_program_failed : failed (identifyJointKernel graph query.jointNumerator) = true := by decide +kernel

theorem conditional_program_failed : failed (identifyConditionalKernel graph query) = true := by decide +kernel

end HedgeConditionalInstalledReentry
end Examples
end Causality
end Thesis
