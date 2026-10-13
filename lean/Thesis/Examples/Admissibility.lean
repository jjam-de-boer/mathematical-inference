import Thesis.Causality.Admissibility
import Thesis.Examples.LocalSupportIdentification
import Thesis.Examples.ConditionalPromotionSupport

namespace Thesis
namespace Causality
namespace Examples
namespace ZeroCellAdmissibility

open Probability ZeroCellChain ZeroCellLocalIdentification

/-!
# Primitive admissibility genuinely permits observational zeros

The existing finite SCM has `X = false` and an independent unbiased `Y`.
The supported action `X = false` is admissible although the observed law
contains zeros.  Its absent action `X = true` is rejected by the primitive
action test; the test is sufficient overlap, not a claim that every rejected
action in every graph is unidentifiable.

The conditioning regression has a positive intervened `Y = true` cylinder.
Promotion preserves that actual conditioner support.  These checks exercise
the primitive admissibility definitions and their general proofs; they do
not replace the needed recursive ID/IDC support-propagation theorem by a
hand-picked family of numerical examples.
-/

theorem action_has_no_parents : signature.actionParents query.action = NodeSet.empty := by
  funext node
  unfold ObservedSignature.actionParents
  have noChildren : finAny signature.count
      (fun child => query.action child && signature.directed node child) = false := by
    change finAny 2 (fun _child => _ && false) = false
    simp only [Bool.and_false]
    rfl
  rw [noChildren, Bool.and_false]
  rfl

/-- The admissibility check retains only the supported action cylinder.
It does not demand a positive complete observed law. -/
theorem supported_action_admissible :
    ObservationalActionAdmissibleAt model query.action supportedReference := by
  change ObservationalCylinderPositiveAt model
    (NodeSet.union query.action (signature.actionParents query.action)) supportedReference
  rw [action_has_no_parents, NodeSet.union_empty_right]
  exact action_cylinder_positive

/-- The general no-parent theorem supplies every supported parent context,
without deciding a proposition quantified over arbitrary assignments. -/
theorem supported_action_admissible_on_parent_support :
    ObservationalActionAdmissibleOnParentSupport model query.action supportedReference :=
  ObservationalActionAdmissibleOnParentSupport.of_noParents action_has_no_parents supported_action_admissible

noncomputable def supported_action_positive_value :
    ProbabilityResult.PositiveSupportedValue
      ((ProbabilityTerm.kernel ⟨query.action, NodeSet.empty, signature.actionParents query.action⟩).denote
        model supportedReference) :=
  supported_action_admissible.positiveValue

theorem unsupported_action_not_admissible :
    ¬ ObservationalActionAdmissibleAt model query.action reference := by
  intro admissible
  change ObservationalCylinderPositiveAt model
    (NodeSet.union query.action (signature.actionParents query.action)) reference at admissible
  rw [action_has_no_parents, NodeSet.union_empty_right] at admissible
  have zero : (model.observationalDist.probVal (Kernel.agreesOn query.action reference)).num = 0 := by
    decide +kernel
  change 0 < (model.observationalDist.probVal (Kernel.agreesOn query.action reference)).num at admissible
  rw [zero] at admissible
  exact Nat.not_lt_zero _ admissible

/-- This is a genuine extension beyond the positive class, not a disguised
positive model passed through differently named hypotheses. -/
theorem model_not_positive : ¬ ObservationallyPositive model :=
  model_not_observationally_positive

def conditionedKernel : Kernel signature :=
  ⟨NodeSet.empty, query.action, NodeSet.singleton y⟩

theorem original_condition_admissible :
    Kernel.ConditioningAdmissibleAt model conditionedKernel supportedReference := by
  unfold Kernel.ConditioningAdmissibleAt
  decide +kernel

/-- The intrinsic block-promotion theorem supplies the new conditioner's
positivity.  Observational admissibility of the combined action is not
silently deduced from this causal-support theorem. -/
theorem promoted_condition_admissible :
    Kernel.ConditioningAdmissibleAt model
      ⟨NodeSet.empty, NodeSet.union query.action (NodeSet.singleton y), NodeSet.empty⟩ supportedReference :=
  Kernel.ConditioningAdmissibleAt.promoteCondition
    (by simpa only [NodeSet.union_empty_right] using original_condition_admissible)

end ZeroCellAdmissibility

namespace IntrinsicComponentAdmissibility

open Probability GuardedKernelZeroRegression NullActionPromotionSupport

/-!
## A supported host at a null factual action

In the existing original hidden DAG, the factual action `X = true` is null,
but `P(Y | do(X = true), M = true)` is supported.  The intrinsic component
support helper promotes the earlier outside mediator and permits the later
outside `Z` action without demanding a factual `X,M` cylinder.

The selected singleton is used only to test the general intrinsic support
lemma.  No bidirected closure or whole-component identification derivation
is claimed for this selection.  Graph closure remains a separate input of
the actual component compiler.
-/

def remaining : NodeSet signature := NodeSet.diff NodeSet.full query.action
def component : NodeSet signature := NodeSet.singleton y

theorem component_subset : NodeSet.Subset component remaining :=
  (NodeSet.subsetBool_eq_true_iff component remaining).mp (by decide +kernel)

theorem host_condition_eq : chainCondition remaining y = query.condition :=
  (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)

/-- The source is supported in the actual original-DAG model; literal
collapse preservation reads that same support in the primitive SCM layer. -/
noncomputable def host_supported :
    (ProbabilityTerm.kernel ⟨NodeSet.singleton y, query.action, chainCondition remaining y⟩).SupportedAt
      model.toLatentRootSCM reference := by
  rw [host_condition_eq]
  exact model.termSupportedAt_to_collapsed query.sourceTerm reference original_supported

/-- The old observable overlap premise genuinely fails here.  Positivity
of an `X,M` cylinder would imply positivity of its null `X` subcylinder. -/
theorem no_observational_overlap : ¬ ObservationalCylinderPositiveAt model.toLatentRootSCM
    (NodeSet.union query.action (chainCondition remaining y)) reference := by
  intro overlap
  have positive := ObservationalCylinderPositiveAt.of_subset
    (NodeSet.subset_union_left query.action (chainCondition remaining y)) overlap
  change 0 < (model.toLatentRootSCM.observationalDist.probVal (Kernel.agreesOn query.action reference)).num at positive
  rw [model.toLatentRootSCM_observationalDist, observational_action_is_null] at positive
  exact Nat.not_lt_zero _ positive

/-- Promotion and later-intervention invariance construct the entire
primitive source support from `host_supported`, despite the failed factual
overlap test.  No second support witness or semantic-equality leaf is input. -/
noncomputable def component_source_supported :
    (ProbabilityTerm.kernel ⟨NodeSet.singleton y,
      NodeSet.union query.action (NodeSet.diff remaining component), chainCondition component y⟩).SupportedAt
      model.toLatentRootSCM reference :=
  PublishedCurrentKernelReduction.componentFactor_source_supportedAt_of_host
    (remaining := remaining) (externalAction := query.action)
    model.toLatentRootSCM component component_subset y (by decide) reference host_supported

/-- Read the constructed support back into the original finite hidden DAG.
This regression is not restricted to canonical pairwise latent roots. -/
noncomputable def native_component_source_supported : model.TermSupportedAt
    (.kernel ⟨NodeSet.singleton y, NodeSet.union query.action (NodeSet.diff remaining component),
      chainCondition component y⟩) reference :=
  model.termSupportedAt_of_collapsed _ reference component_source_supported

end IntrinsicComponentAdmissibility
end Examples
end Causality
end Thesis
