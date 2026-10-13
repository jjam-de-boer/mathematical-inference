import Thesis.Causality.Admissibility
import Thesis.Examples.LocalSupportIdentification

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
end Examples
end Causality
end Thesis
