import Thesis.CausalTransport.HiddenDAGCorrespondence
import Thesis.Examples.HiddenDAGIdentification

namespace Thesis
namespace Causality
namespace Examples
namespace HiddenDAGCompleteness

open HiddenDAGCollapse

/-!
# Full hidden-DAG completeness regressions on a noncanonical hidden relay

Reuse the five-node original DAG `U,X,V,Y,Z`, whose projection contains
`X -> Y` and all three bidirected pairs.  Its actual collapse has a hidden
root with three observed children.  Neither the native soundness direction
nor the native countermodel direction can assume that collapse is canonical.

The successful queries use the existing literal ID/IDC output equations.
The failed queries ask for `Y` under `do(X)`, without and with conditioning on
`Z`.  Only the small projected engine's result tag is evaluated here.  The
actual countermodel records, their positivity, whole observed-law equality
and original-query separation come from the general proved construction;
no exponential full-model numerical evaluation is needed for these tests.

Every completeness field is exercised.  The hidden alphabet sizes are not
fixed by the Boolean alphabets of the earlier concrete soundness fixture.
-/

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => false
  second := fun _ => true
  first_enumerated := by intro _; change false ∈ [false, true]; decide +kernel
  second_enumerated := by intro _; change true ∈ [false, true]; decide +kernel
  different := fun _ => Bool.false_ne_true

/-- The full published record is inhabited for this actual original DAG,
not passed in as an assumption by the regression. -/
noncomputable def published : PublishedHiddenDAGCompleteness projection :=
  projection.publishedHiddenDAGCompleteness rich

/-- Success identifies the joint query in every positive original-DAG
record, not only the previously constructed numerical example. -/
theorem successful_joint_identifiable :
    (HiddenDAGModelClass.positive projection).identifiable HiddenDAGIdentification.jointQuery :=
  HiddenDAGModelClass.identifyJointKernel_identified _ HiddenDAGIdentification.joint_identified

/-- Feed native identifiability into the actual published joint field. -/
noncomputable def jointCertificate :
    PublishedJointCertificate (GraphModelClass.positive projection.observedGraph)
      projection.observedGraph.dSeparationCorrectness HiddenDAGIdentification.jointQuery :=
  projection.publishedHiddenDAGJointCompleteness rich _ successful_joint_identifiable

/-- Successful recursive IDC likewise quantifies over all positive native
records and compares the original conditional query on common support. -/
theorem successful_conditional_identifiable :
    (HiddenDAGModelClass.positive projection).conditionalIdentifiable
      HiddenDAGIdentification.conditionalQuery :=
  HiddenDAGModelClass.identifyConditionalKernel_identified _
    HiddenDAGIdentification.conditional_identified

noncomputable def conditionalCertificate :
    PublishedConditionalCertificate (GraphModelClass.positive projection.observedGraph)
      projection.observedGraph.dSeparationCorrectness HiddenDAGIdentification.conditionalQuery :=
  projection.publishedHiddenDAGConditionalCompleteness rich _ successful_conditional_identifiable

def failedJointQuery : JointKernelQuery signature where
  outcome := NodeSet.singleton y
  action := NodeSet.singleton x
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

def failedConditionalQuery : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton y
  action := NodeSet.singleton x
  condition := NodeSet.singleton z
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  action_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

/-- A finite tag check avoids demanding decidable equality of function-
valued node sets or probability-term syntax. -/
private def failedResult (result : IdentificationOutcome S) : Bool :=
  match result with
  | .failed _ => true
  | _ => false

/-- Recover the failure data from the actual computed result, not by
choosing a witness from propositional non-identifiability. -/
def jointFailure : {fail : IdentificationFail signature //
    identifyJointKernel projection.observedGraph failedJointQuery = .failed fail} := by
  have checked : failedResult
      (identifyJointKernel projection.observedGraph failedJointQuery) = true := by
    decide +kernel
  cases result : identifyJointKernel projection.observedGraph failedJointQuery with
  | identified term => simp only [result, failedResult, Bool.false_eq_true] at checked
  | failed fail => exact ⟨fail, rfl⟩
  | unfinished => simp only [result, failedResult, Bool.false_eq_true] at checked

def conditionalFailure : {fail : IdentificationFail signature //
    identifyConditionalKernel projection.observedGraph failedConditionalQuery = .failed fail} := by
  have checked : failedResult
      (identifyConditionalKernel projection.observedGraph failedConditionalQuery) = true := by
    decide +kernel
  cases result : identifyConditionalKernel projection.observedGraph failedConditionalQuery with
  | identified term => simp only [result, failedResult, Bool.false_eq_true] at checked
  | failed fail => exact ⟨fail, rfl⟩
  | unfinished => simp only [result, failedResult, Bool.false_eq_true] at checked

/-- Both members are actual positive finite SCM records on the original
five-node DAG.  They retain the failed query's original observed alphabets. -/
noncomputable def jointCounterexample :
    HiddenDAGCounterexampleIn (HiddenDAGModelClass.positive projection) failedJointQuery :=
  identifyJointKernel_hiddenDAG_failed_counterexample rich failedJointQuery jointFailure.property

/-- The conditional pair separates values where both original kernels are
supported, rather than merely changing their support domains. -/
noncomputable def conditionalCounterexample :
    HiddenDAGConditionalCounterexampleIn (HiddenDAGModelClass.positive projection)
      failedConditionalQuery :=
  identifyConditionalKernel_hiddenDAG_failed_counterexample rich failedConditionalQuery
    conditionalFailure.property

theorem failed_joint_not_identifiable :
    ¬ (HiddenDAGModelClass.positive projection).identifiable failedJointQuery :=
  jointCounterexample.not_identifiable

theorem failed_conditional_not_identifiable :
    ¬ (HiddenDAGModelClass.positive projection).conditionalIdentifiable failedConditionalQuery :=
  conditionalCounterexample.not_identifiable

/-- Positive failure witnesses also belong to the larger zero-permitting
class; no zero-unrestricted success theorem is inferred from this fact. -/
theorem failed_joint_not_identifiable_all :
    ¬ (HiddenDAGModelClass.all projection).identifiable failedJointQuery :=
  identifyJointKernel_hiddenDAG_failed_not_identifiable_all rich failedJointQuery jointFailure.property

/-- Exercise the actual hedge field on the extracted original-query hedge. -/
noncomputable def hedgeCounterexample :
    HiddenDAGCounterexampleIn (HiddenDAGModelClass.positive projection) failedJointQuery :=
  published.hedge_counterexample failedJointQuery
    (identifyJointKernelFailedHedge failedJointQuery jointFailure.property).witness

end HiddenDAGCompleteness
end Examples
end Causality
end Thesis
