import Thesis.CausalTransport.GuardedPrintedSoundness
import Thesis.CausalTransport.HiddenDAGAdmissibility

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-!
# Actual certificates from explicit native admissibility tests

Unlike the old positive-model certificate, these records quantify over every
original finite hidden-DAG SCM and over admissible references individually.
Their support boundary consists of explicit primitive conditions: fixed
action values overlap on supported observed-parent contexts, the conditionals
actually used by the literal returned expression are admissible, and a
conditional query's original intervened conditioner has positive mass.
The action quantification is stated explicitly; pointwise context overlap is
not silently substituted for supported-parent overlap.

No field assumes compiler `Data`, a completed recursive support tree, or a
semantic equation.  The constructors below compute the actual successful
compiler, read the primitive tests into printed support, and use the uniform
ID/IDC availability proofs to construct every intermediate tree.  The stored
success equation and path derivation keep the literal program output visible.

The displayed action test is a boundary of the published application, not a
new requirement on every internal support constructor.  In particular the
conditional support recursion continues to use intrinsic conditioner
promotion rather than factual action overlap.

These are automatic certificates at actual success, valid throughout their
explicit zero-permitting application domain.  The semantic completeness
direction and the final query-domain package must still be assembled; this
module does not relabel the old positive `PublishedCompleteness` record.
-/

/-- An actual successful guarded joint formula with its native path proof
and a constructed support tree at every explicitly admissible application.
The observed law may have zeros and hidden/noise alphabets remain arbitrary. -/
structure PublishedAdmissibleJointCertificate (P : FiniteLatentProjection S) (query : JointKernelQuery S) where
  formula : ProbabilityTerm S
  result : identifyGuardedJointKernel P.observedGraph query = .identified formula
  actionFree : formula.ActionFree
  derivation : PathDoCalculusDerivation P.observedGraph query.sourceTerm formula
  supported : forall model : FiniteHiddenDAGSCM S P, forall reference : S.Assignment,
    model.ObservationalActionAdmissibleOnParentSupport query.action reference →
    model.UsedConditionalsAdmissibleAt formula reference →
    HiddenDAGLocalDerivationSupport model reference (derivation.compile P.observedGraph.dSeparationCorrectness)

/-- A conditional certificate retains the original intervened conditioner's
positivity in addition to the observable action and used-conditional tests.
It does not equate a defined printed formula with a meaningful null source. -/
structure PublishedAdmissibleConditionalCertificate (P : FiniteLatentProjection S) (query : ConditionalKernelQuery S) where
  formula : ProbabilityTerm S
  result : identifyGuardedConditionalKernel P.observedGraph query = .identified formula
  actionFree : formula.ActionFree
  derivation : PathDoCalculusDerivation P.observedGraph query.sourceTerm formula
  supported : forall model : FiniteHiddenDAGSCM S P, forall reference : S.Assignment,
    model.ObservationalActionAdmissibleOnParentSupport query.action reference →
    model.ConditioningAdmissibleAt query.operationKernel reference →
    model.UsedConditionalsAdmissibleAt formula reference →
    HiddenDAGLocalDerivationSupport model reference (derivation.compile P.observedGraph.dSeparationCorrectness)

/-- Compile the actual successful joint output into the reference-indexed
certificate.  The primitive native conditional tests construct the printed
value, which constructs the real aligned compiler data and native tree. -/
noncomputable def identifyGuardedJointKernel_admissibleCertificate
    (query : JointKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyGuardedJointKernel P.observedGraph query = .identified term) :
    PublishedAdmissibleJointCertificate P query := by
  let compiled := (identifyGuardedJointKernelLocalCompilation P.observedGraph.dSeparationCorrectness query result).aligned
  exact {
    formula := term
    result := result
    actionFree := identifyGuardedJointKernel_identified_actionFree P.observedGraph query result
    derivation := compiled.reduction.derivation
    supported := fun model reference _actionAdmissible usedConditionals => by
      let printed := model.supportedAt_of_usedConditionalsAdmissible term reference usedConditionals
      let available := identifyGuardedJointKernelLocalCompilation_printedAvailable P.observedGraph.dSeparationCorrectness query result
      let data := available model.toLatentRootSCM
        (fun first second => model.toLatentRootSCM_projectedGraph first second) reference
        (model.termSupportedAt_to_collapsed term reference printed)
      exact compiled.hiddenDAG_supportedAt model reference data
  }

/-- Compile every actual conditional success, including all promotions.
Both native endpoints come from primitive positivity tests; the uniform IDC
proof supplies every recursive promotion, Bayes and marginal support subtree. -/
noncomputable def identifyGuardedConditionalKernel_admissibleCertificate
    (query : ConditionalKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyGuardedConditionalKernel P.observedGraph query = .identified term) :
    PublishedAdmissibleConditionalCertificate P query := by
  let compiled := (identifyGuardedConditionalKernelLocalCompilation P.observedGraph.dSeparationCorrectness query result).aligned
  exact {
    formula := term
    result := result
    actionFree := identifyGuardedConditionalKernel_identified_actionFree P.observedGraph query result
    derivation := compiled.derivation
    supported := fun model reference _actionAdmissible sourceAdmissible usedConditionals => by
      let source := model.supportedAt_of_conditioningAdmissible query.operationKernel reference sourceAdmissible
      let printed := model.supportedAt_of_usedConditionalsAdmissible term reference usedConditionals
      let available := identifyGuardedConditionalKernelLocalCompilation_printedAvailable P.observedGraph.dSeparationCorrectness query result
      let data := available model.toLatentRootSCM
        (fun first second => model.toLatentRootSCM_projectedGraph first second) reference
        (model.termSupportedAt_to_collapsed query.sourceTerm reference source)
        (model.termSupportedAt_to_collapsed term reference printed)
      exact compiled.hiddenDAG_supportedAt model reference data
  }

/-- Interpret the joint certificate's actual native tree at an admissible
reference, without an external soundness interface or a global-positive class. -/
noncomputable def PublishedAdmissibleJointCertificate.soundAt {query : JointKernelQuery S}
    (certificate : PublishedAdmissibleJointCertificate P query)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (actionAdmissible : model.ObservationalActionAdmissibleOnParentSupport query.action reference)
    (usedConditionals : model.UsedConditionalsAdmissibleAt certificate.formula reference) :
    model.TermEquivalentAt query.sourceTerm certificate.formula reference :=
  certificate.derivation.hiddenDAG_denotational_soundAt
    (certificate.supported model reference actionAdmissible usedConditionals)

/-- Interpret the conditional certificate while retaining actual source
conditioning admissibility.  Positive outcome numerators are not required. -/
noncomputable def PublishedAdmissibleConditionalCertificate.soundAt {query : ConditionalKernelQuery S}
    (certificate : PublishedAdmissibleConditionalCertificate P query)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (actionAdmissible : model.ObservationalActionAdmissibleOnParentSupport query.action reference)
    (sourceAdmissible : model.ConditioningAdmissibleAt query.operationKernel reference)
    (usedConditionals : model.UsedConditionalsAdmissibleAt certificate.formula reference) :
    model.TermEquivalentAt query.sourceTerm certificate.formula reference :=
  certificate.derivation.hiddenDAG_denotational_soundAt
    (certificate.supported model reference actionAdmissible sourceAdmissible usedConditionals)

/-- One model supplies the observable domain tests; observational agreement
transfers both supported-parent action overlap and used-conditional checks.
The certificate identifies the original joint values in the two actual DAGs. -/
noncomputable def PublishedAdmissibleJointCertificate.identifiableAt {query : JointKernelQuery S}
    (certificate : PublishedAdmissibleJointCertificate P query)
    (left right : FiniteHiddenDAGSCM S P) (observational : left.ObservationalAgreement right)
    (reference : S.Assignment)
    (actionAdmissible : left.ObservationalActionAdmissibleOnParentSupport query.action reference)
    (usedConditionals : left.UsedConditionalsAdmissibleAt certificate.formula reference) :
    ProbabilityResult.Equivalent (left.termDenote query.sourceTerm reference) (right.termDenote query.sourceTerm reference) :=
  ProbabilityResult.trans (certificate.soundAt left reference actionAdmissible usedConditionals)
    (ProbabilityResult.trans (FiniteHiddenDAGSCM.actionFree_invariant left right observational certificate.formula certificate.actionFree reference)
      (ProbabilityResult.symm (certificate.soundAt right reference
        (actionAdmissible.transfer observational)
        (usedConditionals.transfer observational certificate.formula certificate.actionFree reference))))

/-- Conditional comparison keeps the original conditioner's positivity in
both models.  Only the genuinely observable tests transfer across their common
observed law; causal source support is not inferred from that agreement. -/
noncomputable def PublishedAdmissibleConditionalCertificate.identifiableAt {query : ConditionalKernelQuery S}
    (certificate : PublishedAdmissibleConditionalCertificate P query)
    (left right : FiniteHiddenDAGSCM S P) (observational : left.ObservationalAgreement right)
    (reference : S.Assignment)
    (actionAdmissible : left.ObservationalActionAdmissibleOnParentSupport query.action reference)
    (leftSource : left.ConditioningAdmissibleAt query.operationKernel reference)
    (rightSource : right.ConditioningAdmissibleAt query.operationKernel reference)
    (usedConditionals : left.UsedConditionalsAdmissibleAt certificate.formula reference) :
    ProbabilityResult.Equivalent (left.termDenote query.sourceTerm reference) (right.termDenote query.sourceTerm reference) :=
  ProbabilityResult.trans (certificate.soundAt left reference actionAdmissible leftSource usedConditionals)
    (ProbabilityResult.trans (FiniteHiddenDAGSCM.actionFree_invariant left right observational certificate.formula certificate.actionFree reference)
      (ProbabilityResult.symm (certificate.soundAt right reference
        (actionAdmissible.transfer observational) rightSource
        (usedConditionals.transfer observational certificate.formula certificate.actionFree reference))))

end Causality
end Thesis
