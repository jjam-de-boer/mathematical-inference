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
Their intrinsic support boundary consists of the conditionals actually used
by the literal returned expression and, for a conditional query, positivity
of the original intervened conditioner.  The full availability proofs do not
need factual action overlap, so the stored support constructor now exposes
that stronger result instead of retaining an unused action premise.

No field assumes compiler `Data`, a completed recursive support tree, or a
semantic equation.  The constructors below compute the actual successful
compiler, read the primitive tests into printed support, and use the uniform
ID/IDC availability proofs to construct every intermediate tree.  The stored
success equation and path derivation keep the literal program output visible.

The displayed action test remains a separate boundary of the papers'
application.  The established `soundAt` and `identifiableAt` wrappers retain
it for compatibility; the `intrinsic_*` methods do not request it.  Thus
valid reductions at null factual actions are also covered, without claiming
that an undefined printed formula or null original conditioner has a value.

These are automatic certificates at actual success, valid throughout their
explicit zero-permitting application domain.  The independent primitive
query-domain completeness direction is assembled in
`HiddenDAGAdmissibleCompleteness`.  The broader intrinsic semantic
correspondence retaining the used-conditional qualification is assembled in
`HiddenDAGSupportedCorrespondence`.  Neither package asserts that external
action admissibility alone supplies every internal quotient.
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
    model.UsedConditionalsAdmissibleAt formula reference →
    HiddenDAGLocalDerivationSupport model reference (derivation.compile P.observedGraph.dSeparationCorrectness)

/-- A conditional certificate retains the original intervened conditioner's
positivity in addition to its used-conditional tests, without factual overlap.
It does not equate a defined printed formula with a meaningful null source. -/
structure PublishedAdmissibleConditionalCertificate (P : FiniteLatentProjection S) (query : ConditionalKernelQuery S) where
  formula : ProbabilityTerm S
  result : identifyGuardedConditionalKernel P.observedGraph query = .identified formula
  actionFree : formula.ActionFree
  derivation : PathDoCalculusDerivation P.observedGraph query.sourceTerm formula
  supported : forall model : FiniteHiddenDAGSCM S P, forall reference : S.Assignment,
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
    supported := fun model reference usedConditionals => by
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
    supported := fun model reference sourceAdmissible usedConditionals => by
      let source := model.supportedAt_of_conditioningAdmissible query.operationKernel reference sourceAdmissible
      let printed := model.supportedAt_of_usedConditionalsAdmissible term reference usedConditionals
      let available := identifyGuardedConditionalKernelLocalCompilation_printedAvailable P.observedGraph.dSeparationCorrectness query result
      let data := available model.toLatentRootSCM
        (fun first second => model.toLatentRootSCM_projectedGraph first second) reference
        (model.termSupportedAt_to_collapsed query.sourceTerm reference source)
        (model.termSupportedAt_to_collapsed term reference printed)
      exact compiled.hiddenDAG_supportedAt model reference data
  }

/-- Interpret the actual joint tree wherever the printed expression's
primitive demand tests hold.  Factual action overlap is unnecessary: the
uniform availability construction already supplies every causal predecessor. -/
noncomputable def PublishedAdmissibleJointCertificate.intrinsic_soundAt {query : JointKernelQuery S}
    (certificate : PublishedAdmissibleJointCertificate P query)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (usedConditionals : model.UsedConditionalsAdmissibleAt certificate.formula reference) :
    model.TermEquivalentAt query.sourceTerm certificate.formula reference :=
  certificate.derivation.hiddenDAG_denotational_soundAt
    (certificate.supported model reference usedConditionals)

/-- Intrinsic conditional interpretation needs the original native
conditioner, not factual action overlap.  This includes valid promotions at
null factual actions and still excludes unsupported original targets. -/
noncomputable def PublishedAdmissibleConditionalCertificate.intrinsic_soundAt {query : ConditionalKernelQuery S}
    (certificate : PublishedAdmissibleConditionalCertificate P query)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (sourceAdmissible : model.ConditioningAdmissibleAt query.operationKernel reference)
    (usedConditionals : model.UsedConditionalsAdmissibleAt certificate.formula reference) :
    model.TermEquivalentAt query.sourceTerm certificate.formula reference :=
  certificate.derivation.hiddenDAG_denotational_soundAt
    (certificate.supported model reference sourceAdmissible usedConditionals)

/-- The paper-qualified joint wrapper keeps its established action-test
signature while delegating to the stronger intrinsic tree interpretation. -/
noncomputable def PublishedAdmissibleJointCertificate.soundAt {query : JointKernelQuery S}
    (certificate : PublishedAdmissibleJointCertificate P query)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (_actionAdmissible : model.ObservationalActionAdmissibleOnParentSupport query.action reference)
    (usedConditionals : model.UsedConditionalsAdmissibleAt certificate.formula reference) :
    model.TermEquivalentAt query.sourceTerm certificate.formula reference :=
  certificate.intrinsic_soundAt model reference usedConditionals

/-- Interpret the conditional certificate while retaining actual source
conditioning admissibility.  Positive outcome numerators are not required. -/
noncomputable def PublishedAdmissibleConditionalCertificate.soundAt {query : ConditionalKernelQuery S}
    (certificate : PublishedAdmissibleConditionalCertificate P query)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (_actionAdmissible : model.ObservationalActionAdmissibleOnParentSupport query.action reference)
    (sourceAdmissible : model.ConditioningAdmissibleAt query.operationKernel reference)
    (usedConditionals : model.UsedConditionalsAdmissibleAt certificate.formula reference) :
    model.TermEquivalentAt query.sourceTerm certificate.formula reference :=
  certificate.intrinsic_soundAt model reference sourceAdmissible usedConditionals

/-- Intrinsic two-model joint identification needs only one model's
observable primitive demand tests.  Agreement transfers those tests and the
literal formula; no factual action-overlap premise is supplied on either side. -/
noncomputable def PublishedAdmissibleJointCertificate.intrinsic_identifiableAt {query : JointKernelQuery S}
    (certificate : PublishedAdmissibleJointCertificate P query)
    (left right : FiniteHiddenDAGSCM S P) (observational : left.ObservationalAgreement right)
    (reference : S.Assignment)
    (usedConditionals : left.UsedConditionalsAdmissibleAt certificate.formula reference) :
    ProbabilityResult.Equivalent (left.termDenote query.sourceTerm reference) (right.termDenote query.sourceTerm reference) :=
  ProbabilityResult.trans (certificate.intrinsic_soundAt left reference usedConditionals)
    (ProbabilityResult.trans (FiniteHiddenDAGSCM.actionFree_invariant left right observational certificate.formula certificate.actionFree reference)
      (ProbabilityResult.symm (certificate.intrinsic_soundAt right reference
        (usedConditionals.transfer observational certificate.formula certificate.actionFree reference))))

/-- Intrinsic conditional identification retains actual causal source
positivity on both sides; it drops only the unnecessary factual action test.
Observational agreement is never used to infer the other causal conditioner. -/
noncomputable def PublishedAdmissibleConditionalCertificate.intrinsic_identifiableAt {query : ConditionalKernelQuery S}
    (certificate : PublishedAdmissibleConditionalCertificate P query)
    (left right : FiniteHiddenDAGSCM S P) (observational : left.ObservationalAgreement right)
    (reference : S.Assignment)
    (leftSource : left.ConditioningAdmissibleAt query.operationKernel reference)
    (rightSource : right.ConditioningAdmissibleAt query.operationKernel reference)
    (usedConditionals : left.UsedConditionalsAdmissibleAt certificate.formula reference) :
    ProbabilityResult.Equivalent (left.termDenote query.sourceTerm reference) (right.termDenote query.sourceTerm reference) :=
  ProbabilityResult.trans (certificate.intrinsic_soundAt left reference leftSource usedConditionals)
    (ProbabilityResult.trans (FiniteHiddenDAGSCM.actionFree_invariant left right observational certificate.formula certificate.actionFree reference)
      (ProbabilityResult.symm (certificate.intrinsic_soundAt right reference rightSource
        (usedConditionals.transfer observational certificate.formula certificate.actionFree reference))))

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
