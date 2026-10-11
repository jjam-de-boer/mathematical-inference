import Thesis.CausalTransport.HiddenDAGPositiveCertificates
import Thesis.CausalTransport.ConditionalCompilation

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature} {P : FiniteLatentProjection S}

/-!
# Successful ID/IDC formulas in their original hidden-DAG models

The corrected identification engines already return inspectable published
certificates for every successful run on an observed ADMG.  This module
interprets those same certificates in positive full hidden-DAG models.
The formula is the engine's literal output, not a separately chosen adjustment
formula, and neither canonical membership of the collapsed model nor an
external latent-projection interface is supplied.

The public conclusions deliberately assume an *actual successful engine
equation*.  They prove the forward direction: successful ID/IDC runs identify
their original query throughout any positive full-model family over the
projection.  They do not assert that every query identifiable in that family
must succeed.  Establishing that converse still needs countermodel lifting
to the original hidden DAG.  Nor is global positivity silently weakened to
arbitrary observational zeros: that needs the separate local-support compiler.
-/

/-- A successful joint ID formula denotes its original query in every
positive full hidden model over the supplied projection.  Observed and hidden
graph paths enter through the proved projection and native soundness. -/
noncomputable def identifyJointKernel_hiddenDAG_soundAt
    (query : JointKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyJointKernel P.observedGraph query = .identified term)
    (model : FiniteHiddenDAGSCM S P) (positive : model.ObservationallyPositive)
    (assignment : S.Assignment) :
    model.TermEquivalentAt query.sourceTerm term assignment := by
  let certificate := identifyJointKernelPublishedCertificate
    (C := GraphModelClass.positive P.observedGraph)
    P.observedGraph.dSeparationCorrectness (fun member => member.2) query result
  exact certificate.compile.hiddenDAG_denotational_soundAt model positive assignment

/-- The same forward interpretation for the full recursive IDC engine,
including its finite sequence of rule-2 conditioner promotions. -/
noncomputable def identifyConditionalKernel_hiddenDAG_soundAt
    (query : ConditionalKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyConditionalKernel P.observedGraph query = .identified term)
    (model : FiniteHiddenDAGSCM S P) (positive : model.ObservationallyPositive)
    (assignment : S.Assignment) :
    model.TermEquivalentAt query.sourceTerm term assignment := by
  let certificate := identifyConditionalKernelPublishedCertificate
    (C := GraphModelClass.positive P.observedGraph)
    P.observedGraph.dSeparationCorrectness (fun member => member.2) query result
  exact certificate.compile.hiddenDAG_denotational_soundAt model positive assignment

/-- Successful joint ID equates causal values in two original full models.
Their finite hidden and private-noise presentations may differ.  Positivity
of the second observed law follows from their observational agreement. -/
noncomputable def identifyJointKernel_hiddenDAG_identifiableAt
    (query : JointKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyJointKernel P.observedGraph query = .identified term)
    (left right : FiniteHiddenDAGSCM S P)
    (observational : left.ObservationalAgreement right)
    (positive : left.ObservationallyPositive) (assignment : S.Assignment) :
    ProbabilityResult.Equivalent (left.termDenote query.sourceTerm assignment)
      (right.termDenote query.sourceTerm assignment) := by
  let certificate := identifyJointKernelPublishedCertificate
    (C := GraphModelClass.positive P.observedGraph)
    P.observedGraph.dSeparationCorrectness (fun member => member.2) query result
  exact certificate.compile.toGeneric.hiddenDAG_identifiableAt
    trivial left right observational positive assignment

/-- Successful conditional ID gives the same original-model identification
conclusion.  Its actual conditioners are positive under the explicit premise;
no conclusion about a null conditional is inferred from this adapter. -/
noncomputable def identifyConditionalKernel_hiddenDAG_identifiableAt
    (query : ConditionalKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyConditionalKernel P.observedGraph query = .identified term)
    (left right : FiniteHiddenDAGSCM S P)
    (observational : left.ObservationalAgreement right)
    (positive : left.ObservationallyPositive) (assignment : S.Assignment) :
    ProbabilityResult.Equivalent (left.termDenote query.sourceTerm assignment)
      (right.termDenote query.sourceTerm assignment) := by
  let certificate := identifyConditionalKernelPublishedCertificate
    (C := GraphModelClass.positive P.observedGraph)
    P.observedGraph.dSeparationCorrectness (fun member => member.2) query result
  exact certificate.compile.toGeneric.hiddenDAG_identifiableAt
    trivial left right observational positive assignment

namespace HiddenDAGModelFamily

/-- Forward joint identification for any selected positive full-DAG family.
The quantifier is on the family's original semantic models; no pairwise-root
replacement is used to interpret its observational or causal probabilities. -/
theorem identifyJointKernel_identified
    (family : HiddenDAGModelFamily S P)
    (positive : forall model, (family.semantics model).ObservationallyPositive)
    (query : JointKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyJointKernel P.observedGraph query = .identified term) :
    family.JointIdentifiable query := by
  intro left right observational assignment
  have agreement : (family.semantics left).ObservationalAgreement (family.semantics right) :=
    observational
  exact ⟨identifyJointKernel_hiddenDAG_identifiableAt (P := P) query result
    (family.semantics left) (family.semantics right) agreement
    (positive left) assignment⟩

/-- Forward conditional identification in the same native family semantics.
The common-support API is respected, though positivity supplies that support
everywhere for these particular family members. -/
theorem identifyConditionalKernel_identified
    (family : HiddenDAGModelFamily S P)
    (positive : forall model, (family.semantics model).ObservationallyPositive)
    (query : ConditionalKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyConditionalKernel P.observedGraph query = .identified term) :
    family.ConditionalIdentifiable query := by
  intro left right observational assignment _leftSupported _rightSupported
  have agreement : (family.semantics left).ObservationalAgreement (family.semantics right) :=
    observational
  exact ⟨identifyConditionalKernel_hiddenDAG_identifiableAt (P := P) query result
    (family.semantics left) (family.semantics right) agreement
    (positive left) assignment⟩

end HiddenDAGModelFamily
end Causality
end Thesis
