import Thesis.CausalTransport.ModalRealization
import Thesis.CausalTransport.HiddenDAGSupportedCorrespondence

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-!
# Support-aware modal completeness in original finite hidden DAGs

Observed zeros do not give positive-class membership.  Instead, the completed
native certificates construct local support from the displayed formula's
primitive demand tests, together with the original source conditioner for a
conditional target.  This module retains those exact application boundaries
when adding modal traces and executable intervention/observation records.

The executed model is the native model's intervention-preserving collapse.
Its roots may have more than two children: no false `Compatible` premise is
inserted.  Literal native/collapsed result preservation and the proved native
path soundness connect every operation value back to the original full DAG.
The caller supplies neither a complete support tree nor an additional
soundness/completeness theorem.  Undefined conditionals are never completed.
-/

/-- A native derivation with every modal rule leaf realized and the source
and observational formula both tied to the actually executed kernel value.
The support field remains indexed by this model and this reference. -/
structure NativeModalKernelRealization (model : FiniteHiddenDAGSCM S P)
    (kernel : Kernel S) (formula : ProbabilityTerm S) (reference : S.Assignment)
    (derivation : DoCalculusDerivation P.observedGraph (.kernel kernel) formula)
    (trace : ModalDerivationTrace P.observedGraph derivation) where
  supported : HiddenDAGLocalDerivationSupport model reference derivation
  operation : KernelOperationRealization model.toLatentRootSCM kernel reference
  leaves : trace.OperationRealizations reference
    model.collapsedPathPrimitiveSoundness.compileChecked supported.toCollapsed
  nativeValue : ProbabilityResult.Equivalent
    (model.kernelDenote kernel reference) (some operation.value)
  formulaValue : ProbabilityResult.Equivalent
    (model.termDenote formula reference) (some operation.value)

namespace NativeModalKernelRealization

/-- Construct executable payloads from the certificate's already proved
native support; no global positivity or canonical pair-root restriction. -/
noncomputable def ofSupport (model : FiniteHiddenDAGSCM S P)
    (kernel : Kernel S) (formula : ProbabilityTerm S) (reference : S.Assignment)
    (derivation : DoCalculusDerivation P.observedGraph (.kernel kernel) formula)
    (trace : ModalDerivationTrace P.observedGraph derivation)
    (supported : HiddenDAGLocalDerivationSupport model reference derivation) :
    NativeModalKernelRealization model kernel formula reference derivation trace := by
  let collapsed := supported.toCollapsed
  let operation := KernelOperationRealization.ofSupported collapsed.endpoints.1
  have nativeValue : ProbabilityResult.Equivalent
      (model.kernelDenote kernel reference) (some operation.value) := by
    rw [model.kernelDenote_preserved kernel reference]
    exact operation.denotation
  exact {
    supported := supported
    operation := operation
    leaves := trace.realizeOperations reference
      model.collapsedPathPrimitiveSoundness.compileChecked collapsed
    nativeValue := nativeValue
    formulaValue := ProbabilityResult.trans
      (ProbabilityResult.symm (derivation.hiddenDAG_denotational_soundAt supported)) nativeValue
  }

end NativeModalKernelRealization

/-- A realized source cannot be an undefined conditional.  The payload's
native equation is a checked defined value, not a default zero. -/
theorem NativeModalKernelRealization.source_ne_none
    {model : FiniteHiddenDAGSCM S P} {kernel : Kernel S} {formula : ProbabilityTerm S}
    {reference : S.Assignment}
    {derivation : DoCalculusDerivation P.observedGraph (.kernel kernel) formula}
    {trace : ModalDerivationTrace P.observedGraph derivation}
    (realized : NativeModalKernelRealization model kernel formula reference derivation trace) :
    model.kernelDenote kernel reference ≠ none := by
  intro absent
  have value := realized.nativeValue
  rw [absent] at value
  cases value

theorem NativeModalKernelRealization.formula_ne_none
    {model : FiniteHiddenDAGSCM S P} {kernel : Kernel S} {formula : ProbabilityTerm S}
    {reference : S.Assignment}
    {derivation : DoCalculusDerivation P.observedGraph (.kernel kernel) formula}
    {trace : ModalDerivationTrace P.observedGraph derivation}
    (realized : NativeModalKernelRealization model kernel formula reference derivation trace) :
    model.termDenote formula reference ≠ none := by
  intro absent
  have value := realized.formulaValue
  rw [absent] at value
  cases value

/-- The literal successful joint program and its modal trace. -/
structure AdmissibleModalJointDerivation (projection : FiniteLatentProjection S)
    (query : JointKernelQuery S) where
  certificate : PublishedAdmissibleJointCertificate projection query
  trace : ModalDerivationTrace projection.observedGraph
    (certificate.derivation.compile projection.observedGraph.dSeparationCorrectness)

/-- Conditional targets retain their separate source-conditioning demand. -/
structure AdmissibleModalConditionalDerivation (projection : FiniteLatentProjection S)
    (query : ConditionalKernelQuery S) where
  certificate : PublishedAdmissibleConditionalCertificate projection query
  trace : ModalDerivationTrace projection.observedGraph
    (certificate.derivation.compile projection.observedGraph.dSeparationCorrectness)

def PublishedAdmissibleJointCertificate.toModal
    (certificate : PublishedAdmissibleJointCertificate P query) :
    AdmissibleModalJointDerivation P query where
  certificate := certificate
  trace := (certificate.derivation.compile P.observedGraph.dSeparationCorrectness).toModalTrace

def PublishedAdmissibleConditionalCertificate.toModal
    (certificate : PublishedAdmissibleConditionalCertificate P query) :
    AdmissibleModalConditionalDerivation P query where
  certificate := certificate
  trace := (certificate.derivation.compile P.observedGraph.dSeparationCorrectness).toModalTrace

/-- The formula's demand tests generate every intermediate support witness.
A zero outcome is permitted; an undefined demanded conditional is not. -/
noncomputable def AdmissibleModalJointDerivation.realizeAt
    (encoded : AdmissibleModalJointDerivation P query)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (used : model.UsedConditionalsAdmissibleAt encoded.certificate.formula reference) :
    NativeModalKernelRealization model query.operationKernel encoded.certificate.formula reference
      (encoded.certificate.derivation.compile P.observedGraph.dSeparationCorrectness) encoded.trace :=
  NativeModalKernelRealization.ofSupport model query.operationKernel encoded.certificate.formula reference
    (encoded.certificate.derivation.compile P.observedGraph.dSeparationCorrectness) encoded.trace
    (encoded.certificate.supported model reference used)

noncomputable def AdmissibleModalConditionalDerivation.realizeAt
    (encoded : AdmissibleModalConditionalDerivation P query)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (source : model.ConditioningAdmissibleAt query.operationKernel reference)
    (used : model.UsedConditionalsAdmissibleAt encoded.certificate.formula reference) :
    NativeModalKernelRealization model query.operationKernel encoded.certificate.formula reference
      (encoded.certificate.derivation.compile P.observedGraph.dSeparationCorrectness) encoded.trace :=
  NativeModalKernelRealization.ofSupport model query.operationKernel encoded.certificate.formula reference
    (encoded.certificate.derivation.compile P.observedGraph.dSeparationCorrectness) encoded.trace
    (encoded.certificate.supported model reference source used)

namespace FiniteLatentProjection

/-- Completed supported-zero completeness now returns a modal certificate,
without an external completeness record or caller-supplied compiler data. -/
noncomputable def supportedJointModalCompleteness
    (projection : FiniteLatentProjection S) (rich : ObservedSignature.ValueRich S)
    (query : JointKernelQuery S) (identified : HiddenDAGSupportedDomain.jointIdentifiable projection query) :
    AdmissibleModalJointDerivation projection query :=
  (projection.supportedAdmissibleJointCompleteness rich query identified).toModal

noncomputable def supportedConditionalModalCompleteness
    (projection : FiniteLatentProjection S) (rich : ObservedSignature.ValueRich S)
    (query : ConditionalKernelQuery S)
    (identified : HiddenDAGSupportedDomain.conditionalIdentifiable projection query) :
    AdmissibleModalConditionalDerivation projection query :=
  (projection.supportedAdmissibleConditionalCompleteness rich query identified).toModal

theorem supported_joint_modal_iff
    (projection : FiniteLatentProjection S) (rich : ObservedSignature.ValueRich S)
    (query : JointKernelQuery S) : HiddenDAGSupportedDomain.jointIdentifiable projection query ↔
      Nonempty (AdmissibleModalJointDerivation projection query) := by
  constructor
  · intro identified
    exact ⟨projection.supportedJointModalCompleteness rich query identified⟩
  · rintro ⟨encoded⟩
    exact encoded.certificate.supported_identifiable

theorem supported_conditional_modal_iff
    (projection : FiniteLatentProjection S) (rich : ObservedSignature.ValueRich S)
    (query : ConditionalKernelQuery S) : HiddenDAGSupportedDomain.conditionalIdentifiable projection query ↔
      Nonempty (AdmissibleModalConditionalDerivation projection query) := by
  constructor
  · intro identified
    exact ⟨projection.supportedConditionalModalCompleteness rich query identified⟩
  · rintro ⟨encoded⟩
    exact encoded.certificate.supported_identifiable

end FiniteLatentProjection

namespace FiniteHiddenDAGSCM

/-- Initial epistemic mode of this native model, with its proved collapse
as the stored SCM.  No conditioning or positivity is hidden in this adapter. -/
def initialCausalMode (model : FiniteHiddenDAGSCM S P) (name : String) : CausalMode S :=
  ⟨name, CausalEpistemicRecord.initial model.toLatentRootSCM⟩

end FiniteHiddenDAGSCM

/-- A native joint certificate attached to a mode of that exact model.
Model equality is weaker and more accurate than canonical compatibility. -/
structure ModeIndexedAdmissibleJointDerivation (model : FiniteHiddenDAGSCM S P)
    (mode : CausalMode S) (query : JointKernelQuery S) where
  model_eq : mode.record.model = model.toLatentRootSCM
  encoded : AdmissibleModalJointDerivation P query

structure ModeIndexedAdmissibleConditionalDerivation (model : FiniteHiddenDAGSCM S P)
    (mode : CausalMode S) (query : ConditionalKernelQuery S) where
  model_eq : mode.record.model = model.toLatentRootSCM
  encoded : AdmissibleModalConditionalDerivation P query

/-- Read the local native application at the attached mode's model.  The
mode equality is retained in the wrapper; execution starts from its model
prior, just as in the positive-class operation API. -/
noncomputable def ModeIndexedAdmissibleJointDerivation.realizeAt
    {model : FiniteHiddenDAGSCM S P} {mode : CausalMode S} {query : JointKernelQuery S}
    (indexed : ModeIndexedAdmissibleJointDerivation model mode query)
    (reference : S.Assignment)
    (used : model.UsedConditionalsAdmissibleAt indexed.encoded.certificate.formula reference) :
    NativeModalKernelRealization model query.operationKernel indexed.encoded.certificate.formula reference
      (indexed.encoded.certificate.derivation.compile P.observedGraph.dSeparationCorrectness) indexed.encoded.trace :=
  indexed.encoded.realizeAt model reference used

noncomputable def ModeIndexedAdmissibleConditionalDerivation.realizeAt
    {model : FiniteHiddenDAGSCM S P} {mode : CausalMode S} {query : ConditionalKernelQuery S}
    (indexed : ModeIndexedAdmissibleConditionalDerivation model mode query)
    (reference : S.Assignment)
    (source : model.ConditioningAdmissibleAt query.operationKernel reference)
    (used : model.UsedConditionalsAdmissibleAt indexed.encoded.certificate.formula reference) :
    NativeModalKernelRealization model query.operationKernel indexed.encoded.certificate.formula reference
      (indexed.encoded.certificate.derivation.compile P.observedGraph.dSeparationCorrectness) indexed.encoded.trace :=
  indexed.encoded.realizeAt model reference source used

/-- The executed value answers the query at the *stored* mode model.
This uses the model-equality witness rather than ignoring the mode index. -/
noncomputable def ModeIndexedAdmissibleJointDerivation.sourceAtMode
    {model : FiniteHiddenDAGSCM S P} {mode : CausalMode S} {query : JointKernelQuery S}
    (indexed : ModeIndexedAdmissibleJointDerivation model mode query)
    (reference : S.Assignment)
    (used : model.UsedConditionalsAdmissibleAt indexed.encoded.certificate.formula reference) :
    ProbabilityResult.Equivalent (query.sourceTerm.denote mode.record.model reference)
      (some (indexed.realizeAt reference used).operation.value) := by
  rw [indexed.model_eq]
  exact (indexed.realizeAt reference used).operation.denotation

noncomputable def ModeIndexedAdmissibleConditionalDerivation.sourceAtMode
    {model : FiniteHiddenDAGSCM S P} {mode : CausalMode S} {query : ConditionalKernelQuery S}
    (indexed : ModeIndexedAdmissibleConditionalDerivation model mode query)
    (reference : S.Assignment)
    (source : model.ConditioningAdmissibleAt query.operationKernel reference)
    (used : model.UsedConditionalsAdmissibleAt indexed.encoded.certificate.formula reference) :
    ProbabilityResult.Equivalent (query.sourceTerm.denote mode.record.model reference)
      (some (indexed.realizeAt reference source used).operation.value) := by
  rw [indexed.model_eq]
  exact (indexed.realizeAt reference source used).operation.denotation

namespace CausalMode

noncomputable def supportedJointModalCompleteness (mode : CausalMode S)
    (model : FiniteHiddenDAGSCM S P) (model_eq : mode.record.model = model.toLatentRootSCM)
    (rich : ObservedSignature.ValueRich S) (query : JointKernelQuery S)
    (identified : HiddenDAGSupportedDomain.jointIdentifiable P query) :
    ModeIndexedAdmissibleJointDerivation model mode query where
  model_eq := model_eq
  encoded := P.supportedJointModalCompleteness rich query identified

noncomputable def supportedConditionalModalCompleteness (mode : CausalMode S)
    (model : FiniteHiddenDAGSCM S P) (model_eq : mode.record.model = model.toLatentRootSCM)
    (rich : ObservedSignature.ValueRich S) (query : ConditionalKernelQuery S)
    (identified : HiddenDAGSupportedDomain.conditionalIdentifiable P query) :
    ModeIndexedAdmissibleConditionalDerivation model mode query where
  model_eq := model_eq
  encoded := P.supportedConditionalModalCompleteness rich query identified

theorem supported_joint_modal_iff (mode : CausalMode S)
    (model : FiniteHiddenDAGSCM S P) (rich : ObservedSignature.ValueRich S)
    (query : JointKernelQuery S) :
    (mode.record.model = model.toLatentRootSCM ∧ HiddenDAGSupportedDomain.jointIdentifiable P query) ↔
      Nonempty (ModeIndexedAdmissibleJointDerivation model mode query) := by
  constructor
  · rintro ⟨same, identified⟩
    exact ⟨mode.supportedJointModalCompleteness model same rich query identified⟩
  · rintro ⟨indexed⟩
    exact ⟨indexed.model_eq, indexed.encoded.certificate.supported_identifiable⟩

theorem supported_conditional_modal_iff (mode : CausalMode S)
    (model : FiniteHiddenDAGSCM S P) (rich : ObservedSignature.ValueRich S)
    (query : ConditionalKernelQuery S) :
    (mode.record.model = model.toLatentRootSCM ∧ HiddenDAGSupportedDomain.conditionalIdentifiable P query) ↔
      Nonempty (ModeIndexedAdmissibleConditionalDerivation model mode query) := by
  constructor
  · rintro ⟨same, identified⟩
    exact ⟨mode.supportedConditionalModalCompleteness model same rich query identified⟩
  · rintro ⟨indexed⟩
    exact ⟨indexed.model_eq, indexed.encoded.certificate.supported_identifiable⟩

end CausalMode
end Causality
end Thesis
