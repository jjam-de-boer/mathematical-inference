import Thesis.Causality.ModalRealization
import Thesis.CausalTransport.Modal

namespace Thesis
namespace Causality

open Probability

/-! Transport certificates enriched with executable modal realizations. -/

/--
A transported joint certificate whose source kernel and every Pearl-rule leaf
are tied to executable record operations in every compatible target model.
-/
structure OperationRealizedJointCertificate
    (sound : PublishedSoundness S G) (query : JointKernelQuery S) where
  certificate : JointIdentificationCertificate G query
  trace : ModalDerivationTrace G certificate.derivation
  realized : forall (model : ExactModel S) (compatible : Compatible model G)
      (assignment : S.Assignment)
      (sourceSupported : query.sourceTerm.SupportedAt model assignment),
    let supportTree := certificate.supported model compatible assignment
      sourceSupported
    KernelOperationRealization model query.operationKernel assignment ×
      trace.OperationRealizations assignment
        (sound.primitive model compatible) supportTree

/-- Conditional counterpart of `OperationRealizedJointCertificate`. -/
structure OperationRealizedConditionalCertificate
    (sound : PublishedSoundness S G) (query : ConditionalKernelQuery S) where
  certificate : ConditionalIdentificationCertificate G query
  trace : ModalDerivationTrace G certificate.derivation
  realized : forall (model : ExactModel S) (compatible : Compatible model G)
      (assignment : S.Assignment)
      (sourceSupported : query.sourceTerm.SupportedAt model assignment),
    let supportTree := certificate.supported model compatible assignment
      sourceSupported
    KernelOperationRealization model query.operationKernel assignment ×
      trace.OperationRealizations assignment
        (sound.primitive model compatible) supportTree

/--
An operation-realized joint certificate indexed by a concrete compatible
epistemic mode.  The underlying certificate remains uniform over all
compatible models; `atMode` below specializes it to the model stored at this
mode.
-/
structure ModeIndexedOperationRealizedJointCertificate
    (mode : CausalMode S) (G : ObservedGraph S)
    (sound : PublishedSoundness S G) (query : JointKernelQuery S) where
  compatible : mode.CompatibleWith G
  certificate : OperationRealizedJointCertificate sound query

/-- Conditional counterpart of `ModeIndexedOperationRealizedJointCertificate`. -/
structure ModeIndexedOperationRealizedConditionalCertificate
    (mode : CausalMode S) (G : ObservedGraph S)
    (sound : PublishedSoundness S G) (query : ConditionalKernelQuery S) where
  compatible : mode.CompatibleWith G
  certificate : OperationRealizedConditionalCertificate sound query

namespace ModeIndexedOperationRealizedJointCertificate

variable {S : ObservedSignature} {G : ObservedGraph S}
  {sound : PublishedSoundness S G} {query : JointKernelQuery S}
  {mode : CausalMode S}

/-- Forget executable realizations while retaining the compatible modal index. -/
def toModeIndexedDerivation
    (indexed : ModeIndexedOperationRealizedJointCertificate
      mode G sound query) :
    ModeIndexedJointDerivation mode G query where
  compatible := indexed.compatible
  encoded :=
    { certificate := indexed.certificate.certificate
      trace := indexed.certificate.trace }

/-- Specialize the uniform executable realization to the indexed mode's model. -/
noncomputable def atMode
    (indexed : ModeIndexedOperationRealizedJointCertificate
      mode G sound query)
    (assignment : S.Assignment)
    (sourceSupported : query.sourceTerm.SupportedAt
      mode.record.model assignment) :
    let supportTree := indexed.certificate.certificate.supported
      mode.record.model indexed.compatible assignment sourceSupported
    KernelOperationRealization mode.record.model query.operationKernel assignment ×
      indexed.certificate.trace.OperationRealizations assignment
        (sound.primitive mode.record.model indexed.compatible) supportTree :=
  indexed.certificate.realized mode.record.model indexed.compatible assignment
    sourceSupported

end ModeIndexedOperationRealizedJointCertificate

namespace ModeIndexedOperationRealizedConditionalCertificate

variable {S : ObservedSignature} {G : ObservedGraph S}
  {sound : PublishedSoundness S G} {query : ConditionalKernelQuery S}
  {mode : CausalMode S}

/-- Forget executable realizations while retaining the compatible modal index. -/
def toModeIndexedDerivation
    (indexed : ModeIndexedOperationRealizedConditionalCertificate
      mode G sound query) :
    ModeIndexedConditionalDerivation mode G query where
  compatible := indexed.compatible
  encoded :=
    { certificate := indexed.certificate.certificate
      trace := indexed.certificate.trace }

/-- Specialize the uniform executable realization to the indexed mode's model. -/
noncomputable def atMode
    (indexed : ModeIndexedOperationRealizedConditionalCertificate
      mode G sound query)
    (assignment : S.Assignment)
    (sourceSupported : query.sourceTerm.SupportedAt
      mode.record.model assignment) :
    let supportTree := indexed.certificate.certificate.supported
      mode.record.model indexed.compatible assignment sourceSupported
    KernelOperationRealization mode.record.model query.operationKernel assignment ×
      indexed.certificate.trace.OperationRealizations assignment
        (sound.primitive mode.record.model indexed.compatible) supportTree :=
  indexed.certificate.realized mode.record.model indexed.compatible assignment
    sourceSupported

end ModeIndexedOperationRealizedConditionalCertificate

namespace ModalEncodedJointDerivation

noncomputable def toOperationRealized
    (sound : PublishedSoundness S G)
    (encoded : ModalEncodedJointDerivation G query) :
    OperationRealizedJointCertificate sound query where
  certificate := encoded.certificate
  trace := encoded.trace
  realized := by
    intro model compatible assignment sourceSupported
    let supportTree := encoded.certificate.supported model compatible assignment
      sourceSupported
    have kernelSupported : ProbabilityTerm.SupportedAt model
        (.kernel query.operationKernel) assignment := by
      simpa using sourceSupported
    exact ⟨KernelOperationRealization.ofSupported kernelSupported,
      encoded.trace.realizeOperations assignment
        (sound.primitive model compatible) supportTree⟩

end ModalEncodedJointDerivation

namespace ModalEncodedConditionalDerivation

noncomputable def toOperationRealized
    (sound : PublishedSoundness S G)
    (encoded : ModalEncodedConditionalDerivation G query) :
    OperationRealizedConditionalCertificate sound query where
  certificate := encoded.certificate
  trace := encoded.trace
  realized := by
    intro model compatible assignment sourceSupported
    let supportTree := encoded.certificate.supported model compatible assignment
      sourceSupported
    have kernelSupported : ProbabilityTerm.SupportedAt model
        (.kernel query.operationKernel) assignment := by
      simpa using sourceSupported
    exact ⟨KernelOperationRealization.ofSupported kernelSupported,
      encoded.trace.realizeOperations assignment
        (sound.primitive model compatible) supportTree⟩

end ModalEncodedConditionalDerivation

namespace OperationRealizedJointCertificate

variable {S : ObservedSignature} {G : ObservedGraph S}
  {sound : PublishedSoundness S G} {query : JointKernelQuery S}

theorem identifiable
    (realized : OperationRealizedJointCertificate sound query) :
    TypeTheoreticIdentifiable G query :=
  realized.certificate.identifiable sound

end OperationRealizedJointCertificate

namespace OperationRealizedConditionalCertificate

variable {S : ObservedSignature} {G : ObservedGraph S}
  {sound : PublishedSoundness S G} {query : ConditionalKernelQuery S}

theorem identifiable
    (realized : OperationRealizedConditionalCertificate sound query) :
    TypeTheoreticConditionalIdentifiable G query :=
  realized.certificate.identifiable sound

end OperationRealizedConditionalCertificate

/--
The finite source theorem transports all the way to operation-realized modal
certificates, provided both its completeness and primitive soundness
specializations are supplied.
-/
theorem finiteSource_operationRealized_joint_iff
    (complete : PublishedFiniteSourceCompleteness T G)
    (sound : PublishedFiniteSourceSoundness T G)
    (query : JointKernelQuery T.toObserved) :
    TypeTheoreticIdentifiable G.interpret query <->
      Nonempty (OperationRealizedJointCertificate sound.toPublished query) := by
  constructor
  · intro identifiable
    rcases (finiteSource_completeness_transport complete).1 query identifiable with
      ⟨encoded⟩
    exact ⟨encoded.toModal.toOperationRealized sound.toPublished⟩
  · intro realized
    rcases realized with ⟨realized⟩
    exact realized.identifiable

theorem finiteSource_operationRealized_conditional_iff
    (complete : PublishedFiniteSourceCompleteness T G)
    (sound : PublishedFiniteSourceSoundness T G)
    (query : ConditionalKernelQuery T.toObserved) :
    TypeTheoreticConditionalIdentifiable G.interpret query <->
      Nonempty
        (OperationRealizedConditionalCertificate sound.toPublished query) := by
  constructor
  · intro identifiable
    rcases (finiteSource_completeness_transport complete).2.1 query identifiable with
      ⟨encoded⟩
    exact ⟨encoded.toModal.toOperationRealized sound.toPublished⟩
  · intro realized
    rcases realized with ⟨realized⟩
    exact realized.identifiable

/--
The operation-realized joint transport with compatibility and executable
realizations combined in one mode-indexed certificate.
-/
theorem finiteSource_modeIndexedOperationRealized_joint_iff
    (mode : CausalMode T.toObserved) (G : FiniteTableGraph T)
    (currentCompatible : mode.CompatibleWith G.interpret)
    (complete : PublishedFiniteSourceCompleteness T G)
    (sound : PublishedFiniteSourceSoundness T G)
    (query : JointKernelQuery T.toObserved) :
    mode.JointIdentifiableOn G.interpret query <->
      Nonempty
        (ModeIndexedOperationRealizedJointCertificate mode G.interpret
          sound.toPublished query) := by
  constructor
  · intro identifiable
    rcases (finiteSource_operationRealized_joint_iff complete sound query).mp
        identifiable with ⟨certificate⟩
    exact ⟨⟨currentCompatible, certificate⟩⟩
  · intro indexed
    rcases indexed with ⟨indexed⟩
    exact (finiteSource_operationRealized_joint_iff complete sound query).mpr
      ⟨indexed.certificate⟩

/-- Conditional counterpart of the mode-indexed operation-realized transport. -/
theorem finiteSource_modeIndexedOperationRealized_conditional_iff
    (mode : CausalMode T.toObserved) (G : FiniteTableGraph T)
    (currentCompatible : mode.CompatibleWith G.interpret)
    (complete : PublishedFiniteSourceCompleteness T G)
    (sound : PublishedFiniteSourceSoundness T G)
    (query : ConditionalKernelQuery T.toObserved) :
    mode.ConditionalIdentifiableOn G.interpret query <->
      Nonempty
        (ModeIndexedOperationRealizedConditionalCertificate mode G.interpret
          sound.toPublished query) := by
  constructor
  · intro identifiable
    rcases (finiteSource_operationRealized_conditional_iff complete sound query).mp
        identifiable with ⟨certificate⟩
    exact ⟨⟨currentCompatible, certificate⟩⟩
  · intro indexed
    rcases indexed with ⟨indexed⟩
    exact (finiteSource_operationRealized_conditional_iff complete sound query).mpr
      ⟨indexed.certificate⟩

end Causality
end Thesis
