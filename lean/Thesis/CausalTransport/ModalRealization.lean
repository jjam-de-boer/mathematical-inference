import Thesis.Causality.ModalRealization
import Thesis.CausalTransport.Modal

namespace Thesis
namespace Causality

open Probability

universe u

/-!
Transport certificates enriched with executable modal realizations.

Joint and conditional kernel queries share the same operation-realization
payload once their source term, operation kernel, and underlying identification
certificate are fixed. `OperationRealizedCertificateCore` carries that payload
once. The generic, joint, and conditional public structures extend this core,
while their promoted `certificate` fields retain the query-specific types.
-/

/--
Shared operation-realization payload for an underlying identification
certificate presentation.
-/
structure OperationRealizedCertificateCore
    (sound : PublishedSoundness S G) (sourceTerm : ProbabilityTerm S)
    (operationKernel : Kernel S) (Certificate : Type u)
    (toIdentification : Certificate ->
      IdentificationCertificate (GraphModelClass.all G) sourceTerm) where
  certificate : Certificate
  trace : ModalDerivationTrace G (toIdentification certificate).derivation
  realized : forall (model : ExactModel S) (compatible : Compatible model G)
      (assignment : S.Assignment)
      (sourceSupported : sourceTerm.SupportedAt model assignment),
    let supportTree := (toIdentification certificate).supported model compatible
      assignment sourceSupported
    KernelOperationRealization model operationKernel assignment ×
      trace.OperationRealizations assignment
        (sound.primitive model compatible) supportTree

/--
An identification certificate whose source kernel and every Pearl-rule leaf
are tied to executable record operations in every compatible target model.
-/
structure OperationRealizedCertificate
    (sound : PublishedSoundness S G) (sourceTerm : ProbabilityTerm S)
    (operationKernel : Kernel S) extends
      OperationRealizedCertificateCore sound sourceTerm operationKernel
        (IdentificationCertificate (GraphModelClass.all G) sourceTerm) (fun certificate => certificate)

structure OperationRealizedJointCertificate
    (sound : PublishedSoundness S G) (query : JointKernelQuery S) extends
      OperationRealizedCertificateCore sound query.sourceTerm query.operationKernel
        (JointIdentificationCertificate (GraphModelClass.all G) query)
        (fun certificate => certificate.toGeneric)

structure OperationRealizedConditionalCertificate
    (sound : PublishedSoundness S G) (query : ConditionalKernelQuery S) extends
      OperationRealizedCertificateCore sound query.sourceTerm query.operationKernel
        (ConditionalIdentificationCertificate (GraphModelClass.all G) query)
        (fun certificate => certificate.toGeneric)

def OperationRealizedJointCertificate.toGeneric
    (certificate : OperationRealizedJointCertificate sound query) :
    OperationRealizedCertificate sound query.sourceTerm query.operationKernel where
  certificate := certificate.certificate.toGeneric
  trace := certificate.trace
  realized := certificate.realized

def OperationRealizedConditionalCertificate.toGeneric
    (certificate : OperationRealizedConditionalCertificate sound query) :
    OperationRealizedCertificate sound query.sourceTerm query.operationKernel where
  certificate := certificate.certificate.toGeneric
  trace := certificate.trace
  realized := certificate.realized

/--
An operation-realized certificate indexed by a concrete compatible epistemic
mode.  The underlying certificate remains uniform over all compatible models;
the joint/conditional `atMode` wrappers below specialize it to the stored
model.
-/
structure ModeIndexedOperationRealizedCertificateCore
    (mode : CausalMode S) (G : ObservedGraph S) (Certificate : Type u) where
  compatible : mode.CompatibleWith G
  certificate : Certificate

structure ModeIndexedOperationRealizedCertificate
    (mode : CausalMode S) (G : ObservedGraph S)
    (sound : PublishedSoundness S G) (sourceTerm : ProbabilityTerm S)
    (operationKernel : Kernel S) extends
      ModeIndexedOperationRealizedCertificateCore mode G
        (OperationRealizedCertificate sound sourceTerm operationKernel)

structure ModeIndexedOperationRealizedJointCertificate
    (mode : CausalMode S) (G : ObservedGraph S)
    (sound : PublishedSoundness S G) (query : JointKernelQuery S) extends
      ModeIndexedOperationRealizedCertificateCore mode G
        (OperationRealizedJointCertificate sound query)

structure ModeIndexedOperationRealizedConditionalCertificate
    (mode : CausalMode S) (G : ObservedGraph S)
    (sound : PublishedSoundness S G) (query : ConditionalKernelQuery S) extends
      ModeIndexedOperationRealizedCertificateCore mode G
        (OperationRealizedConditionalCertificate sound query)

namespace ModeIndexedOperationRealizedJointCertificate

variable {S : ObservedSignature} {G : ObservedGraph S}
  {sound : PublishedSoundness S G} {query : JointKernelQuery S}
  {mode : CausalMode S}

/-- Forget the joint query wrapper while retaining mode compatibility. -/
def toGeneric
    (indexed : ModeIndexedOperationRealizedJointCertificate
      mode G sound query) :
    ModeIndexedOperationRealizedCertificate mode G sound query.sourceTerm
      query.operationKernel where
  compatible := indexed.compatible
  certificate := indexed.certificate.toGeneric

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

/-- Forget the conditional query wrapper while retaining mode compatibility. -/
def toGeneric
    (indexed : ModeIndexedOperationRealizedConditionalCertificate
      mode G sound query) :
    ModeIndexedOperationRealizedCertificate mode G sound query.sourceTerm
      query.operationKernel where
  compatible := indexed.compatible
  certificate := indexed.certificate.toGeneric

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
  JointIdentificationCertificate.identifiable sound realized.certificate

end OperationRealizedJointCertificate

namespace OperationRealizedConditionalCertificate

variable {S : ObservedSignature} {G : ObservedGraph S}
  {sound : PublishedSoundness S G} {query : ConditionalKernelQuery S}

theorem identifiable
    (realized : OperationRealizedConditionalCertificate sound query) :
    TypeTheoreticConditionalIdentifiable G query :=
  ConditionalIdentificationCertificate.identifiable sound realized.certificate

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
realizations combined in one mode-indexed certificate.  Compatibility is part
of both sides of the equivalence because the certificate stores its witness.
-/
theorem finiteSource_modeIndexedOperationRealized_joint_iff
    (mode : CausalMode T.toObserved) (G : FiniteTableGraph T)
    (complete : PublishedFiniteSourceCompleteness T G)
    (sound : PublishedFiniteSourceSoundness T G)
    (query : JointKernelQuery T.toObserved) :
    (mode.CompatibleWith G.interpret /\
      mode.JointIdentifiableOn G.interpret query) <->
      Nonempty
        (ModeIndexedOperationRealizedJointCertificate mode G.interpret
          sound.toPublished query) := by
  constructor
  · rintro ⟨currentCompatible, identifiable⟩
    rcases (finiteSource_operationRealized_joint_iff complete sound query).mp
        identifiable with ⟨certificate⟩
    exact ⟨⟨currentCompatible, certificate⟩⟩
  · rintro ⟨indexed⟩
    exact ⟨indexed.compatible,
      (finiteSource_operationRealized_joint_iff complete sound query).mpr
        ⟨indexed.certificate⟩⟩

/-- Conditional counterpart of the exact mode-indexed operation-realized package. -/
theorem finiteSource_modeIndexedOperationRealized_conditional_iff
    (mode : CausalMode T.toObserved) (G : FiniteTableGraph T)
    (complete : PublishedFiniteSourceCompleteness T G)
    (sound : PublishedFiniteSourceSoundness T G)
    (query : ConditionalKernelQuery T.toObserved) :
    (mode.CompatibleWith G.interpret /\
      mode.ConditionalIdentifiableOn G.interpret query) <->
      Nonempty
        (ModeIndexedOperationRealizedConditionalCertificate mode G.interpret
          sound.toPublished query) := by
  constructor
  · rintro ⟨currentCompatible, identifiable⟩
    rcases (finiteSource_operationRealized_conditional_iff complete sound query).mp
        identifiable with ⟨certificate⟩
    exact ⟨⟨currentCompatible, certificate⟩⟩
  · rintro ⟨indexed⟩
    exact ⟨indexed.compatible,
      (finiteSource_operationRealized_conditional_iff complete sound query).mpr
        ⟨indexed.certificate⟩⟩

/-- Compatibility-specialized form of the mode-indexed joint equivalence. -/
theorem finiteSource_modeIndexedOperationRealized_joint_iff_of_compatible
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
    exact (finiteSource_modeIndexedOperationRealized_joint_iff
      mode G complete sound query).mp ⟨currentCompatible, identifiable⟩
  · intro certificate
    exact ((finiteSource_modeIndexedOperationRealized_joint_iff
      mode G complete sound query).mpr certificate).2

/-- Compatibility-specialized form of the mode-indexed conditional equivalence. -/
theorem finiteSource_modeIndexedOperationRealized_conditional_iff_of_compatible
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
    exact (finiteSource_modeIndexedOperationRealized_conditional_iff
      mode G complete sound query).mp ⟨currentCompatible, identifiable⟩
  · intro certificate
    exact ((finiteSource_modeIndexedOperationRealized_conditional_iff
      mode G complete sound query).mpr certificate).2

end Causality
end Thesis
