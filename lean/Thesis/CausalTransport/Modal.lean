import Thesis.Causality.Modalities
import Thesis.CausalTransport.FiniteSource

namespace Thesis
namespace Causality

/-!
Transport-specific modal certificates.

The executable epistemic records and transitions live in `Modalities`; this
module adds the external soundness/completeness interfaces and mode-indexed
identification theorems.
-/

/-- A transported joint certificate retaining its operation-sensitive modal trace. -/
structure ModalEncodedJointDerivation
    (G : ObservedGraph S) (query : JointKernelQuery S) where
  certificate : JointIdentificationCertificate G query
  trace : ModalDerivationTrace G certificate.derivation

/-- Conditional counterpart of `ModalEncodedJointDerivation`. -/
structure ModalEncodedConditionalDerivation
    (G : ObservedGraph S) (query : ConditionalKernelQuery S) where
  certificate : ConditionalIdentificationCertificate G query
  trace : ModalDerivationTrace G certificate.derivation

def EncodedJointDerivation.toModal
    (encoded : EncodedJointDerivation G query) :
    ModalEncodedJointDerivation G query where
  certificate := encoded.certificate
  trace := encoded.certificate.derivation.toModalTrace

def EncodedConditionalDerivation.toModal
    (encoded : EncodedConditionalDerivation G query) :
    ModalEncodedConditionalDerivation G query where
  certificate := encoded.certificate
  trace := encoded.certificate.derivation.toModalTrace

def ModalEncodedJointDerivation.erase
    (encoded : ModalEncodedJointDerivation G query) :
    EncodedJointDerivation G query where
  certificate := encoded.certificate

def ModalEncodedConditionalDerivation.erase
    (encoded : ModalEncodedConditionalDerivation G query) :
    EncodedConditionalDerivation G query where
  certificate := encoded.certificate

theorem ModalEncodedJointDerivation.identifiable
    (sound : PublishedSoundness S G)
    (encoded : ModalEncodedJointDerivation G query) :
    TypeTheoreticIdentifiable G query :=
  transport_joint_soundness sound query encoded.erase

theorem ModalEncodedConditionalDerivation.identifiable
    (sound : PublishedSoundness S G)
    (encoded : ModalEncodedConditionalDerivation G query) :
    TypeTheoreticConditionalIdentifiable G query :=
  transport_conditional_soundness sound query encoded.erase

/-- A modal certificate indexed by a concrete compatible epistemic mode. -/
structure ModeIndexedJointDerivation (mode : CausalMode S)
    (G : ObservedGraph S) (query : JointKernelQuery S) where
  compatible : Compatible mode.record.model G
  encoded : ModalEncodedJointDerivation G query

structure ModeIndexedConditionalDerivation (mode : CausalMode S)
    (G : ObservedGraph S) (query : ConditionalKernelQuery S) where
  compatible : Compatible mode.record.model G
  encoded : ModalEncodedConditionalDerivation G query

namespace CausalMode

def JointIdentifiable (mode : CausalMode S) (query : JointKernelQuery S) : Prop :=
  TypeTheoreticIdentifiable mode.record.model.observedGraph query

def ConditionalIdentifiable (mode : CausalMode S)
    (query : ConditionalKernelQuery S) : Prop :=
  TypeTheoreticConditionalIdentifiable mode.record.model.observedGraph query

def CompatibleWith (mode : CausalMode S) (graph : ObservedGraph S) : Prop :=
  Compatible mode.record.model graph

def JointIdentifiableOn (_mode : CausalMode S) (graph : ObservedGraph S)
    (query : JointKernelQuery S) : Prop :=
  TypeTheoreticIdentifiable graph query

def ConditionalIdentifiableOn (_mode : CausalMode S)
    (graph : ObservedGraph S) (query : ConditionalKernelQuery S) : Prop :=
  TypeTheoreticConditionalIdentifiable graph query

theorem transported_joint_iff (mode : CausalMode S)
    (complete : PublishedCompleteness S mode.record.model.observedGraph)
    (sound : PublishedSoundness S mode.record.model.observedGraph)
    (query : JointKernelQuery S) :
    mode.JointIdentifiable query <->
      Nonempty (ModalEncodedJointDerivation
        mode.record.model.observedGraph query) := by
  constructor
  · intro identifiable
    exact ⟨(transport_joint_completeness complete query identifiable).toModal⟩
  · intro encoded
    rcases encoded with ⟨encoded⟩
    exact encoded.identifiable sound

theorem transported_conditional_iff (mode : CausalMode S)
    (complete : PublishedCompleteness S mode.record.model.observedGraph)
    (sound : PublishedSoundness S mode.record.model.observedGraph)
    (query : ConditionalKernelQuery S) :
    mode.ConditionalIdentifiable query <->
      Nonempty (ModalEncodedConditionalDerivation
        mode.record.model.observedGraph query) := by
  constructor
  · intro identifiable
    exact ⟨(transport_conditional_completeness complete query identifiable).toModal⟩
  · intro encoded
    rcases encoded with ⟨encoded⟩
    exact encoded.identifiable sound

/--
For the finite source, compatibility and joint identifiability are exactly the
data packaged by a mode-indexed transported derivation.
-/
theorem finiteSource_transported_joint_iff
    (mode : CausalMode T.toObserved) (G : FiniteTableGraph T)
    (complete : PublishedFiniteSourceCompleteness T G)
    (sound : PublishedFiniteSourceSoundness T G)
    (query : JointKernelQuery T.toObserved) :
    (mode.CompatibleWith G.interpret /\
      mode.JointIdentifiableOn G.interpret query) <->
      Nonempty (ModeIndexedJointDerivation mode G.interpret query) := by
  constructor
  · rintro ⟨currentCompatible, identifiable⟩
    have encoded := transport_joint_completeness complete.toPublished
      query identifiable
    exact ⟨⟨currentCompatible, encoded.toModal⟩⟩
  · rintro ⟨indexed⟩
    exact ⟨indexed.compatible,
      indexed.encoded.identifiable sound.toPublished⟩

/-- Conditional counterpart of the exact mode-indexed finite-source package. -/
theorem finiteSource_transported_conditional_iff
    (mode : CausalMode T.toObserved) (G : FiniteTableGraph T)
    (complete : PublishedFiniteSourceCompleteness T G)
    (sound : PublishedFiniteSourceSoundness T G)
    (query : ConditionalKernelQuery T.toObserved) :
    (mode.CompatibleWith G.interpret /\
      mode.ConditionalIdentifiableOn G.interpret query) <->
      Nonempty (ModeIndexedConditionalDerivation mode G.interpret query) := by
  constructor
  · rintro ⟨currentCompatible, identifiable⟩
    have encoded := transport_conditional_completeness complete.toPublished
      query identifiable
    exact ⟨⟨currentCompatible, encoded.toModal⟩⟩
  · rintro ⟨indexed⟩
    exact ⟨indexed.compatible,
      indexed.encoded.identifiable sound.toPublished⟩

/-- Compatibility-specialized form of `finiteSource_transported_joint_iff`. -/
theorem finiteSource_transported_joint_iff_of_compatible
    (mode : CausalMode T.toObserved) (G : FiniteTableGraph T)
    (currentCompatible : mode.CompatibleWith G.interpret)
    (complete : PublishedFiniteSourceCompleteness T G)
    (sound : PublishedFiniteSourceSoundness T G)
    (query : JointKernelQuery T.toObserved) :
    mode.JointIdentifiableOn G.interpret query <->
      Nonempty (ModeIndexedJointDerivation mode G.interpret query) := by
  constructor
  · intro identifiable
    exact (finiteSource_transported_joint_iff mode G complete sound query).mp
      ⟨currentCompatible, identifiable⟩
  · intro certificate
    exact ((finiteSource_transported_joint_iff mode G complete sound query).mpr
      certificate).2

/-- Compatibility-specialized form of `finiteSource_transported_conditional_iff`. -/
theorem finiteSource_transported_conditional_iff_of_compatible
    (mode : CausalMode T.toObserved) (G : FiniteTableGraph T)
    (currentCompatible : mode.CompatibleWith G.interpret)
    (complete : PublishedFiniteSourceCompleteness T G)
    (sound : PublishedFiniteSourceSoundness T G)
    (query : ConditionalKernelQuery T.toObserved) :
    mode.ConditionalIdentifiableOn G.interpret query <->
      Nonempty (ModeIndexedConditionalDerivation mode G.interpret query) := by
  constructor
  · intro identifiable
    exact (finiteSource_transported_conditional_iff mode G complete sound query).mp
      ⟨currentCompatible, identifiable⟩
  · intro certificate
    exact ((finiteSource_transported_conditional_iff mode G complete sound query).mpr
      certificate).2

/-- Completeness transport with both a compatible mode index and modal traces. -/
theorem finiteSource_modal_completeness_transport
    (mode : CausalMode T.toObserved) (G : FiniteTableGraph T)
    (currentCompatible : mode.CompatibleWith G.interpret)
    (complete : PublishedFiniteSourceCompleteness T G) :
    (forall query,
      TypeTheoreticIdentifiable G.interpret query ->
        Nonempty (ModeIndexedJointDerivation mode G.interpret query)) /\
    (forall query,
      TypeTheoreticConditionalIdentifiable G.interpret query ->
        Nonempty (ModeIndexedConditionalDerivation mode G.interpret query)) /\
    (forall query, HedgeWitness G.interpret query ->
      Not (TypeTheoreticIdentifiable G.interpret query)) := by
  rcases finiteSource_completeness_transport complete with
    ⟨joint, conditional, hedge⟩
  exact ⟨fun query identifiable => by
      rcases joint query identifiable with ⟨encoded⟩
      exact ⟨⟨currentCompatible, encoded.toModal⟩⟩,
    fun query identifiable => by
      rcases conditional query identifiable with ⟨encoded⟩
      exact ⟨⟨currentCompatible, encoded.toModal⟩⟩,
    hedge⟩

end CausalMode

namespace CausalTransition

theorem jointIdentifiable_iff (transition : CausalTransition S)
    (query : JointKernelQuery S) :
    transition.source.JointIdentifiable query <->
      transition.target.JointIdentifiable query := by
  rw [CausalMode.JointIdentifiable, CausalMode.JointIdentifiable,
    transition.model_eq]

theorem conditionalIdentifiable_iff (transition : CausalTransition S)
    (query : ConditionalKernelQuery S) :
    transition.source.ConditionalIdentifiable query <->
      transition.target.ConditionalIdentifiable query := by
  rw [CausalMode.ConditionalIdentifiable, CausalMode.ConditionalIdentifiable,
    transition.model_eq]

theorem compatibleWith_iff (transition : CausalTransition S)
    (graph : ObservedGraph S) :
    transition.source.CompatibleWith graph <->
      transition.target.CompatibleWith graph := by
  rw [CausalMode.CompatibleWith, CausalMode.CompatibleWith,
    transition.model_eq]

end CausalTransition

end Causality
end Thesis
