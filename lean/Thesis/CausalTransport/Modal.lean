import Thesis.Causality.Modalities
import Thesis.CausalTransport.FiniteSource

namespace Thesis
namespace Causality

/-!
Transport-specific modal certificates.

The executable epistemic records and transitions live in `Modalities`; this
module adds soundness/completeness interfaces and mode-indexed identification
theorems.  Modal certificates retain their selected `GraphModelClass`; the
default remains `all` for existing callers.  In particular, a positive-class
certificate must not silently become an unrestricted zero-class certificate.
-/

/-- A transported joint certificate retaining its operation-sensitive modal trace. -/
structure ModalEncodedJointDerivation
    (G : ObservedGraph S) (query : JointKernelQuery S)
    (C : GraphModelClass G := GraphModelClass.all G) where
  certificate : JointIdentificationCertificate C query
  trace : ModalDerivationTrace G certificate.derivation

/-- Conditional counterpart of `ModalEncodedJointDerivation`. -/
structure ModalEncodedConditionalDerivation
    (G : ObservedGraph S) (query : ConditionalKernelQuery S)
    (C : GraphModelClass G := GraphModelClass.all G) where
  certificate : ConditionalIdentificationCertificate C query
  trace : ModalDerivationTrace G certificate.derivation

def EncodedJointDerivation.toModal
    {G : ObservedGraph S} {query : JointKernelQuery S}
    {C : GraphModelClass G} (encoded : EncodedJointDerivation C query) :
    ModalEncodedJointDerivation G query C where
  certificate := encoded.certificate
  trace := encoded.certificate.derivation.toModalTrace

def EncodedConditionalDerivation.toModal
    {G : ObservedGraph S} {query : ConditionalKernelQuery S}
    {C : GraphModelClass G} (encoded : EncodedConditionalDerivation C query) :
    ModalEncodedConditionalDerivation G query C where
  certificate := encoded.certificate
  trace := encoded.certificate.derivation.toModalTrace

def ModalEncodedJointDerivation.erase
    {C : GraphModelClass G} (encoded : ModalEncodedJointDerivation G query C) :
    EncodedJointDerivation C query where
  certificate := encoded.certificate

def ModalEncodedConditionalDerivation.erase
    {C : GraphModelClass G} (encoded : ModalEncodedConditionalDerivation G query C) :
    EncodedConditionalDerivation C query where
  certificate := encoded.certificate

theorem ModalEncodedJointDerivation.identifiable
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    (sound : PublishedSoundness S G)
    (encoded : ModalEncodedJointDerivation G query C) :
    C.identifiable query :=
  transport_joint_soundness sound query encoded.erase

theorem ModalEncodedConditionalDerivation.identifiable
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    (sound : PublishedSoundness S G)
    (encoded : ModalEncodedConditionalDerivation G query C) :
    C.conditionalIdentifiable query :=
  transport_conditional_soundness sound query encoded.erase

/-! ## Mode indices with explicit model-class membership

The historical mode wrappers below retain their unrestricted signatures.
These class-indexed versions additionally remember that the stored model is
in the certificate's class.  Compatibility alone would not justify applying
a positive-class support constructor at a zero-containing mode.
-/

structure ModeIndexedJointDerivationIn (mode : CausalMode S)
    {G : ObservedGraph S} (C : GraphModelClass G) (query : JointKernelQuery S) where
  member : C.Mem mode.record.model
  encoded : ModalEncodedJointDerivation G query C

structure ModeIndexedConditionalDerivationIn (mode : CausalMode S)
    {G : ObservedGraph S} (C : GraphModelClass G) (query : ConditionalKernelQuery S) where
  member : C.Mem mode.record.model
  encoded : ModalEncodedConditionalDerivation G query C

/-- Class membership supplies the weaker graphical compatibility premise. -/
theorem ModeIndexedJointDerivationIn.compatible
    {C : GraphModelClass G} (indexed : ModeIndexedJointDerivationIn mode C query) :
    Compatible mode.record.model G :=
  C.mem_compatible mode.record.model indexed.member

theorem ModeIndexedConditionalDerivationIn.compatible
    {C : GraphModelClass G} (indexed : ModeIndexedConditionalDerivationIn mode C query) :
    Compatible mode.record.model G :=
  C.mem_compatible mode.record.model indexed.member

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

/-- Exact modal transport inside a selected class.  No completeness record
for the larger `all` class is required or inferred. -/
theorem transported_joint_iff_in (mode : CausalMode S)
    {G : ObservedGraph S} (C : GraphModelClass G)
    (complete : PublishedCompleteness C) (sound : PublishedSoundness S G)
    (query : JointKernelQuery S) :
    (C.Mem mode.record.model ∧ C.identifiable query) ↔
      Nonempty (ModeIndexedJointDerivationIn mode C query) := by
  constructor
  · rintro ⟨member, identified⟩
    exact ⟨⟨member, (transport_joint_completeness complete query identified).toModal⟩⟩
  · rintro ⟨indexed⟩
    exact ⟨indexed.member, indexed.encoded.identifiable sound⟩

/-- Conditional transport has the same class boundary; the underlying
certificate still retains its original source-support obligations. -/
theorem transported_conditional_iff_in (mode : CausalMode S)
    {G : ObservedGraph S} (C : GraphModelClass G)
    (complete : PublishedCompleteness C) (sound : PublishedSoundness S G)
    (query : ConditionalKernelQuery S) :
    (C.Mem mode.record.model ∧ C.conditionalIdentifiable query) ↔
      Nonempty (ModeIndexedConditionalDerivationIn mode C query) := by
  constructor
  · rintro ⟨member, identified⟩
    exact ⟨⟨member, (transport_conditional_completeness complete query identified).toModal⟩⟩
  · rintro ⟨indexed⟩
    exact ⟨indexed.member, indexed.encoded.identifiable sound⟩

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
    (complete : PublishedCompleteness
      (GraphModelClass.all mode.record.model.observedGraph))
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
    (complete : PublishedCompleteness
      (GraphModelClass.all mode.record.model.observedGraph))
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
