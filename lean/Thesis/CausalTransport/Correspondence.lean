import Thesis.CausalTransport.Certificates

namespace Thesis
namespace Causality

open Probability

/-!
External completeness and soundness interfaces with checked certificate transport.

The published identification theorem is deliberately represented by explicit
parameters.  Internal query semantics and identifiability live in
`Thesis.Causality.Identification`.

Completeness and certificates are indexed by a `GraphModelClass`, so positivity
and other regularity hypotheses are specialisations rather than constraints on
the SCM layer.  Primitive soundness remains stated for every compatible model
under local support.

This file is the generic, graph-indexed boundary. It does not depend on the
finite source-table encoding: `FiniteSource` specializes these interfaces only
after independently defining source evaluation and its preservation map. A
reader looking for what Lean assumes should begin with `PublishedCompleteness`
and `PublishedSoundness`; a reader looking for what Lean proves should follow
the certificate compilation and transport theorems below.
-/

/-! ## Explicit external theorem interface and checked transport -/

/-!
The generic records in `Certificates` factor the shared certificate shape.
The following query-indexed structures expose the joint and conditional fields
directly; explicit adapters map them to the generic representation.
-/

structure JointIdentificationCertificate {S : ObservedSignature}
    {G : ObservedGraph S} (C : GraphModelClass G)
    (q : JointKernelQuery S) extends IdentificationCertificate C q.sourceTerm

structure ConditionalIdentificationCertificate {S : ObservedSignature}
    {G : ObservedGraph S} (C : GraphModelClass G)
    (q : ConditionalKernelQuery S) extends
      IdentificationCertificate C q.sourceTerm

structure PublishedJointCertificate {S : ObservedSignature}
    {G : ObservedGraph S} (C : GraphModelClass G)
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S) extends
      PublishedIdentificationCertificate C correct q.sourceTerm

structure PublishedConditionalCertificate {S : ObservedSignature}
    {G : ObservedGraph S} (C : GraphModelClass G)
    (correct : DSeparationCorrectness G) (q : ConditionalKernelQuery S) extends
      PublishedIdentificationCertificate C correct q.sourceTerm

def JointIdentificationCertificate.toGeneric
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {q : JointKernelQuery S}
    (certificate : JointIdentificationCertificate C q) :
    IdentificationCertificate C q.sourceTerm :=
  certificate.toIdentificationCertificate

def ConditionalIdentificationCertificate.toGeneric
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {q : ConditionalKernelQuery S}
    (certificate : ConditionalIdentificationCertificate C q) :
    IdentificationCertificate C q.sourceTerm :=
  certificate.toIdentificationCertificate

def JointIdentificationCertificate.ofGeneric
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {q : JointKernelQuery S}
    (certificate : IdentificationCertificate C q.sourceTerm) :
    JointIdentificationCertificate C q where
  toIdentificationCertificate := certificate

def ConditionalIdentificationCertificate.ofGeneric
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {q : ConditionalKernelQuery S}
    (certificate : IdentificationCertificate C q.sourceTerm) :
    ConditionalIdentificationCertificate C q where
  toIdentificationCertificate := certificate

def PublishedJointCertificate.toGeneric
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G} {q : JointKernelQuery S}
    (certificate : PublishedJointCertificate C correct q) :
    PublishedIdentificationCertificate C correct q.sourceTerm :=
  certificate.toPublishedIdentificationCertificate

def PublishedConditionalCertificate.toGeneric
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G} {q : ConditionalKernelQuery S}
    (certificate : PublishedConditionalCertificate C correct q) :
    PublishedIdentificationCertificate C correct q.sourceTerm :=
  certificate.toPublishedIdentificationCertificate

def PublishedJointCertificate.compile
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G} {q : JointKernelQuery S}
    (certificate : PublishedJointCertificate C correct q) :
    JointIdentificationCertificate C q :=
  JointIdentificationCertificate.ofGeneric certificate.toGeneric.compile

def PublishedConditionalCertificate.compile
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G} {q : ConditionalKernelQuery S}
    (certificate : PublishedConditionalCertificate C correct q) :
    ConditionalIdentificationCertificate C q :=
  ConditionalIdentificationCertificate.ofGeneric certificate.toGeneric.compile

/--
Formal interface to identification completeness inside a selected model class.

An inhabitant is passed to the transport theorem explicitly; no axiom is
declared in this module.  Unlike an arbitrary `Derivable` predicate, each
completeness field must return an inspectable do-calculus and
probability-algebra derivation.  The classical Shpitser–Pearl specialisation
is `PublishedCompleteness (GraphModelClass.positive G)` on a `ValueRich`
signature.
-/
structure PublishedCompleteness {S : ObservedSignature} {G : ObservedGraph S}
    (C : GraphModelClass G) where
  dseparation : DSeparationCorrectness G
  joint_complete : forall q,
    C.identifiable q ->
      PublishedJointCertificate C dseparation q
  conditional_complete : forall q,
    C.conditionalIdentifiable q ->
      PublishedConditionalCertificate C dseparation q
  hedge_counterexample : forall q,
    HedgeWitness G q -> CounterexampleIn C q

/-- Primitive semantics stated with the standard path-blocking side condition. -/
structure PathPrimitiveSoundness (G : ObservedGraph S)
    (model : FiniteLatentSCM S) where
  doRule : forall {left right} (assignment : S.Assignment),
    PathDoRuleApplication G left right ->
      ProbabilityTerm.SupportedAt model (.kernel left) assignment ->
      ProbabilityTerm.SupportedAt model (.kernel right) assignment ->
      ProbabilityTerm.EquivalentAt model (.kernel left) (.kernel right)
        assignment
  marginalization : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
      ProbabilityTerm.SupportedAt model (.kernel ⟨y, x, w⟩) assignment ->
      ProbabilityTerm.SupportedAt model
        (.marginalize z (.kernel ⟨NodeSet.union y z, x, w⟩)) assignment ->
      ProbabilityTerm.EquivalentAt model
        (.kernel ⟨y, x, w⟩)
        (.marginalize z (.kernel ⟨NodeSet.union y z, x, w⟩)) assignment
  conditioning : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
      ProbabilityTerm.SupportedAt model
        (.kernel ⟨y, x, NodeSet.union z w⟩) assignment ->
      ProbabilityTerm.SupportedAt model
        (.divide
          (.kernel ⟨NodeSet.union y z, x, w⟩)
          (.kernel ⟨z, x, w⟩)) assignment ->
      ProbabilityTerm.EquivalentAt model
        (.kernel ⟨y, x, NodeSet.union z w⟩)
        (.divide
          (.kernel ⟨NodeSet.union y z, x, w⟩)
          (.kernel ⟨z, x, w⟩)) assignment
  chain : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
      ProbabilityTerm.SupportedAt model
        (.kernel ⟨NodeSet.union y z, x, w⟩) assignment ->
      ProbabilityTerm.SupportedAt model
        (.multiply
          (.kernel ⟨y, x, NodeSet.union z w⟩)
          (.kernel ⟨z, x, w⟩)) assignment ->
      ProbabilityTerm.EquivalentAt model
        (.kernel ⟨NodeSet.union y z, x, w⟩)
        (.multiply
          (.kernel ⟨y, x, NodeSet.union z w⟩)
          (.kernel ⟨z, x, w⟩)) assignment

def PathPrimitiveSoundness.compile
    (correct : DSeparationCorrectness G)
    (semantics : PathPrimitiveSoundness G model) :
    LocalPrimitiveSoundness G model where
  doRule := fun assignment application leftSupported rightSupported =>
    semantics.doRule assignment (application.toPath correct)
      leftSupported rightSupported
  marginalization := semantics.marginalization
  conditioning := semantics.conditioning
  chain := semantics.chain

/--
External semantic soundness interface.  The path criterion and its executable
equivalence are separate fields; Lean compiles them into concrete rule soundness.
-/
structure PublishedSoundness (S : ObservedSignature)
    (G : ObservedGraph S) where
  dseparation : DSeparationCorrectness G
  pathPrimitive : forall model : ExactModel S,
    Compatible model G -> PathPrimitiveSoundness G model

def PublishedSoundness.primitive (sound : PublishedSoundness S G)
    (model : ExactModel S) (compatible : Compatible model G) :
    LocalPrimitiveSoundness G model :=
  (sound.pathPrimitive model compatible).compile sound.dseparation

noncomputable def JointIdentificationCertificate.denotational_soundAt
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {q : JointKernelQuery S}
    (sound : PublishedSoundness S G)
    (certificate : JointIdentificationCertificate C q)
    (model : ExactModel S) (member : C.Mem model)
    (assignment : S.Assignment)
    (sourceSupported : q.sourceTerm.SupportedAt model assignment) :
    ProbabilityTerm.EquivalentAt model q.sourceTerm certificate.formula
      assignment :=
  certificate.derivation.denotational_soundAt
    (sound.primitive model (C.mem_compatible model member))
    (certificate.supported model member assignment sourceSupported)

noncomputable def ConditionalIdentificationCertificate.denotational_soundAt
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {q : ConditionalKernelQuery S}
    (sound : PublishedSoundness S G)
    (certificate : ConditionalIdentificationCertificate C q)
    (model : ExactModel S) (member : C.Mem model)
    (assignment : S.Assignment)
    (sourceSupported : q.sourceTerm.SupportedAt model assignment) :
    ProbabilityTerm.EquivalentAt model q.sourceTerm certificate.formula
      assignment :=
  certificate.derivation.denotational_soundAt
    (sound.primitive model (C.mem_compatible model member))
    (certificate.supported model member assignment sourceSupported)

theorem JointIdentificationCertificate.identifiable
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {q : JointKernelQuery S}
    (sound : PublishedSoundness S G)
    (certificate : JointIdentificationCertificate C q) :
    C.identifiable q := by
  intro M N hM hN observational assignment
  let supportedM := q.supportedAt M assignment
  let supportedN := q.supportedAt N assignment
  let sourceToFormulaM := certificate.denotational_soundAt sound M hM
    assignment supportedM
  let sourceToFormulaN := certificate.denotational_soundAt sound N hN
    assignment supportedN
  exact ⟨ProbabilityResult.trans sourceToFormulaM
    (ProbabilityResult.trans
      (ProbabilityTerm.actionFree_invariant M N observational
        certificate.formula certificate.actionFree assignment)
      (ProbabilityResult.symm sourceToFormulaN))⟩

theorem ConditionalIdentificationCertificate.identifiable
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {q : ConditionalKernelQuery S}
    (sound : PublishedSoundness S G)
    (certificate : ConditionalIdentificationCertificate C q) :
    C.conditionalIdentifiable q := by
  intro M N hM hN observational assignment supportedM supportedN
  let sourceToFormulaM := certificate.denotational_soundAt sound M hM
    assignment supportedM
  let sourceToFormulaN := certificate.denotational_soundAt sound N hN
    assignment supportedN
  exact ⟨ProbabilityResult.trans sourceToFormulaM
    (ProbabilityResult.trans
      (ProbabilityTerm.actionFree_invariant M N observational
        certificate.formula certificate.actionFree assignment)
      (ProbabilityResult.symm sourceToFormulaN))⟩

/-- Encoded derivation certificate; the finite derivation data is preserved. -/
structure EncodedJointDerivation {S : ObservedSignature} {G : ObservedGraph S}
    (C : GraphModelClass G) (q : JointKernelQuery S) where
  certificate : JointIdentificationCertificate C q

structure EncodedConditionalDerivation {S : ObservedSignature}
    {G : ObservedGraph S} (C : GraphModelClass G)
    (q : ConditionalKernelQuery S) where
  certificate : ConditionalIdentificationCertificate C q

def transport_joint_completeness
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    (published : PublishedCompleteness C) (q : JointKernelQuery S)
    (h : C.identifiable q) : EncodedJointDerivation C q := by
  constructor
  exact (published.joint_complete q h).compile

def transport_conditional_completeness
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    (published : PublishedCompleteness C) (q : ConditionalKernelQuery S)
    (h : C.conditionalIdentifiable q) :
    EncodedConditionalDerivation C q := by
  constructor
  exact (published.conditional_complete q h).compile

theorem transport_joint_soundness
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    (sound : PublishedSoundness S G) (q : JointKernelQuery S)
    (certificate : EncodedJointDerivation C q) :
    C.identifiable q := by
  exact certificate.certificate.identifiable sound

/-- A sound distributional certificate also identifies each local event. -/
theorem transport_joint_event_soundness
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    (sound : PublishedSoundness S G) (q : InterventionalQuery S)
    (certificate : EncodedJointDerivation C q.kernelQuery) :
    C.eventIdentifiable q :=
  C.kernel_identifiable_implies_event q
    (transport_joint_soundness sound q.kernelQuery certificate)

theorem transport_conditional_soundness
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    (sound : PublishedSoundness S G) (q : ConditionalKernelQuery S)
    (certificate : EncodedConditionalDerivation C q) :
    C.conditionalIdentifiable q := by
  exact certificate.certificate.identifiable sound

theorem transported_joint_iff
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    (complete : PublishedCompleteness C)
    (sound : PublishedSoundness S G) (q : JointKernelQuery S) :
    C.identifiable q <-> Nonempty (EncodedJointDerivation C q) := by
  constructor
  · intro identifiable
    exact ⟨transport_joint_completeness complete q identifiable⟩
  · intro certificate
    rcases certificate with ⟨certificate⟩
    exact transport_joint_soundness sound q certificate

theorem transported_conditional_iff
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    (complete : PublishedCompleteness C)
    (sound : PublishedSoundness S G) (q : ConditionalKernelQuery S) :
    C.conditionalIdentifiable q <->
      Nonempty (EncodedConditionalDerivation C q) := by
  constructor
  · intro identifiable
    exact ⟨transport_conditional_completeness complete q identifiable⟩
  · intro certificate
    rcases certificate with ⟨certificate⟩
    exact transport_conditional_soundness sound q certificate

theorem transport_hedge_failure
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    (published : PublishedCompleteness C) (q : JointKernelQuery S)
    (hedge : HedgeWitness G q) :
    Not (C.identifiable q) :=
  (published.hedge_counterexample q hedge).not_identifiable

/-- The combined finite-rational completeness transport used by the thesis. -/
theorem finite_causal_completeness_transport
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    (published : PublishedCompleteness C) :
    (forall q, C.identifiable q ->
      Nonempty (EncodedJointDerivation C q)) /\
    (forall q, C.conditionalIdentifiable q ->
      Nonempty (EncodedConditionalDerivation C q)) /\
    (forall q, HedgeWitness G q -> Not (C.identifiable q)) := by
  exact ⟨fun q identifiable =>
      ⟨transport_joint_completeness published q identifiable⟩,
    fun q identifiable =>
      ⟨transport_conditional_completeness published q identifiable⟩,
    transport_hedge_failure published⟩

end Causality
end Thesis
