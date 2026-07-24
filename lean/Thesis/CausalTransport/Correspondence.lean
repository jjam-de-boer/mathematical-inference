import Thesis.CausalTransport.Certificates

namespace Thesis
namespace Causality

open Probability

/-!
External completeness and soundness interfaces with checked certificate transport.

The published identification theorem is deliberately represented by explicit
parameters.  Internal query semantics and identifiability live in
`Thesis.Causality.Identification`.

This file is the generic, graph-indexed boundary. It does not depend on the
finite source-table encoding: `FiniteSource` specializes these interfaces only
after independently defining source evaluation and its preservation map. A
reader looking for what Lean assumes should begin with `PublishedCompleteness`
and `PublishedSoundness`; a reader looking for what Lean proves should follow
the certificate compilation and transport theorems below.
-/

/-! ## Explicit external theorem interface and checked transport -/

/-!
The generic records in `Certificates` are implementation cores.  The following
public structures deliberately retain their original fields, constructors, and
recursors so imports predating this refactor remain source-compatible.
-/

structure JointIdentificationCertificate (G : ObservedGraph S)
    (q : JointKernelQuery S) where
  formula : ProbabilityTerm S
  actionFree : formula.ActionFree
  derivation : DoCalculusDerivation G q.sourceTerm formula
  supported : forall model : ExactModel S, (compatible : Compatible model G) ->
    forall assignment, q.sourceTerm.SupportedAt model assignment ->
      LocalDerivationSupport model assignment derivation

structure ConditionalIdentificationCertificate (G : ObservedGraph S)
    (q : ConditionalKernelQuery S) where
  formula : ProbabilityTerm S
  actionFree : formula.ActionFree
  derivation : DoCalculusDerivation G q.sourceTerm formula
  supported : forall model : ExactModel S, (compatible : Compatible model G) ->
    forall assignment, q.sourceTerm.SupportedAt model assignment ->
      LocalDerivationSupport model assignment derivation

structure PublishedJointCertificate (G : ObservedGraph S)
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S) where
  formula : ProbabilityTerm S
  actionFree : formula.ActionFree
  derivation : PathDoCalculusDerivation G q.sourceTerm formula
  supported : forall model : ExactModel S, (compatible : Compatible model G) ->
    forall assignment, q.sourceTerm.SupportedAt model assignment ->
      LocalDerivationSupport model assignment (derivation.compile correct)

structure PublishedConditionalCertificate (G : ObservedGraph S)
    (correct : DSeparationCorrectness G) (q : ConditionalKernelQuery S) where
  formula : ProbabilityTerm S
  actionFree : formula.ActionFree
  derivation : PathDoCalculusDerivation G q.sourceTerm formula
  supported : forall model : ExactModel S, (compatible : Compatible model G) ->
    forall assignment, q.sourceTerm.SupportedAt model assignment ->
      LocalDerivationSupport model assignment (derivation.compile correct)

def JointIdentificationCertificate.toGeneric
    (certificate : JointIdentificationCertificate G q) :
    IdentificationCertificate G q.sourceTerm where
  formula := certificate.formula
  actionFree := certificate.actionFree
  derivation := certificate.derivation
  supported := certificate.supported

def ConditionalIdentificationCertificate.toGeneric
    (certificate : ConditionalIdentificationCertificate G q) :
    IdentificationCertificate G q.sourceTerm where
  formula := certificate.formula
  actionFree := certificate.actionFree
  derivation := certificate.derivation
  supported := certificate.supported

def JointIdentificationCertificate.ofGeneric
    (certificate : IdentificationCertificate G q.sourceTerm) :
    JointIdentificationCertificate G q where
  formula := certificate.formula
  actionFree := certificate.actionFree
  derivation := certificate.derivation
  supported := certificate.supported

def ConditionalIdentificationCertificate.ofGeneric
    (certificate : IdentificationCertificate G q.sourceTerm) :
    ConditionalIdentificationCertificate G q where
  formula := certificate.formula
  actionFree := certificate.actionFree
  derivation := certificate.derivation
  supported := certificate.supported

def PublishedJointCertificate.toGeneric
    (certificate : PublishedJointCertificate G correct q) :
    PublishedIdentificationCertificate G correct q.sourceTerm where
  formula := certificate.formula
  actionFree := certificate.actionFree
  derivation := certificate.derivation
  supported := certificate.supported

def PublishedConditionalCertificate.toGeneric
    (certificate : PublishedConditionalCertificate G correct q) :
    PublishedIdentificationCertificate G correct q.sourceTerm where
  formula := certificate.formula
  actionFree := certificate.actionFree
  derivation := certificate.derivation
  supported := certificate.supported

def PublishedJointCertificate.compile
    (certificate : PublishedJointCertificate G correct q) :
    JointIdentificationCertificate G q :=
  JointIdentificationCertificate.ofGeneric certificate.toGeneric.compile

def PublishedConditionalCertificate.compile
    (certificate : PublishedConditionalCertificate G correct q) :
    ConditionalIdentificationCertificate G q :=
  ConditionalIdentificationCertificate.ofGeneric certificate.toGeneric.compile

/--
Formal interface to the published classical result.  An inhabitant is passed
to the transport theorem explicitly; no axiom is declared in this module.
Unlike an arbitrary `Derivable` predicate, each completeness field must return
an inspectable do-calculus and probability-algebra derivation.
-/
structure PublishedCompleteness (S : ObservedSignature)
    (G : ObservedGraph S) where
  dseparation : DSeparationCorrectness G
  joint_complete : forall q,
    Identifiable G q ->
      PublishedJointCertificate G dseparation q
  conditional_complete : forall q,
    ConditionalIdentifiable G q ->
      PublishedConditionalCertificate G dseparation q
  hedge_counterexample : forall q,
    HedgeWitness G q -> Counterexample G q

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
    (sound : PublishedSoundness S G)
    (certificate : JointIdentificationCertificate G q)
    (model : ExactModel S) (compatible : Compatible model G)
    (assignment : S.Assignment)
    (sourceSupported : q.sourceTerm.SupportedAt model assignment) :
    ProbabilityTerm.EquivalentAt model q.sourceTerm certificate.formula
      assignment :=
  certificate.derivation.denotational_soundAt
    (sound.primitive model compatible)
    (certificate.supported model compatible assignment sourceSupported)

noncomputable def ConditionalIdentificationCertificate.denotational_soundAt
    (sound : PublishedSoundness S G)
    (certificate : ConditionalIdentificationCertificate G q)
    (model : ExactModel S) (compatible : Compatible model G)
    (assignment : S.Assignment)
    (sourceSupported : q.sourceTerm.SupportedAt model assignment) :
    ProbabilityTerm.EquivalentAt model q.sourceTerm certificate.formula
      assignment :=
  certificate.derivation.denotational_soundAt
    (sound.primitive model compatible)
    (certificate.supported model compatible assignment sourceSupported)

theorem JointIdentificationCertificate.identifiable
    (sound : PublishedSoundness S G)
    (certificate : JointIdentificationCertificate G q) :
    Identifiable G q := by
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
    (sound : PublishedSoundness S G)
    (certificate : ConditionalIdentificationCertificate G q) :
    ConditionalIdentifiable G q := by
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
structure EncodedJointDerivation
    (G : ObservedGraph S) (q : JointKernelQuery S) where
  classical : JointIdentificationCertificate G q

structure EncodedConditionalDerivation
    (G : ObservedGraph S) (q : ConditionalKernelQuery S) where
  classical : ConditionalIdentificationCertificate G q

def transport_joint_completeness
    (P : PublishedCompleteness S G) (q : JointKernelQuery S)
    (h : TypeTheoreticIdentifiable G q) : EncodedJointDerivation G q := by
  constructor
  exact (P.joint_complete q h).compile

def transport_conditional_completeness
    (P : PublishedCompleteness S G) (q : ConditionalKernelQuery S)
    (h : TypeTheoreticConditionalIdentifiable G q) :
    EncodedConditionalDerivation G q := by
  constructor
  exact (P.conditional_complete q h).compile

theorem transport_joint_soundness
    (P : PublishedSoundness S G) (q : JointKernelQuery S)
    (certificate : EncodedJointDerivation G q) :
    TypeTheoreticIdentifiable G q := by
  exact certificate.classical.identifiable P

/-- A sound distributional certificate also identifies each local event. -/
theorem transport_joint_event_soundness
    (P : PublishedSoundness S G) (q : InterventionalQuery S)
    (certificate : EncodedJointDerivation G q.kernelQuery) :
    TypeTheoreticEventIdentifiable G q :=
  typeTheoretic_kernel_identifiable_implies_event G q
    (transport_joint_soundness P q.kernelQuery certificate)

theorem transport_conditional_soundness
    (P : PublishedSoundness S G) (q : ConditionalKernelQuery S)
    (certificate : EncodedConditionalDerivation G q) :
    TypeTheoreticConditionalIdentifiable G q := by
  exact certificate.classical.identifiable P

theorem transported_joint_iff
    (complete : PublishedCompleteness S G)
    (sound : PublishedSoundness S G) (q : JointKernelQuery S) :
    TypeTheoreticIdentifiable G q <-> Nonempty (EncodedJointDerivation G q) := by
  constructor
  · intro identifiable
    exact ⟨transport_joint_completeness complete q identifiable⟩
  · intro certificate
    rcases certificate with ⟨certificate⟩
    exact transport_joint_soundness sound q certificate

theorem transported_conditional_iff
    (complete : PublishedCompleteness S G)
    (sound : PublishedSoundness S G) (q : ConditionalKernelQuery S) :
    TypeTheoreticConditionalIdentifiable G q <->
      Nonempty (EncodedConditionalDerivation G q) := by
  constructor
  · intro identifiable
    exact ⟨transport_conditional_completeness complete q identifiable⟩
  · intro certificate
    rcases certificate with ⟨certificate⟩
    exact transport_conditional_soundness sound q certificate

theorem transport_hedge_failure
    (P : PublishedCompleteness S G) (q : JointKernelQuery S)
    (hedge : HedgeWitness G q) :
    Not (TypeTheoreticIdentifiable G q) := by
  let C := P.hedge_counterexample q hedge
  intro h
  exact C.query_separated
    (h C.left C.right C.left_compatible C.right_compatible
      C.observationally_equal)

/-- The combined finite-rational completeness transport used by the thesis. -/
theorem finite_causal_completeness_transport
    (P : PublishedCompleteness S G) :
    (forall q, TypeTheoreticIdentifiable G q ->
      Nonempty (EncodedJointDerivation G q)) /\
    (forall q, TypeTheoreticConditionalIdentifiable G q ->
      Nonempty (EncodedConditionalDerivation G q)) /\
    (forall q, HedgeWitness G q -> Not (TypeTheoreticIdentifiable G q)) := by
  exact ⟨fun q identifiable =>
      ⟨transport_joint_completeness P q identifiable⟩,
    fun q identifiable =>
      ⟨transport_conditional_completeness P q identifiable⟩,
    transport_hedge_failure P⟩

end Causality
end Thesis
