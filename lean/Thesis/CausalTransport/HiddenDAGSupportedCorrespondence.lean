import Thesis.CausalTransport.HiddenDAGSupportedDomain
import Thesis.CausalTransport.GuardedAdmissibleCertificates
import Thesis.CausalTransport.HiddenDAGCompleteness

namespace Thesis
namespace Causality

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-!
# Supported-zero joint and conditional identification correspondence

`HiddenDAGSupportedDomain` specifies a finite observational representation
and its primitive used-conditional application domain independently of any
engine.  This integration module proves that the actual guarded ID/IDC
engines succeed exactly when such a positive-covered representation exists.
It also constructs their literal-output joint and conditional certificates
and inhabits the joint/conditional/hedge completeness package.

Success uses the proved uniform availability constructors, not assumed
compiler Data.  Coverage of its returned expression is a syntactic
kernel-generated invariant followed by the independent positivity proof;
causal soundness is not used to establish countermodel positivity or coverage.
Failure retains actual positive native counterpairs, which lie in every
candidate positive-covered domain.  Public termination excludes unfinished.

The constructive completeness functions match the computed program outcome.
The existential semantic candidate is unpacked only to prove a contradiction
in a failed branch, never selected into the returned `Type` by choice.
All original finite hidden-DAG records remain quantified, including zeros
and arbitrary finite hidden/private-noise alphabets.

This is the expression-qualified query-level result stated by the semantic
domain.  It does not assert that the returned formula covers every reference
admissible for every alternative representation, or that primitive external
action/source tests alone make all internal conditionals meaningful.  The
verified deterministic-mediator counterexample refutes the latter claim.
-/

/-- The actual joint certificate is still kernel-generated even though
probabilities of its outcomes may be zero.  This is a graph-derivation
syntax invariant, not an appeal to native denotational soundness. -/
theorem PublishedAdmissibleJointCertificate.formula_zeroFree {query : JointKernelQuery S}
    (certificate : PublishedAdmissibleJointCertificate P query) : certificate.formula.ZeroFree :=
  (certificate.derivation.compile P.observedGraph.dSeparationCorrectness).zeroFree_iff.mp trivial

theorem PublishedAdmissibleConditionalCertificate.formula_zeroFree {query : ConditionalKernelQuery S}
    (certificate : PublishedAdmissibleConditionalCertificate P query) : certificate.formula.ZeroFree :=
  (certificate.derivation.compile P.observedGraph.dSeparationCorrectness).zeroFree_iff.mp trivial

/-- Independently proved primitive positivity gives the literal successful
joint output its non-vacuous positive coverage.  Applications outside that
positive subclass are still permitted by the same primitive demand tests. -/
theorem PublishedAdmissibleJointCertificate.positiveCovered {query : JointKernelQuery S}
    (certificate : PublishedAdmissibleJointCertificate P query) :
    HiddenDAGSupportedDomain.PositiveCovered P certificate.formula :=
  HiddenDAGSupportedDomain.positiveCovered_of_zeroFree certificate.formula certificate.formula_zeroFree

theorem PublishedAdmissibleConditionalCertificate.positiveCovered {query : ConditionalKernelQuery S}
    (certificate : PublishedAdmissibleConditionalCertificate P query) :
    HiddenDAGSupportedDomain.PositiveCovered P certificate.formula :=
  HiddenDAGSupportedDomain.positiveCovered_of_zeroFree certificate.formula certificate.formula_zeroFree

/-- The joint certificate computes the original native query on its full
explicit used-conditional domain, not only in positive models.  The complete
support tree is constructed internally from this application's tests. -/
theorem PublishedAdmissibleJointCertificate.representedOn {query : JointKernelQuery S}
    (certificate : PublishedAdmissibleJointCertificate P query) :
    HiddenDAGSupportedDomain.jointRepresentedOn P query certificate.formula := by
  intro model reference admissible
  exact ⟨certificate.soundAt model reference admissible.1 admissible.2⟩

/-- Conditional representation retains the actual original source
conditioner.  Positive displayed support is not treated as source support. -/
theorem PublishedAdmissibleConditionalCertificate.representedOn {query : ConditionalKernelQuery S}
    (certificate : PublishedAdmissibleConditionalCertificate P query) :
    HiddenDAGSupportedDomain.conditionalRepresentedOn P query certificate.formula := by
  intro model reference admissible
  exact ⟨certificate.soundAt model reference admissible.1.1 admissible.1.2 admissible.2⟩

/-- Actual joint success witnesses the engine-independent semantic
identification predicate with the literal returned observational expression. -/
theorem PublishedAdmissibleJointCertificate.supported_identifiable {query : JointKernelQuery S}
    (certificate : PublishedAdmissibleJointCertificate P query) :
    HiddenDAGSupportedDomain.jointIdentifiable P query :=
  ⟨certificate.formula, certificate.actionFree, certificate.positiveCovered, certificate.representedOn⟩

theorem PublishedAdmissibleConditionalCertificate.supported_identifiable {query : ConditionalKernelQuery S}
    (certificate : PublishedAdmissibleConditionalCertificate P query) :
    HiddenDAGSupportedDomain.conditionalIdentifiable P query :=
  ⟨certificate.formula, certificate.actionFree, certificate.positiveCovered, certificate.representedOn⟩

/-- Guarded joint failure keeps its literal native positive counterpair.
Each record meets every positive-covered candidate's primitive demand tests
at every reference, as certified by the independent domain lemmas. -/
noncomputable def identifyGuardedJointKernel_supported_failed_counterexample
    (rich : ObservedSignature.ValueRich S) (query : JointKernelQuery S) {failure : IdentificationFail S}
    (result : identifyGuardedJointKernel P.observedGraph query = .failed failure) :
    HiddenDAGCounterexampleIn (HiddenDAGModelClass.positive P) query :=
  identifyJointKernel_hiddenDAG_failed_counterexample rich query
    ((identifyGuardedJointKernel_failed_iff P.observedGraph query failure).mp result)

/-- Full recursive conditional failure separates the unchanged original
target on common support, including every prior conditioner promotion. -/
noncomputable def identifyGuardedConditionalKernel_supported_failed_counterexample
    (rich : ObservedSignature.ValueRich S) (query : ConditionalKernelQuery S) {failure : IdentificationFail S}
    (result : identifyGuardedConditionalKernel P.observedGraph query = .failed failure) :
    HiddenDAGConditionalCounterexampleIn (HiddenDAGModelClass.positive P) query :=
  identifyConditionalKernel_hiddenDAG_failed_counterexample rich query
    ((identifyGuardedConditionalKernel_failed_iff P.observedGraph query failure).mp result)

/-- Any genuine supported observational representation forces an actual
guarded joint success certificate.  The computed outcome, not the
existential semantic witness, determines its formula and graph derivation. -/
noncomputable def FiniteLatentProjection.supportedAdmissibleJointCompleteness
    (projection : FiniteLatentProjection S) (rich : ObservedSignature.ValueRich S)
    (query : JointKernelQuery S) (identified : HiddenDAGSupportedDomain.jointIdentifiable projection query) :
    PublishedAdmissibleJointCertificate projection query := by
  cases result : identifyGuardedJointKernel projection.observedGraph query with
  | identified term => exact identifyGuardedJointKernel_admissibleCertificate query result
  | failed failure =>
      exact False.elim
        ((identifyGuardedJointKernel_supported_failed_counterexample rich query result).not_supported_identifiable identified)
  | unfinished => exact False.elim (identifyGuardedJointKernel_ne_unfinished _ query result)

/-- Conditional completeness has the same constructive outcome match and
retains the original conditional domain, with no choice of a representative
formula or assumed semantic decision procedure. -/
noncomputable def FiniteLatentProjection.supportedAdmissibleConditionalCompleteness
    (projection : FiniteLatentProjection S) (rich : ObservedSignature.ValueRich S)
    (query : ConditionalKernelQuery S) (identified : HiddenDAGSupportedDomain.conditionalIdentifiable projection query) :
    PublishedAdmissibleConditionalCertificate projection query := by
  cases result : identifyGuardedConditionalKernel projection.observedGraph query with
  | identified term => exact identifyGuardedConditionalKernel_admissibleCertificate query result
  | failed failure =>
      exact False.elim
        ((identifyGuardedConditionalKernel_supported_failed_counterexample rich query result).not_supported_identifiable identified)
  | unfinished => exact False.elim (identifyGuardedConditionalKernel_ne_unfinished _ query result)

namespace HiddenDAGSupportedDomain

/-- Exact query-level supported-zero joint correspondence.  The semantic
side refers only to observational representations and primitive application
tests; the program side retains its actual returned formula. -/
theorem identifyGuardedJointKernel_identifiable_iff (rich : ObservedSignature.ValueRich S) (query : JointKernelQuery S) :
    jointIdentifiable P query ↔ ∃ term, identifyGuardedJointKernel P.observedGraph query = .identified term := by
  constructor
  · intro identified
    let certificate := P.supportedAdmissibleJointCompleteness rich query identified
    exact ⟨certificate.formula, certificate.result⟩
  · rintro ⟨term, result⟩
    exact (identifyGuardedJointKernel_admissibleCertificate query result).supported_identifiable

/-- The corresponding full recursive IDC iff theorem, retaining actual
original causal conditioners at every semantic application. -/
theorem identifyGuardedConditionalKernel_identifiable_iff (rich : ObservedSignature.ValueRich S) (query : ConditionalKernelQuery S) :
    conditionalIdentifiable P query ↔ ∃ term, identifyGuardedConditionalKernel P.observedGraph query = .identified term := by
  constructor
  · intro identified
    let certificate := P.supportedAdmissibleConditionalCompleteness rich query identified
    exact ⟨certificate.formula, certificate.result⟩
  · rintro ⟨term, result⟩
    exact (identifyGuardedConditionalKernel_admissibleCertificate query result).supported_identifiable

end HiddenDAGSupportedDomain

/-- Inhabited supported-zero completeness for all original finite hidden
DAGs.  Positive membership describes the exhibited hedge counterpairs only,
not the semantic identification predicate or certificate application class. -/
structure PublishedSupportedAdmissibleCompleteness (projection : FiniteLatentProjection S) where
  joint_complete : forall query, HiddenDAGSupportedDomain.jointIdentifiable projection query →
    PublishedAdmissibleJointCertificate projection query
  conditional_complete : forall query, HiddenDAGSupportedDomain.conditionalIdentifiable projection query →
    PublishedAdmissibleConditionalCertificate projection query
  hedge_counterexample : forall query, HedgeWitness projection.observedGraph query →
    HiddenDAGCounterexampleIn (HiddenDAGModelClass.positive projection) query

/-- Assemble every supported-zero completeness field with actual native
certificates and countermodel records.  Only the established observed
value-richness hypothesis is required for the completeness direction. -/
noncomputable def FiniteLatentProjection.publishedSupportedAdmissibleCompleteness
    (projection : FiniteLatentProjection S) (rich : ObservedSignature.ValueRich S) :
    PublishedSupportedAdmissibleCompleteness projection where
  joint_complete := projection.supportedAdmissibleJointCompleteness rich
  conditional_complete := projection.supportedAdmissibleConditionalCompleteness rich
  hedge_counterexample := fun _ witness => hedge_hiddenDAG_counterexample rich witness

end Causality
end Thesis
