import Thesis.CausalTransport.HiddenDAGAdmissibleDomain
import Thesis.CausalTransport.GuardedAdmissibleCertificates
import Thesis.CausalTransport.HiddenDAGCompleteness

namespace Thesis
namespace Causality

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-!
# Constructive completeness at the primitive native admissible-query boundary

The semantic premise is the independently specified original-query domain
from `HiddenDAGAdmissibleDomain`, not a condition that the program succeeds
or that its printed expression is defined.  Every actual guarded failure
has the unchanged positive native countermodels, whose primitive action
and causal-source admissibility are now certified at every reference.
Public termination excludes the unfinished result.

Matching the actual outcome therefore constructs an inhabited joint or
conditional certificate from semantic primitive-domain identifiability.
Its recursive support tree is already built uniformly from primitive
used-conditional tests by `GuardedAdmissibleCertificates`.  Neither a formula,
model nor derivation is selected from propositional existence using choice.

The package deliberately records the direction proved here.  A certificate
interprets success where its used conditionals are admissible, while the
semantic premise here uses only the independent primitive query boundary.
Thus this is not a success iff identifiability claim on that whole boundary,
nor a declaration that those external query tests guarantee all internal
quotients.  The final paper-scope correspondence must still account for that
used-conditional application qualification rather than silently drop it.
-/

/-- Every actual guarded joint failure supplies an original-query pair
whose fixed action values overlap on every supported parent context. -/
noncomputable def identifyGuardedJointKernel_admissible_failed_counterexample
    (rich : ObservedSignature.ValueRich S) (query : JointKernelQuery S) {failure : IdentificationFail S}
    (result : identifyGuardedJointKernel P.observedGraph query = .failed failure) :
    HiddenDAGAdmissibleJointCounterexample P query :=
  (identifyJointKernel_hiddenDAG_failed_counterexample rich query
    ((identifyGuardedJointKernel_failed_iff P.observedGraph query failure).mp result)).toAdmissible

/-- Recursive conditional failure separates the unchanged target on common
support.  Both exhibited native records meet the original action and causal
conditioner tests; all preceding promotions are already included. -/
noncomputable def identifyGuardedConditionalKernel_admissible_failed_counterexample
    (rich : ObservedSignature.ValueRich S) (query : ConditionalKernelQuery S) {failure : IdentificationFail S}
    (result : identifyGuardedConditionalKernel P.observedGraph query = .failed failure) :
    HiddenDAGAdmissibleConditionalCounterexample P query :=
  (identifyConditionalKernel_hiddenDAG_failed_counterexample rich query
    ((identifyGuardedConditionalKernel_failed_iff P.observedGraph query failure).mp result)).toAdmissible

/-- Primitive-domain joint identification yields the actual guarded success
certificate.  Its formula, graph derivation and uniform zero-permitting
support constructor are read from the computed outcome, not assumed. -/
noncomputable def FiniteLatentProjection.primitiveAdmissibleJointCompleteness
    (projection : FiniteLatentProjection S) (rich : ObservedSignature.ValueRich S)
    (query : JointKernelQuery S)
    (identified : HiddenDAGAdmissibleDomain.jointIdentifiable projection query) :
    PublishedAdmissibleJointCertificate projection query := by
  cases result : identifyGuardedJointKernel projection.observedGraph query with
  | identified term => exact identifyGuardedJointKernel_admissibleCertificate query result
  | failed failure =>
      exact False.elim
        ((identifyGuardedJointKernel_admissible_failed_counterexample rich query result).not_identifiable identified)
  | unfinished => exact False.elim (identifyGuardedJointKernel_ne_unfinished _ query result)

/-- The conditional completeness constructor uses the full original-query
domain.  No promotion-count bound, externally supplied support tree or
semantic positivity assumption on a printed denominator is introduced. -/
noncomputable def FiniteLatentProjection.primitiveAdmissibleConditionalCompleteness
    (projection : FiniteLatentProjection S) (rich : ObservedSignature.ValueRich S)
    (query : ConditionalKernelQuery S)
    (identified : HiddenDAGAdmissibleDomain.conditionalIdentifiable projection query) :
    PublishedAdmissibleConditionalCertificate projection query := by
  cases result : identifyGuardedConditionalKernel projection.observedGraph query with
  | identified term => exact identifyGuardedConditionalKernel_admissibleCertificate query result
  | failed failure =>
      exact False.elim
        ((identifyGuardedConditionalKernel_admissible_failed_counterexample rich query result).not_identifiable identified)
  | unfinished => exact False.elim (identifyGuardedConditionalKernel_ne_unfinished _ query result)

/-- A projected hedge supplies an actual admissible pair on the supplied
original hidden DAG.  Arbitrary finite relay and private-noise alphabets are
constructed by the existing reverse realization, not fixed by this boundary. -/
noncomputable def hedge_hiddenDAG_admissible_counterexample (rich : ObservedSignature.ValueRich S)
    {query : JointKernelQuery S} (witness : HedgeWitness P.observedGraph query) :
    HiddenDAGAdmissibleJointCounterexample P query :=
  (hedge_hiddenDAG_counterexample rich witness).toAdmissible

/-- The one-way completeness package for the independent primitive query
domain.  Certificates retain their explicit used-conditional application
tests; this type does not assert a stronger zero-class success equivalence.
Every field is inhabited by the constructor below, not imported externally. -/
structure PrimitiveAdmissibleCompleteness (projection : FiniteLatentProjection S) where
  joint_complete : forall query,
    HiddenDAGAdmissibleDomain.jointIdentifiable projection query →
      PublishedAdmissibleJointCertificate projection query
  conditional_complete : forall query,
    HiddenDAGAdmissibleDomain.conditionalIdentifiable projection query →
      PublishedAdmissibleConditionalCertificate projection query
  hedge_counterexample : forall query, HedgeWitness projection.observedGraph query →
    HiddenDAGAdmissibleJointCounterexample projection query

/-- Assemble the proved joint, conditional and hedge fields on every
value-rich finite observed signature.  The semantic premises quantify over
all actual native records, including observed zeros, and all admissible
references.  Global positivity is used only for the exhibited counterpairs. -/
noncomputable def FiniteLatentProjection.primitiveAdmissibleCompleteness
    (projection : FiniteLatentProjection S) (rich : ObservedSignature.ValueRich S) :
    PrimitiveAdmissibleCompleteness projection where
  joint_complete := projection.primitiveAdmissibleJointCompleteness rich
  conditional_complete := projection.primitiveAdmissibleConditionalCompleteness rich
  hedge_counterexample := fun _ witness => hedge_hiddenDAG_admissible_counterexample rich witness

end Causality
end Thesis
