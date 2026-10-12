import Thesis.CausalTransport.GuardedConditionalSoundness
import Thesis.CausalTransport.HiddenDAGCompleteness

namespace Thesis
namespace Causality

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-!
# The exact all-model boundary of guarded finite hidden-DAG identification

The ambient class below is every original finite hidden-DAG SCM, including
observational zeros and arbitrary finite hidden/private-noise alphabets.
Observed domains stay fixed and value-rich for the countermodel direction.

Guarded joint and conditional failure retain the old programs' exact failure
witnesses.  Their already constructed positive native countermodels also
belong to the larger zero-permitting class, so genuine failure refutes
identifiability in that larger class without any extra regularity premise.
Public termination excludes the unfinished sentinel.

Consequently, all-class semantic identifiability constructively yields the
actual identified expression, its success equation, and the formula-aligned
local-data compilation.  The expression is read by matching the computed
outcome; it is not selected from propositional existence using choice.
The semantic premise is not used to infer a positive displayed denominator.

This is a one-way completeness boundary plus support-qualified compilation,
not an unrestricted zero-class success equivalence.  The returned compilation
constructs support from its primitive `Data`, as established by the native
soundness adapters.  It does NOT prove that `Data` is inhabited in every model
and assignment merely from engine success or all-class identifiability.
In particular it does not inhabit `PublishedCompleteness` for a weakened or
silently relabelled model class.  The established full positive published
theorems remain separate and unchanged.
-/

/-! ## Actual native countermodels in the class allowing zeros -/

/-- Reuse the actual positive original-DAG pair at a guarded joint failure.
Only membership is widened; the records, observed agreement and original
query disagreement are exactly those of the constructed counterexample. -/
noncomputable def identifyGuardedJointKernel_hiddenDAG_failed_counterexample
    (rich : ObservedSignature.ValueRich S) (query : JointKernelQuery S) {failure : IdentificationFail S}
    (result : identifyGuardedJointKernel P.observedGraph query = .failed failure) :
    HiddenDAGCounterexampleIn (HiddenDAGModelClass.all P) query := by
  let pair := identifyJointKernel_hiddenDAG_failed_counterexample rich query
    ((identifyGuardedJointKernel_failed_iff P.observedGraph query failure).mp result)
  exact {
    left := pair.left
    right := pair.right
    left_mem := trivial
    right_mem := trivial
    observationally_equal := pair.observationally_equal
    query_separated := pair.query_separated
  }

/-- Guarded conditional failure separates the unchanged original query's
values on common support.  A missing-support discrepancy is not used as
a counterexample, and the pair is not replaced by a selected model family. -/
noncomputable def identifyGuardedConditionalKernel_hiddenDAG_failed_counterexample
    (rich : ObservedSignature.ValueRich S) (query : ConditionalKernelQuery S) {failure : IdentificationFail S}
    (result : identifyGuardedConditionalKernel P.observedGraph query = .failed failure) :
    HiddenDAGConditionalCounterexampleIn (HiddenDAGModelClass.all P) query := by
  let pair := identifyConditionalKernel_hiddenDAG_failed_counterexample rich query
    ((identifyGuardedConditionalKernel_failed_iff P.observedGraph query failure).mp result)
  exact {
    left := pair.left
    right := pair.right
    left_mem := trivial
    right_mem := trivial
    observationally_equal := pair.observationally_equal
    query_separated := pair.query_separated
  }

/-! ## All-class identifiability yields literal supported-compilation syntax -/

/-- All-class joint identifiability forces an actual guarded success and
returns its inspectable local-data compilation.  Matching the program, not
deciding semantic identifiability, determines the formula in this `Type`.
Support at a model/reference still requires the returned primitive data. -/
noncomputable def identifyGuardedJointKernel_hiddenDAG_completeAtLocalBoundary
    (rich : ObservedSignature.ValueRich S) (query : JointKernelQuery S)
    (identified : (HiddenDAGModelClass.all P).identifiable query) :
    Σ' term : ProbabilityTerm S,
      Σ' _result : identifyGuardedJointKernel P.observedGraph query = .identified term,
        PublishedLocalKernelSuccess P.observedGraph P.observedGraph.dSeparationCorrectness
          query.outcome query.action term := by
  cases result : identifyGuardedJointKernel P.observedGraph query with
  | identified term =>
      exact ⟨term, rfl, identifyGuardedJointKernelLocalCompilation P.observedGraph.dSeparationCorrectness query result⟩
  | failed failure =>
      exact False.elim
        ((identifyGuardedJointKernel_hiddenDAG_failed_counterexample rich query result).not_identifiable identified)
  | unfinished => exact False.elim (identifyGuardedJointKernel_ne_unfinished _ query result)

/-- The analogous constructive conditional boundary uses full original-query
common-support identifiability.  Every prior promotion remains covered by
the failure countermodel and the uniform success compiler, respectively. -/
noncomputable def identifyGuardedConditionalKernel_hiddenDAG_completeAtLocalBoundary
    (rich : ObservedSignature.ValueRich S) (query : ConditionalKernelQuery S)
    (identified : (HiddenDAGModelClass.all P).conditionalIdentifiable query) :
    Σ' term : ProbabilityTerm S,
      Σ' _result : identifyGuardedConditionalKernel P.observedGraph query = .identified term,
        PublishedLocalConditionalSuccess P.observedGraph P.observedGraph.dSeparationCorrectness query term := by
  cases result : identifyGuardedConditionalKernel P.observedGraph query with
  | identified term =>
      exact ⟨term, rfl, identifyGuardedConditionalKernelLocalCompilation P.observedGraph.dSeparationCorrectness query result⟩
  | failed failure =>
      exact False.elim
        ((identifyGuardedConditionalKernel_hiddenDAG_failed_counterexample rich query result).not_identifiable identified)
  | unfinished => exact False.elim (identifyGuardedConditionalKernel_ne_unfinished _ query result)

end Causality
end Thesis
