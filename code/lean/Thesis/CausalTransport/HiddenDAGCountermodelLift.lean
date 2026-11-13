import Thesis.CausalTransport.HiddenDAGModelClass
import Thesis.CausalTransport.HiddenDAGProbability

namespace Thesis
namespace Causality

open Probability

/-!
# Lift actual canonical countermodels into the original finite hidden DAG

Every input pair here is an existing positive projected-graph counterexample,
with actual finite equations and independent root records.  Each member is
realized by the internally constructed original-DAG relay model.  Complete
probability preservation keeps their entire observed laws equal; partial
kernel preservation transports a purported native agreement back to the
original separated values.

Conditional separation is on common support.  The original constructive
support witnesses are explicitly transported into the two native models;
a difference consisting only of missing support is never used as a gap.
Strict observed positivity is preserved by intrinsic probability transfer,
not by importing denotational soundness or treating a collapse as canonical.

The resulting records inhabit the class of all positive finite SCMs on the
given original hidden graph.  Their hidden and private-noise alphabets may
differ, and may have any finite sizes.  No root-placement readiness, shared
switch condition, selected-family equivalence or countermodel interface is
an additional premise.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-- Preserve the whole observed agreement of two compatible source models,
not merely agreement of a chosen event or of coordinate marginals. -/
private theorem realization_observationalAgreement (left right : ExactModel S)
    (leftCompatible : Compatible left P.observedGraph)
    (rightCompatible : Compatible right P.observedGraph)
    (equal : ObservationallyEquivalent left right) :
    (left.toHiddenDAGSCM leftCompatible).ObservationalAgreement
      (right.toHiddenDAGSCM rightCompatible) := by
  intro event
  exact QProb.equiv_trans (left.toHiddenDAGSCM_observationalValue leftCompatible event)
    (QProb.equiv_trans (equal event)
      (QProb.equiv_symm (right.toHiddenDAGSCM_observationalValue rightCompatible event)))

/-- Realize an entire positive joint countermodel pair inside the original
hidden DAG.  The separated query is unchanged; no auxiliary numerator query
or specially chosen original-DAG model is substituted. -/
noncomputable def CounterexampleIn.toHiddenDAG {query : JointKernelQuery S}
    (pair : CounterexampleIn (GraphModelClass.positive P.observedGraph) query) :
    HiddenDAGCounterexampleIn (HiddenDAGModelClass.positive P) query where
  left := pair.left.toHiddenDAGSCM pair.left_mem.1
  right := pair.right.toHiddenDAGSCM pair.right_mem.1
  left_mem := pair.left.toHiddenDAGSCM_observational_num_pos pair.left_mem.1 pair.left_mem.2
  right_mem := pair.right.toHiddenDAGSCM_observational_num_pos pair.right_mem.1 pair.right_mem.2
  observationally_equal := realization_observationalAgreement pair.left pair.right
    pair.left_mem.1 pair.right_mem.1 pair.observationally_equal
  query_separated := by
    intro nativeAgreement
    apply pair.query_separated
    intro assignment
    rcases nativeAgreement assignment with ⟨nativeEquivalent⟩
    change Nonempty (ProbabilityResult.Equivalent
      (query.operationKernel.denote pair.left assignment)
      (query.operationKernel.denote pair.right assignment))
    exact ⟨ProbabilityResult.trans
      (ProbabilityResult.symm (pair.left.toHiddenDAGSCM_kernelDenote pair.left_mem.1
        query.operationKernel assignment))
      (ProbabilityResult.trans nativeEquivalent
        (pair.right.toHiddenDAGSCM_kernelDenote pair.right_mem.1 query.operationKernel assignment))⟩

/-- Realize a positive conditional countermodel pair, preserving genuine
common-support value separation.  The two original support values are moved
as explicit data through partial-result equivalence, not chosen anew. -/
noncomputable def ConditionalCounterexampleIn.toHiddenDAG {query : ConditionalKernelQuery S}
    (pair : ConditionalCounterexampleIn (GraphModelClass.positive P.observedGraph) query) :
    HiddenDAGConditionalCounterexampleIn (HiddenDAGModelClass.positive P) query where
  left := pair.left.toHiddenDAGSCM pair.left_mem.1
  right := pair.right.toHiddenDAGSCM pair.right_mem.1
  left_mem := pair.left.toHiddenDAGSCM_observational_num_pos pair.left_mem.1 pair.left_mem.2
  right_mem := pair.right.toHiddenDAGSCM_observational_num_pos pair.right_mem.1 pair.right_mem.2
  observationally_equal := realization_observationalAgreement pair.left pair.right
    pair.left_mem.1 pair.right_mem.1 pair.observationally_equal
  query_separated := by
    intro nativeAgreement
    apply pair.query_separated
    intro assignment leftSupport rightSupport
    have leftPreserved := pair.left.toHiddenDAGSCM_kernelDenote pair.left_mem.1
      query.operationKernel assignment
    have rightPreserved := pair.right.toHiddenDAGSCM_kernelDenote pair.right_mem.1
      query.operationKernel assignment
    have nativeLeftSupport := ProbabilityResult.Supported.transport
      (ProbabilityResult.symm leftPreserved) leftSupport
    have nativeRightSupport := ProbabilityResult.Supported.transport
      (ProbabilityResult.symm rightPreserved) rightSupport
    rcases nativeAgreement assignment nativeLeftSupport nativeRightSupport with ⟨nativeEquivalent⟩
    exact ⟨ProbabilityResult.trans (ProbabilityResult.symm leftPreserved)
      (ProbabilityResult.trans nativeEquivalent rightPreserved)⟩

end Causality
end Thesis
