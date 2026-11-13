import Thesis.CausalTransport.Correspondence
import Thesis.Causality.Reductions

namespace Thesis
namespace Causality

open Probability

/-!
Composition of the finite rational CPT construction with the causal transport.

This theorem is deliberately a coherence result.  A constructed model does
not by itself prove identifiability, which quantifies over every compatible
model; the identifiability premise therefore remains explicit.
-/

namespace FiniteRationalCPT

def toTypeTheoreticModel (C : FiniteRationalCPT S) : TypeTheoreticModel S :=
  C.toSCM

theorem toTypeTheoreticModel_compatible (C : FiniteRationalCPT S) :
    TypeTheoreticCompatible C.toSCM.observedGraph
      C.toTypeTheoreticModel := by
  constructor
  · exact C.toSCM.markovian_isCanonicalSemiMarkovian C.toSCM_isMarkovian
  · intro i j
    rfl

def transportJoint (C : FiniteRationalCPT S)
    (published : PublishedCompleteness (GraphModelClass.all C.toSCM.observedGraph))
    (query : JointKernelQuery S)
    (identifiable :
      TypeTheoreticIdentifiable C.toSCM.observedGraph query) :
    EncodedJointDerivation (GraphModelClass.all C.toSCM.observedGraph) query :=
  transport_joint_completeness published query identifiable

def transportConditional (C : FiniteRationalCPT S)
    (published : PublishedCompleteness (GraphModelClass.all C.toSCM.observedGraph))
    (query : ConditionalKernelQuery S)
    (identifiable :
      TypeTheoreticConditionalIdentifiable C.toSCM.observedGraph query) :
    EncodedConditionalDerivation (GraphModelClass.all C.toSCM.observedGraph)
      query :=
  transport_conditional_completeness published query identifiable

theorem enters_finite_transport (C : FiniteRationalCPT S)
    (published : PublishedCompleteness (GraphModelClass.all C.toSCM.observedGraph)) :
    (forall query,
      TypeTheoreticIdentifiable C.toSCM.observedGraph query ->
        Nonempty (EncodedJointDerivation
          (GraphModelClass.all C.toSCM.observedGraph) query)) /\
    (forall query,
      TypeTheoreticConditionalIdentifiable C.toSCM.observedGraph query ->
        Nonempty (EncodedConditionalDerivation
          (GraphModelClass.all C.toSCM.observedGraph) query)) := by
  constructor
  · intro query identifiable
    exact ⟨C.transportJoint published query identifiable⟩
  · intro query identifiable
    exact ⟨C.transportConditional published query identifiable⟩

end FiniteRationalCPT

end Causality
end Thesis
