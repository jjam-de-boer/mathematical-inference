import Thesis.CausalTransport.HiddenDAGModel

namespace Thesis
namespace Causality

open Probability

/-!
The general-hidden-DAG bridge is intentionally an identifiability theorem,
not an individual-model distribution equivalence.  Latent projection can
replace a general hidden DAG by an observed ADMG for identification questions;
it does not in general turn each multi-child hidden cause into independent
pairwise hidden roots while preserving that model's full distribution.
-/

/--
Finite interventional semantics for the models represented by one full hidden
DAG.  Distributions remain finite rational records, so identifiability below
has the same extensional meaning as in the canonical semi-Markovian class.
-/
structure HiddenDAGModelClass.{u} (S : ObservedSignature.{u})
    (projection : FiniteLatentProjection S) where
  Model : Type (u + 1)
  model_nonempty : Nonempty Model
  generated : Model -> FiniteHiddenDAGSCM S projection

namespace HiddenDAGModelClass

def observationalProb (H : HiddenDAGModelClass S P) (M : H.Model)
    (event : S.Assignment -> Bool) : QProb :=
  (H.generated M).observationalValue event

def interventionalProb (H : HiddenDAGModelClass S P) (M : H.Model)
    (intervention : HardIntervention S)
    (event : S.Assignment -> Bool) : QProb :=
  (H.generated M).interventionalValue intervention event

def ObservationallyEquivalent (H : HiddenDAGModelClass S P)
    (left right : H.Model) : Prop :=
  forall event, QProb.Equiv
    (H.observationalProb left event)
    (H.observationalProb right event)

def kernelResult (H : HiddenDAGModelClass S P) (M : H.Model)
    (kernel : Kernel S) (reference : S.Assignment) :
    ProbabilityResult.Result :=
  let generated := H.generated M
  let distribution :=
    if kernel.hasAction then
      generated.interventionalDist
        { value := kernel.intervention reference }
    else
      generated.observationalDist
  let denominator := distribution.probVal (kernel.conditionEvent reference)
  let numerator := distribution.probVal (kernel.numeratorEvent reference)
  ProbabilityResult.divide (some numerator) (some denominator)

def KernelValueEquivalent (H : HiddenDAGModelClass S P)
    (left right : H.Model) (kernel : Kernel S) : Prop :=
  forall assignment,
    Nonempty (ProbabilityResult.Equivalent
      (H.kernelResult left kernel assignment)
      (H.kernelResult right kernel assignment))

def KernelSupported (H : HiddenDAGModelClass S P)
    (model : H.Model) (kernel : Kernel S) : Prop :=
  Nonempty (forall assignment, Sigma fun value =>
    ProbabilityResult.Equivalent
      (H.kernelResult model kernel assignment) (some value))

def JointIdentifiable (H : HiddenDAGModelClass S P)
    (query : JointKernelQuery S) : Prop :=
  forall left right : H.Model,
    H.ObservationallyEquivalent left right ->
      H.KernelValueEquivalent left right
        { outcome := query.outcome
          action := query.action
          condition := NodeSet.empty }

def ConditionalIdentifiable (H : HiddenDAGModelClass S P)
    (query : ConditionalKernelQuery S) : Prop :=
  (forall model : H.Model,
      H.KernelSupported model
        { outcome := query.outcome
          action := query.action
          condition := query.condition }) /\
    forall left right : H.Model,
      H.ObservationallyEquivalent left right ->
        H.KernelValueEquivalent left right
          { outcome := query.outcome
            action := query.action
            condition := query.condition }

end HiddenDAGModelClass

/--
Exact external interface to the latent-projection theorem used in the
completeness literature.  Its conclusion is preservation of identification
for the whole model class under the projected ADMG.
-/
structure PublishedLatentProjection
    (P : FiniteLatentProjection S) (H : HiddenDAGModelClass S P) where
  joint_identifiable_iff : forall query,
    H.JointIdentifiable query <->
      ClassicalIdentifiable P.observedGraph query
  conditional_identifiable_iff : forall query,
    H.ConditionalIdentifiable query <->
      ClassicalConditionalIdentifiable P.observedGraph query

theorem hiddenDAG_joint_transport
    {S : ObservedSignature} {P : FiniteLatentProjection S}
    {H : HiddenDAGModelClass S P}
    (published : PublishedLatentProjection P H)
    (query : JointKernelQuery S) :
    H.JointIdentifiable query <->
      TypeTheoreticIdentifiable P.observedGraph query := by
  exact (published.joint_identifiable_iff query).trans
    (identifiable_iff P.observedGraph query)

theorem hiddenDAG_conditional_transport
    {S : ObservedSignature} {P : FiniteLatentProjection S}
    {H : HiddenDAGModelClass S P}
    (published : PublishedLatentProjection P H)
    (query : ConditionalKernelQuery S) :
    H.ConditionalIdentifiable query <->
      TypeTheoreticConditionalIdentifiable P.observedGraph query := by
  exact (published.conditional_identifiable_iff query).trans
    (conditional_identifiable_iff P.observedGraph query)

end Causality
end Thesis
