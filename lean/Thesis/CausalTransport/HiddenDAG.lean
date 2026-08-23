import Thesis.CausalTransport.HiddenDAGModel

namespace Thesis
namespace Causality

open Probability

/-!
The explicit external interface relates identifiability in a selected
hidden-DAG family to identifiability in its projected ADMG. This module neither
asserts individual-model distribution equivalence nor constructs the published
bridge. In particular, it does not turn each multi-child hidden cause into
independent pairwise hidden roots while preserving that model's full
distribution.
-/

/--
A selected nonempty family of finite SCMs over one full hidden DAG.  The
`Model` index is the domain of the identifiability quantifiers below, and
`semantics` assigns executable finite rational semantics to each member.  The
family is not required to exhaust every `FiniteHiddenDAGSCM` record over the
same projection.
-/
structure HiddenDAGModelFamily.{u} (S : ObservedSignature.{u})
    (projection : FiniteLatentProjection S) where
  Model : Type (u + 1)
  model_nonempty : Nonempty Model
  semantics : Model -> FiniteHiddenDAGSCM S projection

namespace HiddenDAGModelFamily

def observationalProb (H : HiddenDAGModelFamily S P) (M : H.Model)
    (event : S.Assignment -> Bool) : QProb :=
  (H.semantics M).observationalValue event

def interventionalProb (H : HiddenDAGModelFamily S P) (M : H.Model)
    (intervention : HardIntervention S)
    (event : S.Assignment -> Bool) : QProb :=
  (H.semantics M).interventionalValue intervention event

def ObservationallyEquivalent (H : HiddenDAGModelFamily S P)
    (left right : H.Model) : Prop :=
  forall event, QProb.Equiv
    (H.observationalProb left event)
    (H.observationalProb right event)

def kernelResult (H : HiddenDAGModelFamily S P) (M : H.Model)
    (kernel : Kernel S) (reference : S.Assignment) :
    ProbabilityResult.Result :=
  let model := H.semantics M
  let distribution :=
    if kernel.hasAction then
      model.interventionalDist
        { value := kernel.intervention reference }
    else
      model.observationalDist
  let denominator := distribution.probVal (kernel.conditionEvent reference)
  let numerator := distribution.probVal (kernel.numeratorEvent reference)
  ProbabilityResult.divide (some numerator) (some denominator)

/-- Full equivalence of two partial kernel results at every assignment. -/
def KernelResultEquivalent (H : HiddenDAGModelFamily S P)
    (left right : H.Model) (kernel : Kernel S) : Prop :=
  forall assignment,
    Nonempty (ProbabilityResult.Equivalent
      (H.kernelResult left kernel assignment)
      (H.kernelResult right kernel assignment))

/-- Evidence that one kernel result is defined at one assignment. -/
def KernelSupportedAt (H : HiddenDAGModelFamily S P)
    (model : H.Model) (kernel : Kernel S) (assignment : S.Assignment) : Type :=
  Sigma fun value => ProbabilityResult.Equivalent
    (H.kernelResult model kernel assignment) (some value)

/-- Agreement of two kernel values wherever both models support them. -/
def KernelAgreesOnCommonSupport (H : HiddenDAGModelFamily S P)
    (left right : H.Model) (kernel : Kernel S) : Prop :=
  forall assignment,
    H.KernelSupportedAt left kernel assignment ->
    H.KernelSupportedAt right kernel assignment ->
    Nonempty (ProbabilityResult.Equivalent
      (H.kernelResult left kernel assignment)
      (H.kernelResult right kernel assignment))

/-- Full partial-result equivalence entails agreement on common support. -/
theorem KernelResultEquivalent.agreesOnCommonSupport
    {H : HiddenDAGModelFamily S P} {left right : H.Model}
    {kernel : Kernel S}
    (equivalent : H.KernelResultEquivalent left right kernel) :
    H.KernelAgreesOnCommonSupport left right kernel := by
  intro assignment _ _
  exact equivalent assignment

/-- Constructive support for one kernel at every assignment. -/
def KernelSupportedEverywhere (H : HiddenDAGModelFamily S P)
    (model : H.Model) (kernel : Kernel S) : Prop :=
  Nonempty (forall assignment, H.KernelSupportedAt model kernel assignment)

/-- Joint-kernel identifiability within the selected hidden-DAG family. -/
def JointIdentifiable (H : HiddenDAGModelFamily S P)
    (query : JointKernelQuery S) : Prop :=
  forall left right : H.Model,
    H.ObservationallyEquivalent left right ->
      H.KernelResultEquivalent left right query.operationKernel

/--
Conditional-kernel identifiability within the selected family, comparing
values only at assignments supported by both models.  It neither requires
global support nor asserts that support domains coincide.
-/
def ConditionalIdentifiable (H : HiddenDAGModelFamily S P)
    (query : ConditionalKernelQuery S) : Prop :=
  forall left right : H.Model,
    H.ObservationallyEquivalent left right ->
      H.KernelAgreesOnCommonSupport left right query.operationKernel

/--
The stronger uniform-support formulation: every model supports the query at
every assignment, and observationally equivalent models have fully equivalent
partial results everywhere.
-/
def UniformConditionalIdentifiable (H : HiddenDAGModelFamily S P)
    (query : ConditionalKernelQuery S) : Prop :=
  (forall model : H.Model,
      H.KernelSupportedEverywhere model query.operationKernel) /\
    forall left right : H.Model,
      H.ObservationallyEquivalent left right ->
        H.KernelResultEquivalent left right query.operationKernel

/-- Uniform conditional identifiability entails common-support identifiability. -/
theorem UniformConditionalIdentifiable.conditionalIdentifiable
    {H : HiddenDAGModelFamily S P} {query : ConditionalKernelQuery S}
    (identifiable : H.UniformConditionalIdentifiable query) :
    H.ConditionalIdentifiable query := by
  intro left right observational
  exact (identifiable.2 left right observational).agreesOnCommonSupport

/--
Uniform conditional identifiability is exactly global support together with
common-support identifiability.
-/
theorem uniformConditionalIdentifiable_iff
    (H : HiddenDAGModelFamily S P) (query : ConditionalKernelQuery S) :
    H.UniformConditionalIdentifiable query <->
      (forall model : H.Model,
        H.KernelSupportedEverywhere model query.operationKernel) /\
      H.ConditionalIdentifiable query := by
  constructor
  · intro identifiable
    exact ⟨identifiable.1, identifiable.conditionalIdentifiable⟩
  · rintro ⟨supported, identifiable⟩
    refine ⟨supported, ?_⟩
    intro left right observational assignment
    rcases supported left with ⟨leftSupported⟩
    rcases supported right with ⟨rightSupported⟩
    exact identifiable left right observational assignment
      (leftSupported assignment) (rightSupported assignment)

end HiddenDAGModelFamily

/--
External interface to the latent-projection theorem used in the completeness
literature.  Its fields explicitly assume preservation of joint and
common-support conditional identification between the selected hidden-DAG
family and the projected ADMG class.  This module does not construct an
inhabitant of the interface.
-/
structure PublishedLatentProjection
    (P : FiniteLatentProjection S) (H : HiddenDAGModelFamily S P) where
  joint_identifiable_iff : forall query,
    H.JointIdentifiable query <->
      Identifiable P.observedGraph query
  conditional_identifiable_iff : forall query,
    H.ConditionalIdentifiable query <->
      ConditionalIdentifiable P.observedGraph query

theorem hiddenDAG_joint_transport
    {S : ObservedSignature} {P : FiniteLatentProjection S}
    {H : HiddenDAGModelFamily S P}
    (published : PublishedLatentProjection P H)
    (query : JointKernelQuery S) :
    H.JointIdentifiable query <->
      TypeTheoreticIdentifiable P.observedGraph query := by
  exact published.joint_identifiable_iff query

theorem hiddenDAG_conditional_transport
    {S : ObservedSignature} {P : FiniteLatentProjection S}
    {H : HiddenDAGModelFamily S P}
    (published : PublishedLatentProjection P H)
    (query : ConditionalKernelQuery S) :
    H.ConditionalIdentifiable query <->
      TypeTheoreticConditionalIdentifiable P.observedGraph query := by
  exact published.conditional_identifiable_iff query

end Causality
end Thesis
