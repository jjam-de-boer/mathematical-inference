import Thesis.CausalTransport.HiddenDAGCountermodelLift
import Thesis.CausalTransport.HedgeChannelCompleteness

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-!
# Published completeness for every finite original hidden DAG

The reverse realization embeds every compatible canonical model into an
actual finite SCM on the supplied original DAG, preserving all observed and
hard-interventional probabilities.  Consequently, identifiability throughout
the full positive original-DAG class entails identifiability throughout the
positive canonical projected class.  This implication uses the constructed
models, not an assumed equivalence of arbitrary selected model families.

The existing constructive projected completeness theorem then returns the
original query's inspectable published certificate.  Its class annotation
records the compiler's positive projected-graph regularity; the certificate
is also interpreted natively by `HiddenDAGPositiveCertificates`.  The full
original-DAG countermodels below are actual records, not certificate class
annotations or an uninhabited latent-projection interface.

All hidden and private-noise alphabets may have arbitrary finite sizes.  The
observed signature is fixed and value-rich (at least two values per variable)
for the countermodel and completeness conclusions.  Strict observed
positivity is explicit.  Failure also refutes identification in the larger
zero-permitting class, because its exhibited countermodels are already
positive; success in that larger class still requires local-support work.

This is a one-way certificate assembly boundary, like
`HedgeChannelCompleteness`.  The realization, probability-preservation and
countermodel-lifting cores do not import soundness or use it to establish
positivity.  No case split on semantic identifiability, choice of a model or
choice of a derivation is introduced here.
-/

namespace HiddenDAGModelClass

/-- Native positive-class joint identification pulls back along the actual
reverse realization.  Every projected pair is realized separately; the whole
observed-law equality and unchanged query values are transported explicitly. -/
theorem positive_identifiable_projected (query : JointKernelQuery S)
    (identified : (positive P).identifiable query) :
    (GraphModelClass.positive P.observedGraph).identifiable query := by
  intro left right leftMem rightMem observational assignment
  have nativeObservational :
      (left.toHiddenDAGSCM leftMem.1).ObservationalAgreement
        (right.toHiddenDAGSCM rightMem.1) := by
    intro event
    exact QProb.equiv_trans (left.toHiddenDAGSCM_observationalValue leftMem.1 event)
      (QProb.equiv_trans (observational event)
        (QProb.equiv_symm (right.toHiddenDAGSCM_observationalValue rightMem.1 event)))
  have nativeAgreement := identified
    (left.toHiddenDAGSCM leftMem.1) (right.toHiddenDAGSCM rightMem.1)
    (left.toHiddenDAGSCM_observational_num_pos leftMem.1 leftMem.2)
    (right.toHiddenDAGSCM_observational_num_pos rightMem.1 rightMem.2)
    nativeObservational
  rcases nativeAgreement assignment with ⟨nativeEquivalent⟩
  exact ⟨ProbabilityResult.trans
    (ProbabilityResult.symm (left.toHiddenDAGSCM_kernelDenote leftMem.1
      query.operationKernel assignment))
    (ProbabilityResult.trans nativeEquivalent
      (right.toHiddenDAGSCM_kernelDenote rightMem.1 query.operationKernel assignment))⟩

/-- The conditional pullback retains the two supplied common-support
witnesses.  They are transported into the realized models before native
agreement is applied, so a support-domain discrepancy cannot stand in for
the required equality of genuinely defined conditional values. -/
theorem positive_conditionalIdentifiable_projected (query : ConditionalKernelQuery S)
    (identified : (positive P).conditionalIdentifiable query) :
    (GraphModelClass.positive P.observedGraph).conditionalIdentifiable query := by
  intro left right leftMem rightMem observational assignment leftSupport rightSupport
  have nativeObservational :
      (left.toHiddenDAGSCM leftMem.1).ObservationalAgreement
        (right.toHiddenDAGSCM rightMem.1) := by
    intro event
    exact QProb.equiv_trans (left.toHiddenDAGSCM_observationalValue leftMem.1 event)
      (QProb.equiv_trans (observational event)
        (QProb.equiv_symm (right.toHiddenDAGSCM_observationalValue rightMem.1 event)))
  have nativeAgreement := identified
    (left.toHiddenDAGSCM leftMem.1) (right.toHiddenDAGSCM rightMem.1)
    (left.toHiddenDAGSCM_observational_num_pos leftMem.1 leftMem.2)
    (right.toHiddenDAGSCM_observational_num_pos rightMem.1 rightMem.2)
    nativeObservational
  have leftPreserved := left.toHiddenDAGSCM_kernelDenote leftMem.1
    query.operationKernel assignment
  have rightPreserved := right.toHiddenDAGSCM_kernelDenote rightMem.1
    query.operationKernel assignment
  have nativeLeftSupport := ProbabilityResult.Supported.transport
    (ProbabilityResult.symm leftPreserved) leftSupport
  have nativeRightSupport := ProbabilityResult.Supported.transport
    (ProbabilityResult.symm rightPreserved) rightSupport
  rcases nativeAgreement assignment nativeLeftSupport nativeRightSupport with ⟨nativeEquivalent⟩
  exact ⟨ProbabilityResult.trans (ProbabilityResult.symm leftPreserved)
    (ProbabilityResult.trans nativeEquivalent rightPreserved)⟩

end HiddenDAGModelClass

/-! ## Actual original-DAG countermodels for hedges and failed invocations -/

/-- Every original-query projected hedge has an actual positive pair on the
original hidden DAG.  The arbitrary finite relay alphabets and mechanisms
are constructed internally; no readiness predicate is supplied by a caller. -/
noncomputable def hedge_hiddenDAG_counterexample (rich : ObservedSignature.ValueRich S)
    {query : JointKernelQuery S} (witness : HedgeWitness P.observedGraph query) :
    HiddenDAGCounterexampleIn (HiddenDAGModelClass.positive P) query :=
  (HedgeChannelInstallation.counterexample witness rich).toHiddenDAG

/-- Failed joint ID produces a native pair for its unchanged original query,
at any recursive depth.  The structural failure extractor first restores the
original-query hedge; its semantic realization then yields the two records. -/
noncomputable def identifyJointKernel_hiddenDAG_failed_counterexample
    (rich : ObservedSignature.ValueRich S) (query : JointKernelQuery S)
    {fail : IdentificationFail S}
    (result : identifyJointKernel P.observedGraph query = .failed fail) :
    HiddenDAGCounterexampleIn (HiddenDAGModelClass.positive P) query :=
  hedge_hiddenDAG_counterexample rich (identifyJointKernelFailedHedge query result).witness

/-- Failed recursive IDC likewise separates the original conditional query
on common support, not just a terminal numerator or an auxiliary event. -/
noncomputable def identifyConditionalKernel_hiddenDAG_failed_counterexample
    (rich : ObservedSignature.ValueRich S) (query : ConditionalKernelQuery S)
    {fail : IdentificationFail S}
    (result : identifyConditionalKernel P.observedGraph query = .failed fail) :
    HiddenDAGConditionalCounterexampleIn (HiddenDAGModelClass.positive P) query :=
  (P.observedGraph.identifyConditionalKernel_failed_counterexample rich query result).toHiddenDAG

/-- A failed joint invocation refutes full positive original-DAG
identifiability by its exhibited native countermodel pair. -/
theorem identifyJointKernel_hiddenDAG_failed_not_identifiable
    (rich : ObservedSignature.ValueRich S) (query : JointKernelQuery S)
    {fail : IdentificationFail S}
    (result : identifyJointKernel P.observedGraph query = .failed fail) :
    Not ((HiddenDAGModelClass.positive P).identifiable query) :=
  (identifyJointKernel_hiddenDAG_failed_counterexample rich query result).not_identifiable

/-- A failed conditional invocation refutes full positive original-DAG
conditional identifiability through genuine common-support disagreement. -/
theorem identifyConditionalKernel_hiddenDAG_failed_not_identifiable
    (rich : ObservedSignature.ValueRich S) (query : ConditionalKernelQuery S)
    {fail : IdentificationFail S}
    (result : identifyConditionalKernel P.observedGraph query = .failed fail) :
    Not ((HiddenDAGModelClass.positive P).conditionalIdentifiable query) :=
  (identifyConditionalKernel_hiddenDAG_failed_counterexample rich query result).not_identifiable

/-- The same joint failure also refutes the larger class allowing zeros.
This negative result does not claim zero-unrestricted success correctness. -/
theorem identifyJointKernel_hiddenDAG_failed_not_identifiable_all
    (rich : ObservedSignature.ValueRich S) (query : JointKernelQuery S)
    {fail : IdentificationFail S}
    (result : identifyJointKernel P.observedGraph query = .failed fail) :
    Not ((HiddenDAGModelClass.all P).identifiable query) := by
  intro identified
  exact identifyJointKernel_hiddenDAG_failed_not_identifiable rich query result
    (HiddenDAGModelClass.identifiable_of_subset
      HiddenDAGModelClass.positive_subset_all query identified)

/-- Common-support conditional failure likewise refutes the zero-permitting
class, because both constructed positive models already belong to it. -/
theorem identifyConditionalKernel_hiddenDAG_failed_not_identifiable_all
    (rich : ObservedSignature.ValueRich S) (query : ConditionalKernelQuery S)
    {fail : IdentificationFail S}
    (result : identifyConditionalKernel P.observedGraph query = .failed fail) :
    Not ((HiddenDAGModelClass.all P).conditionalIdentifiable query) := by
  intro identified
  exact identifyConditionalKernel_hiddenDAG_failed_not_identifiable rich query result
    (HiddenDAGModelClass.conditionalIdentifiable_of_subset
      HiddenDAGModelClass.positive_subset_all query identified)

/-! ## Inspectable published certificates and the inhabited completeness package -/

/-- Native full-class joint identifiability yields the engine's inspectable
published certificate for the original query.  The fixed observed alphabets
are unchanged, while hidden and noise alphabets remain unrestricted finite
presentations of the original-DAG models. -/
noncomputable def FiniteLatentProjection.publishedHiddenDAGJointCompleteness
    (projection : FiniteLatentProjection S) (rich : ObservedSignature.ValueRich S)
    (query : JointKernelQuery S)
    (identified : (HiddenDAGModelClass.positive projection).identifiable query) :
    PublishedJointCertificate (GraphModelClass.positive projection.observedGraph)
      projection.observedGraph.dSeparationCorrectness query :=
  projection.observedGraph.publishedJointCompleteness rich query
    (HiddenDAGModelClass.positive_identifiable_projected query identified)

/-- Native conditional identifiability yields the corresponding original-
query certificate, including all recursive IDC exchange steps. -/
noncomputable def FiniteLatentProjection.publishedHiddenDAGConditionalCompleteness
    (projection : FiniteLatentProjection S) (rich : ObservedSignature.ValueRich S)
    (query : ConditionalKernelQuery S)
    (identified : (HiddenDAGModelClass.positive projection).conditionalIdentifiable query) :
    PublishedConditionalCertificate (GraphModelClass.positive projection.observedGraph)
      projection.observedGraph.dSeparationCorrectness query :=
  projection.observedGraph.publishedConditionalCompleteness rich query
    (HiddenDAGModelClass.positive_conditionalIdentifiable_projected query identified)

/-- Published completeness quantified over every positive finite SCM on one
original hidden DAG.  Its certificates retain the established compiler type;
its countermodel field contains actual original-DAG records.  The constructor
below inhabits all fields, rather than leaving another external interface. -/
structure PublishedHiddenDAGCompleteness (projection : FiniteLatentProjection S) where
  dseparation : DSeparationCorrectness projection.observedGraph
  joint_complete : forall query,
    (HiddenDAGModelClass.positive projection).identifiable query →
      PublishedJointCertificate (GraphModelClass.positive projection.observedGraph)
        dseparation query
  conditional_complete : forall query,
    (HiddenDAGModelClass.positive projection).conditionalIdentifiable query →
      PublishedConditionalCertificate (GraphModelClass.positive projection.observedGraph)
        dseparation query
  hedge_counterexample : forall query,
    HedgeWitness projection.observedGraph query →
      HiddenDAGCounterexampleIn (HiddenDAGModelClass.positive projection) query

/-- The inhabited full hidden-DAG completeness package.  The only extra
alphabet hypothesis is observed value-richness; positivity is membership in
the quantified class, not an assumed hidden-DAG transfer theorem. -/
noncomputable def FiniteLatentProjection.publishedHiddenDAGCompleteness
    (projection : FiniteLatentProjection S) (rich : ObservedSignature.ValueRich S) :
    PublishedHiddenDAGCompleteness projection where
  dseparation := projection.observedGraph.dSeparationCorrectness
  joint_complete := projection.publishedHiddenDAGJointCompleteness rich
  conditional_complete := projection.publishedHiddenDAGConditionalCompleteness rich
  hedge_counterexample := fun _ witness => hedge_hiddenDAG_counterexample rich witness

end Causality
end Thesis
