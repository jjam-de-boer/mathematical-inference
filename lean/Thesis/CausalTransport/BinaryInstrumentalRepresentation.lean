import Thesis.Causality.BinaryInstrumentalModel
import Thesis.CausalTransport.HiddenDAGProbability

namespace Thesis
namespace Causality
namespace BinaryInstrumental

open Probability

/-!
# Exact binary-IV response representation on the original hidden DAG

The projection is the actual three-node IV graph: `Z -> X -> Y` with only
`X <-> Y`.  Forward representation applies to *every* finite native SCM on
that original hidden DAG, with arbitrary finite hidden and private-noise
alphabets and with zeros permitted.  The intervention-preserving collapse
is used only through its already proved literal probability preservation and
projected-graph theorem.  No individual-model canonical assumption is added.

Conversely, every independent instrument/profile record pair is realized by
an actual SCM on this same original hidden DAG.  Its root placement, relay
mechanisms and product law are constructed internally by the native
realization theorem.  These two directions justify optimizing over the
finite response representation without enlarging or selecting the causal
model class.  They do not yet implement a linear optimizer or assert that
an arbitrary observed law is compatible with the IV graph.

The instrument factor is separately proved observable.  Consequently later
linear constraints can fix its coefficient from the supplied observed law,
including its null instrument cells, while leaving only profile weights
unknown.  No division by those cells or monotonicity assumption is needed.
-/

variable {P : FiniteLatentProjection signature}

/-- This specifies the original DAG's actual projected graph, not an
external theorem asserting semantic equivalence of selected model families. -/
def HasIVProjection (projection : FiniteLatentProjection signature) : Prop :=
  forall first second, projection.observedGraph.bidirected first second = graph.bidirected first second

private theorem collapsed_hasProjectedGraph (native : FiniteHiddenDAGSCM signature P)
    (graphMatch : HasIVProjection P) : HasProjectedGraph native.toLatentRootSCM graph :=
  fun first second => (native.toLatentRootSCM_projectedGraph first second).trans (graphMatch first second)

/-- Data and preservation proofs for a native model's entire representation.
Both treatment interventions share the same response record as observation. -/
structure ResponseRepresentation (native : FiniteHiddenDAGSCM signature P) where
  instrument : FiniteProbRecord Bool
  responses : FiniteProbRecord Profile
  observational : forall event, QProb.Equiv (native.observationalValue event)
    ((observedRecord instrument responses).probVal event)
  interventional : forall action, QProb.Equiv
    (native.interventionalValue (intervention action) (fun sample => sample y))
    ((effectRecord responses action).probVal id)
  instrument_observable : forall event, QProb.Equiv (instrument.probVal event)
    (native.observationalValue (fun sample => event (sample z)))

/-- Extract a representation from every original finite hidden-DAG SCM.
The records are actual pushforwards of its retained original noise prior;
neither is selected from an existential equivalence assertion. -/
def responseRepresentation (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P) :
    ResponseRepresentation native where
  instrument := instrumentRecord native.toLatentRootSCM
  responses := responseRecord native.toLatentRootSCM
  observational := by
    intro event
    rw [← native.toLatentRootSCM_observationalValue]
    exact observationalValue_response native.toLatentRootSCM
      (noInstrumentConfounding_of_projectedGraph native.toLatentRootSCM (collapsed_hasProjectedGraph native graphMatch)) event
  interventional := by
    intro action
    rw [← native.toLatentRootSCM_interventionalValue]
    exact interventionalValue_response native.toLatentRootSCM action
  instrument_observable := by
    intro event
    rw [← native.toLatentRootSCM_observationalValue]
    exact instrumentRecord_observable native.toLatentRootSCM event

private theorem profileModel_compatible_projection (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (instrument : FiniteProbRecord Bool)
    (responses : FiniteProbRecord Profile) :
    Compatible (profileModel instrument responses) projection.observedGraph :=
  ⟨profileModel_isCanonical instrument responses, fun first second =>
    (profileModel_hasProjectedGraph instrument responses first second).trans (graphMatch first second).symm⟩

/-- Realize every proposed finite independent profile record pair on the
original graph.  Feasibility relative to an observed law must still be proved
against `observedRecord`; it is not supplied as a fictitious model field. -/
def nativeProfileModel (projection : FiniteLatentProjection signature) (graphMatch : HasIVProjection projection)
    (instrument : FiniteProbRecord Bool) (responses : FiniteProbRecord Profile) :
    FiniteHiddenDAGSCM signature projection :=
  (profileModel instrument responses).toHiddenDAGSCM
    (profileModel_compatible_projection projection graphMatch instrument responses)

/-- Reverse whole-law preservation, also at zero-containing distributions. -/
theorem nativeProfileModel_observationalValue (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (instrument : FiniteProbRecord Bool)
    (responses : FiniteProbRecord Profile) (event : Event signature.Assignment) :
    QProb.Equiv ((nativeProfileModel projection graphMatch instrument responses).observationalValue event)
      ((observedRecord instrument responses).probVal event) :=
  QProb.equiv_trans
    ((profileModel instrument responses).toHiddenDAGSCM_observationalValue
      (profileModel_compatible_projection projection graphMatch instrument responses) event)
    (profileModel_observationalValue instrument responses event)

/-- Reverse treatment-effect preservation.  Thus feasible profile witnesses
give actual native causal values, not only optimistic numerical bounds. -/
theorem nativeProfileModel_interventionalValue (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (instrument : FiniteProbRecord Bool)
    (responses : FiniteProbRecord Profile) (action : Bool) :
    QProb.Equiv ((nativeProfileModel projection graphMatch instrument responses).interventionalValue
      (intervention action) (fun sample => sample y))
      ((effectRecord responses action).probVal id) :=
  QProb.equiv_trans
    ((profileModel instrument responses).toHiddenDAGSCM_interventionalValue
      (profileModel_compatible_projection projection graphMatch instrument responses) (intervention action) _)
    (profileModel_interventionalValue instrument responses action)

end BinaryInstrumental
end Causality
end Thesis
