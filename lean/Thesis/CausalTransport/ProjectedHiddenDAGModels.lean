import Thesis.CausalTransport.CliqueRootNative

namespace Thesis.Causality

open Probability

/-!
# The full finite model domain at a fixed observed projection

Unlike a family indexed by one full hidden DAG, this record ranges over all
full finite hidden DAGs whose observed projection is the stated graph. The
actual original native model is part of the record. Its hidden topology,
hidden value alphabets and private-noise alphabets may vary without a common
bound; the public observed signature stays fixed. No selected subfamily,
positivity, canonical-root restriction or external semantic coverage theorem
is built into membership.

The constructed clique representative preserves every observed event under
every hard intervention. Conversely any native model on the fixed clique
graph is itself one member of this full original-graph domain. These two facts
supply the model-domain boundary for projection-wide finite template coverage;
they do not claim the domain or its rational source parameters are finite.
-/

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S}

structure ProjectedHiddenDAGModel (graph : ObservedGraph S) where
  projection : FiniteLatentProjection S
  projected : ∀ left right, projection.observedGraph.bidirected left right = graph.bidirected left right
  model : FiniteHiddenDAGSCM S projection

namespace ProjectedHiddenDAGModel

/-- Every original native model with the required graph agreement is in
the domain, with its unchanged full DAG and all its actual probability data. -/
def ofModel {projection : FiniteLatentProjection S} (model : FiniteHiddenDAGSCM S projection)
    (projected : ∀ left right, projection.observedGraph.bidirected left right = graph.bidirected left right) :
    ProjectedHiddenDAGModel graph := ⟨projection, projected, model⟩

/-- The fixed clique graph is a legitimate original full graph in the same
class. A template instance on it is not a model outside the quantified class. -/
def onCliqueGraph (model : FiniteHiddenDAGSCM S graph.cliqueRootProjection) : ProjectedHiddenDAGModel graph :=
  ⟨graph.cliqueRootProjection, fun _ _ => rfl, model⟩

def cliqueRepresentative (original : ProjectedHiddenDAGModel graph) : FiniteHiddenDAGSCM S graph.cliqueRootProjection :=
  original.model.toCliqueRootSCM graph original.projected

theorem cliqueRepresentative_interventionalValue (original : ProjectedHiddenDAGModel graph)
    (intervention : HardIntervention S) (event : Event S.Assignment) :
    QProb.Equiv (original.cliqueRepresentative.interventionalValue intervention event)
      (original.model.interventionalValue intervention event) :=
  original.model.toCliqueRootSCM_interventionalValue graph original.projected intervention event

theorem cliqueRepresentative_observationalValue (original : ProjectedHiddenDAGModel graph) (event : Event S.Assignment) :
    QProb.Equiv (original.cliqueRepresentative.observationalValue event) (original.model.observationalValue event) :=
  original.model.toCliqueRootSCM_observationalValue graph original.projected event

end ProjectedHiddenDAGModel
end Thesis.Causality
