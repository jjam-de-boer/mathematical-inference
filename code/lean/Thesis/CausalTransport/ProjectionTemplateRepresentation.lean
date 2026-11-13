import Thesis.CausalTransport.ProjectedHiddenDAGModels
import Thesis.CausalTransport.HiddenDAGNativeTemplateRepresentation

namespace Thesis.Causality

open Probability

/-!
# Finite structural-template coverage at a fixed observed projection

The original domain explicitly ranges over all finite full hidden DAGs with
this observed projection. Reduce an actual member to the fixed clique-root
graph with all interventions preserved, then use the existing constructive
fixed-DAG compression and native-template theorem. The resulting finite list
depends only on the observed graph, public signature and target-list length,
not the old hidden-node count, alphabets, mechanisms or rational denominators.

Every output is an actual listed standalone template with actual independent
rational factor records. It preserves the entire observational law and all
requested target probabilities of the unchanged original model. Conversely,
the instantiated model is itself a member of the full projected model domain.
No caller-supplied preservation or exhaustive-family interface is used.

Only the structural family is finite. Its rational source weights remain
unbounded parameters. Compression need not preserve unrequested causal
targets, decide exact compatibility, establish sharp bounds, or supply a
complete optimizer. Conditional targets retain joint/evidence queries and
the original positive causal conditioner rather than completing null values.
-/

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S}

structure ProjectionTemplateRepresentation (original : ProjectedHiddenDAGModel graph) (targets : List (NativeProbabilityQuery S)) where
  template : graph.cliqueRootProjection.hiddenDAG.CodeNativeTemplate
  listed : template ∈ graph.cliqueRootProjection.hiddenDAG.nativeTemplateCatalogue
    (FiniteHiddenDAGSCM.representationNodeBound graph.cliqueRootProjection targets.length)
    (FiniteHiddenDAGSCM.representationSourceBound S targets.length)
  factors : (node : Fin graph.cliqueRootProjection.hiddenDAG.count) → FiniteProbRecord (Fin (template.entry.shape.sourceCard node))
  observational : ∀ event, QProb.Equiv ((template.model (P := graph.cliqueRootProjection) factors).observationalValue event)
    (original.model.observationalValue event)
  preserved : ∀ query, query ∈ targets →
    QProb.Equiv ((template.model (P := graph.cliqueRootProjection) factors).interventionalValue query.intervention query.event)
      (original.model.interventionalValue query.intervention query.event)

/-- Construct the listed entry, factors and law comparisons for every full
original graph in the stated projection class. All fields above are inhabited. -/
def ProjectedHiddenDAGModel.projectionTemplateRepresentation (original : ProjectedHiddenDAGModel graph)
    (targets : List (NativeProbabilityQuery S)) : ProjectionTemplateRepresentation original targets :=
  let fixed := original.cliqueRepresentative.nativeTemplateRepresentation targets
  { template := fixed.template
    listed := fixed.listed
    factors := fixed.factors
    observational := fun event => QProb.equiv_trans (fixed.observational event) (original.cliqueRepresentative_observationalValue event)
    preserved := fun query member => QProb.equiv_trans (fixed.preserved query member)
      (original.cliqueRepresentative_interventionalValue query.intervention query.event) }

namespace ProjectionTemplateRepresentation

variable {original : ProjectedHiddenDAGModel graph} {targets : List (NativeProbabilityQuery S)}

def model (represented : ProjectionTemplateRepresentation original targets) : FiniteHiddenDAGSCM S graph.cliqueRootProjection :=
  represented.template.model (P := graph.cliqueRootProjection) represented.factors

/-- The representative is an actual member of the original quantified
projection class, not only a model in some possibly larger surrogate class. -/
def asProjectedModel (represented : ProjectionTemplateRepresentation original targets) : ProjectedHiddenDAGModel graph :=
  ProjectedHiddenDAGModel.onCliqueGraph represented.model

theorem query_eventPositive_iff (represented : ProjectionTemplateRepresentation original targets)
    (query : NativeProbabilityQuery S) (listed : query ∈ targets) :
    (represented.model.interventionalDist query.intervention).EventPositive query.event ↔
      (original.model.interventionalDist query.intervention).EventPositive query.event :=
  QProb.equiv_num_pos_iff (represented.preserved query listed)

/-- Retaining the actual causal evidence and joint event is sufficient for
conditioned-record preservation, provided the original evidence is supported. -/
theorem conditionOn_probVal (represented : ProjectionTemplateRepresentation original targets)
    (intervention : HardIntervention S) (evidence event : Event S.Assignment)
    (jointListed : (⟨intervention, fun value => evidence value && event value⟩ : NativeProbabilityQuery S) ∈ targets)
    (evidenceListed : (⟨intervention, evidence⟩ : NativeProbabilityQuery S) ∈ targets)
    (supported : (original.model.interventionalDist intervention).EventPositive evidence) :
    QProb.Equiv
      (((represented.model.interventionalDist intervention).conditionOn evidence
        ((represented.query_eventPositive_iff ⟨intervention, evidence⟩ evidenceListed).mpr supported)).probVal event)
      (((original.model.interventionalDist intervention).conditionOn evidence supported).probVal event) := by
  let supportedNew := (represented.query_eventPositive_iff ⟨intervention, evidence⟩ evidenceListed).mpr supported
  exact QProb.equiv_trans ((represented.model.interventionalDist intervention).conditionOn_probVal evidence event supportedNew)
    (QProb.equiv_trans (QProb.div_congr (represented.preserved _ jointListed) (represented.preserved _ evidenceListed) supportedNew supported)
      (QProb.equiv_symm ((original.model.interventionalDist intervention).conditionOn_probVal evidence event supported)))

end ProjectionTemplateRepresentation
end Thesis.Causality
